######################################################################
### SIMULATION STUDY 4 VERSION 3.0.0 		   				       ###
### - Study 4: Robustness analysis for the joint tests             ###
######################################################################

############################
### Loading the packages ###
############################

REQUIRED_PACKAGES <- c(
	"mvtnorm",		
	### mvtnorm::dmvnorm() and mvtnorm::rmvnorm(), compute the density and generate random vector of multivariate normal distribution
	"Matrix", 
	### Matrix::bdiag(), builds a block diagonal matrix given several building block matrices
	"Compositional",
	### Compositional::helm(), creates the Helmert sub-matrix
	"MCMCpack",
	### MCMCpack::rdirichlet(), generates random deviates from the Dirichlet distribution
	"pbapply",
	### pbapply::pbreplicate(), adds progress bar to replicate functions
	"matrixsampling"
	### matrixsampling::rwishart(), samples a Wishart distribution
	### "mice"
	### mice::ampute(), generates multivariate missing data under a MCAR, MAR or MNAR missing data mechanism
	)

CHECK_PACKAGES <- lapply(X = REQUIRED_PACKAGES,
					   FUN = function(x) {
    if (!require(x, character.only = TRUE)) {
      install.packages(x, dependencies = TRUE)
    }
    require(x, character.only = TRUE)
  }
)

#############################
### Loading the functions ###
#############################

BLOCK_HADAMARD_PRODUCT <- function(A_mat, B_mat, p_vec){
	
	### INPUT
	### A_mat: K by K 
	### B_mat: K by K
	### p_vec: K by 1, p = sum(p_vec)
	### OUTPUT
	### N: p by p
	
	K <- length(p_vec)
	COL_mat_temp <- c()
	for(k in 1 : K){
		ROW_mat_temp <- c()
		for(kp in 1 : K){
			if(k == kp){
				ROW_mat_temp <- cbind(ROW_mat_temp, A_mat[k, k] * diag(p_vec[k]) + B_mat[k, k] * matrix(1, p_vec[k], p_vec[k]))
			} else{
				ROW_mat_temp <- cbind(ROW_mat_temp, B_mat[k, kp] * matrix(1, p_vec[k], p_vec[kp]))
			}
		}
		COL_mat_temp <- rbind(COL_mat_temp, ROW_mat_temp)
	}
	N <- COL_mat_temp
	### p by p
	return(N)
}

BEST_UNBIASED_ESTIMATOR <- function(S_mat, p_vec){
	
	### NOTE: this version can deal with NA values
	### INPUT
	### S_mat: p by p, unbiased estimator of the covariance matrix 
	### p_vec: K by 1, p = sum(p_vec)
	### OUTPUT
	### A_mat: K by K
	### B_mat: K by K
	
	K <- length(p_vec)
	A_mat_temp <- matrix(0, K, K)
	B_mat_temp <- matrix(0, K, K)
	for(k in 1 : K){
		for(kp in 1 : K){
			SUB_mat <- S_mat[(sum(p_vec[0 : (k - 1)]) + 1) : sum(p_vec[0 : k]), (sum(p_vec[0 : (kp - 1)]) + 1) : sum(p_vec[0 : kp])]
			if(kp == k){
				SUB_ON_mat <- mean(diag(SUB_mat), na.rm = TRUE)
				SUB_OF_mat <- (sum(SUB_mat[upper.tri(SUB_mat)], na.rm = TRUE) + sum(SUB_mat[lower.tri(SUB_mat)], na.rm = TRUE)) / (p_vec[k] ^ 2 - p_vec[k] - sum(is.na(SUB_mat[upper.tri(SUB_mat)])) - sum(is.na(SUB_mat[lower.tri(SUB_mat)])))
				A_mat_temp[k, kp] <- SUB_ON_mat - SUB_OF_mat
				B_mat_temp[k, kp] <- SUB_OF_mat
			} else{
				B_mat_temp[k, kp] <- mean(as.vector(SUB_mat), na.rm = TRUE)
			}	
		}
	}
	A_mat <- A_mat_temp
	B_mat <- (B_mat_temp + t(B_mat_temp)) / 2
	return(list(A_mat = A_mat, B_mat = B_mat))
}

COMPUTE_GAMMA_MATRIX <- function(p_vec){
	
	### INPUT
	### p_vec: K by 1, p = sum(p_vec)
	### OUTPUT
	### Gamma_mat: p by p
	
	K <- length(p_vec)
	### 1 by 1
	Gamma_mat_temp_1 <- matrix(0, 1, 1)
	Gamma_mat_temp_2 <- matrix(0, 1, 1)
	for(k in 1 : K){
		Gamma_mat_temp_1 <- Matrix::bdiag(Gamma_mat_temp_1, matrix(rep(1 / sqrt(p_vec[k]), p_vec[k]), nrow = 1, ncol = p_vec[k]))
		Gamma_mat_temp_2 <- Matrix::bdiag(Gamma_mat_temp_2, Compositional::helm(p_vec[k]))
	}
	Gamma_mat_temp_1 <- as.matrix(Gamma_mat_temp_1[- 1, - 1])
	### K by p
	Gamma_mat_temp_2 <- as.matrix(Gamma_mat_temp_2[- 1, - 1])	
	### (p - K) by p
	### deleting the first one
	Gamma_mat <- rbind(Gamma_mat_temp_1, Gamma_mat_temp_2)
	return(Gamma_mat)
}

COMPUTE_EMPIRICAL_LOG_LAMBDA_1 <- function(n, p_vec, V_mat){
	
	### INPUT
	### n: 1 by 1, the grand sample size 
	### p_vec: K by 1
	### V_mat: p by p
	### OUTPUT
	### logLambda1: 1 by 1
	
	COMPUTE_DIAGONAL_BLOCKS <- function(M_mat, p_vec) {
		  if (nrow(M_mat) != ncol(M_mat)) {
			stop("M must be a square matrix.")
		  }
		  if (sum(p_vec) != nrow(M_mat)) {
			stop("Sum of sizes must equal the matrix dimension.")
		  }
		  
		  idx <- cumsum(c(0, p_vec))
		  block_list <- vector("list", length(p_vec))
		  
		  for (i in seq_along(p_vec)) {
			row_idx <- (idx[i] + 1):idx[i + 1]
			col_idx <- (idx[i] + 1):idx[i + 1]
			block_list[[i]] <- M_mat[row_idx, col_idx, drop = FALSE]
		  }
		  
		  return(block_list)
	}
	
	K <- length(p_vec)
	V_diag_list <- COMPUTE_DIAGONAL_BLOCKS(M_mat = V_mat, p_vec = c(K, p_vec - 1))
	### (K + 1) by from K to pk - 1
	
	Item_1 <- sum((p_vec - 1) * log(p_vec - 1))
	Item_2 <- log(det(V_mat))
	Item_3 <- - log(det(V_diag_list[[1]]))
	Item_4 <- 0
	
	for(k in 1 : K){
		Item_4 <- Item_4 - (p_vec[k] - 1) * log(sum(diag(V_diag_list[[k + 1]])))
	}
	TwoNlogLambda1 <- Item_1 + Item_2 + Item_3 + Item_4
	logLambda1 <- (n / 2) * TwoNlogLambda1
	return(logLambda1)
}

COMPUTE_EMPIRICAL_LOG_LAMBDA_3 <- function(n_vec, p_vec, V_list){
	
	### INPUT
	### n_vec: M by 1 
	### p_vec: K by 1
	### V_list: M by p by p
	### OUTPUT
	### logLambda3: 1 by 1
	
	COMPUTE_DIAGONAL_BLOCKS <- function(M_mat, p_vec) {
		  if (nrow(M_mat) != ncol(M_mat)) {
			stop("M must be a square matrix.")
		  }
		  if (sum(p_vec) != nrow(M_mat)) {
			stop("Sum of sizes must equal the matrix dimension.")
		  }
		  
		  idx <- cumsum(c(0, p_vec))
		  block_list <- vector("list", length(p_vec))
		  
		  for (i in seq_along(p_vec)) {
			row_idx <- (idx[i] + 1):idx[i + 1]
			col_idx <- (idx[i] + 1):idx[i + 1]
			block_list[[i]] <- M_mat[row_idx, col_idx, drop = FALSE]
		  }
		  
		  return(block_list)
	}
	
	K <- length(p_vec)
	n <- sum(n_vec)
	M <- length(n_vec)
	f_vec <- n_vec / n
	V_sum_mat <- Reduce("+", V_list)
	### p by p
	
	V_sum_diag_list <- COMPUTE_DIAGONAL_BLOCKS(M_mat = V_sum_mat, p_vec = c(K, p_vec - 1))
	### (K + 1) by from K to pk - 1
	
	Item_0 <- - p * sum(f_vec * log(f_vec))
	Item_1 <- 0
	Item_2 <- 0
	Item_3 <- 0
	Item_4 <- 0
	
	for(m in 1 : M){
		Vm_diag_list <- COMPUTE_DIAGONAL_BLOCKS(M_mat = V_list[[m]], p_vec = c(K, p_vec - 1))
		### (K + 1) by from K to pk - 1
		
		Item_1 <- Item_1 + f_vec[m] * log(det(Vm_diag_list[[1]]))
		
		Item_2 <- Item_2 - f_vec[m] * log(det(V_sum_diag_list[[1]]))
		
		for(k in 1 : K){
			
			Item_3 <- Item_3 + f_vec[m] * (p_vec[k] - 1) * log(sum(diag(Vm_diag_list[[k + 1]])))
			Item_4 <- Item_4 - f_vec[m] * (p_vec[k] - 1) * log(sum(diag(V_sum_diag_list[[k + 1]])))
		}
	}
	
	TwoNlogLambda3 <- Item_0 + Item_1 + Item_2 + Item_3 + Item_4
	logLambda3 <- (n / 2) * TwoNlogLambda3
	return(logLambda3)
}

COMPUTE_EMPIRICAL_LOG_LAMBDA_2 <- function(n, p_vec, V_mat, H_mat){
	
	### INPUT
	### n: 1 by 1, the grand sample size 
	### p_vec: K by 1
	### V_mat: p by p
	### H_mat: p by p
	### OUTPUT
	### logLambda2: 1 by 1
	
	COMPUTE_DIAGONAL_BLOCKS <- function(M_mat, p_vec) {
		  if (nrow(M_mat) != ncol(M_mat)) {
			stop("M must be a square matrix.")
		  }
		  if (sum(p_vec) != nrow(M_mat)) {
			stop("Sum of sizes must equal the matrix dimension.")
		  }
		  
		  idx <- cumsum(c(0, p_vec))
		  block_list <- vector("list", length(p_vec))
		  
		  for (i in seq_along(p_vec)) {
			row_idx <- (idx[i] + 1):idx[i + 1]
			col_idx <- (idx[i] + 1):idx[i + 1]
			block_list[[i]] <- M_mat[row_idx, col_idx, drop = FALSE]
		  }
		  
		  return(block_list)
	}
	
	K <- length(p_vec)
	V_diag_list <- COMPUTE_DIAGONAL_BLOCKS(M_mat = V_mat, p_vec = c(K, p_vec - 1))
	### (K + 1) by from K to pk - 1
	H_diag_list <- COMPUTE_DIAGONAL_BLOCKS(M_mat = H_mat, p_vec = c(K, p_vec - 1))
	### (K + 1) by from K to pk - 1
	
	Item_1 <- log(det(V_diag_list[[1]]))
	Item_2 <- - log(det(V_diag_list[[1]] + H_diag_list[[1]]))
	Item_3 <- 0
	Item_4 <- 0
	
	for(k in 1 : K){
		Item_3 <- Item_3 + (p_vec[k] - 1) * log(sum(diag(V_diag_list[[k + 1]])))
		Item_4 <- Item_4 - (p_vec[k] - 1) * log(sum(diag(V_diag_list[[k + 1]] + H_diag_list[[k + 1]])))
	}
	TwoNlogLambda2 <- Item_1 + Item_2 + Item_3 + Item_4
	logLambda2 <- (n / 2) * TwoNlogLambda2
	return(logLambda2)
}

COMPUTE_EMPIRICAL_LOG_LAMBDA_4 <- function(n_vec, p_vec, V_list, H_mat){
	### INPUT
	### n_vec: M by 1 
	### p_vec: K by 1
	### V_list: M by p by p
	### H_mat: p by p
	### OUTPUT
	### logLambda4: 1 by 1
	
	COMPUTE_DIAGONAL_BLOCKS <- function(M_mat, p_vec) {
		  if (nrow(M_mat) != ncol(M_mat)) {
			stop("M must be a square matrix.")
		  }
		  if (sum(p_vec) != nrow(M_mat)) {
			stop("Sum of sizes must equal the matrix dimension.")
		  }
		  
		  idx <- cumsum(c(0, p_vec))
		  block_list <- vector("list", length(p_vec))
		  
		  for (i in seq_along(p_vec)) {
			row_idx <- (idx[i] + 1):idx[i + 1]
			col_idx <- (idx[i] + 1):idx[i + 1]
			block_list[[i]] <- M_mat[row_idx, col_idx, drop = FALSE]
		  }
		  
		  return(block_list)
	}
	
	K <- length(p_vec)
	n <- sum(n_vec)
	V_sum_mat <- Reduce("+", V_list)
	### p by p
	V_sum_diag_list <- COMPUTE_DIAGONAL_BLOCKS(M_mat = V_sum_mat, p_vec = c(K, p_vec - 1))
	### (K + 1) by from K to pk - 1
	H_diag_list <- COMPUTE_DIAGONAL_BLOCKS(M_mat = H_mat, p_vec = c(K, p_vec - 1))
	### (K + 1) by from K to pk - 1
	
	Item_1 <- log(det(V_sum_diag_list[[1]]))
	Item_2 <- - log(det(H_diag_list[[1]] + V_sum_diag_list[[1]]))
	Item_3 <- 0
	Item_4 <- 0
	
	for(k in seq(K)){
		Item_3 <- Item_3 + (p_vec[k] - 1) * log(sum(diag(V_sum_diag_list[[k + 1]])))
		Item_4 <- Item_4 - (p_vec[k] - 1) * log(sum(diag(H_diag_list[[k + 1]] + V_sum_diag_list[[k + 1]])))
	}
	TwoNlogLambda4 <- Item_1 + Item_2 + Item_3 + Item_4
	logLambda4 <- (n / 2) * TwoNlogLambda4
	return(logLambda4)
}

COMPUTE_EMPIRICAL_TEST_STATISTICS_SIMPLIFIED <- function(n_vec, p_vec, mu_mat_0, mu_vec_test, Sigma_mat_0, miss_prop_vec, t_df, COMPUTE_EMPIRICAL_LOG_LAMBDA_1, COMPUTE_EMPIRICAL_LOG_LAMBDA_2, COMPUTE_EMPIRICAL_LOG_LAMBDA_3, COMPUTE_EMPIRICAL_LOG_LAMBDA_4, BLOCK_HADAMARD_PRODUCT, BEST_UNBIASED_ESTIMATOR, COMPUTE_GAMMA_MATRIX){
	##### SIMPLIFIED VERSION does not include truth competitors
	####  only for joint mean tests
	### INPUT
	### n_vec: M by 1
	### p_vec: K by 1
	### mu_mat_0: M by p
	### mu_vec_test: p by 1
	### Sigma_mat_0: p by p
	### miss_prop_vec: dim by 1
	### t_df: 1 by 1
	### OUTPUT
	### log_Lambda_2_est_vec: dim(miss_prop_vec) + 1 by 1
	### log_Lambda_4_est_vec: dim(miss_prop_vec) + 1 by 1
	### G_2_est_vec: dim(miss_prop_vec) + 1 by 1
	### G_4_est_vec: dim(miss_prop_vec) + 1 by 1
	
	M <- length(n_vec)
	n <- sum(n_vec)
	p <- nrow(Sigma_mat_0)

	### create the random samples ###
	X_list <- W_list <- list()
	### M by n ^ (m) by p, M by p by p
	X_bar_mat <- matrix(0, nrow = M, ncol = p)
	### M by p
	X_bar_vec <- rep(0, p)
	### p by 1
	S_mat <- matrix(0, nrow = p, ncol = p)
	### p by p
	
	rep_error <- rep_error_max <- 1
	
	while(rep_error <= rep_error_max){
	### when miss_prop_vec is large or dimension p is too small, 
	### the estimate of Sig_A_mat may not be p.d. 
	### due to too many NAs on the diagonals
	
		tryCatch({
			for(m in 1 : M){
				if(t_df == Inf){
					X_list[[m]] <- mvtnorm::rmvnorm(n = n_vec[m], mean = mu_mat_0[m, ], sigma = Sigma_mat_0)
					### n ^ (m) by p
				} else {
					X_list[[m]] <- mvtnorm::rmvt(n = n_vec[m], df = t_df, delta = mu_mat_0[m, ], sigma = Sigma_mat_0)
					### n ^ (m) by p
				}
				
				X_bar_mat[m, ] <- apply(X_list[[m]], 2, mean)
				### p by 1
				X_bar_vec <- X_bar_vec + n_vec[m] * X_bar_mat[m, ]
				### p by 1
				W_list[[m]] <- cov(X_list[[m]]) * (n_vec[m] - 1)
				S_mat <- S_mat + W_list[[m]]
			}
	
			X_bar_vec <- X_bar_vec / n 
			### p by 1
			S_mat_pool <- S_mat / (n - M)
			### p by p
	
			S_mat_est_add_list <- list()
			S_mat_est_add_list[[1]] <- S_mat_pool
			
			if(!is.null(miss_prop_vec)){
				for(rep_miss in 1 : length(miss_prop_vec)){
					S_mat_est_add_temp <- S_mat_pool
					S_mat_est_add_temp[sample(1 : (nrow(S_mat_est_add_temp) * ncol(S_mat_est_add_temp)), floor(miss_prop_vec[rep_miss] * nrow(S_mat_est_add_temp) * ncol(S_mat_est_add_temp)))] <- NA
					### filling NAs randomly such that total number of NAs = miss_prop_vec[rep_miss] * p ^ 2
					S_mat_est_add_list[[rep_miss + 1]] <- S_mat_est_add_temp
				}
			}
			
			log_Lambda_2_est_vec <- log_Lambda_4_est_vec <- G_2_est_vec <- G_4_est_vec <- rep(0, length(S_mat_est_add_list))
			### (length(miss_prop_vec) + 1) by 1
	
			for(rep_Sigma in 1 : length(S_mat_est_add_list)){
	
				res_sig_est <- BEST_UNBIASED_ESTIMATOR(S_mat = S_mat_est_add_list[[rep_Sigma]], p_vec = p_vec)
				Sig_A_mat_est <- pmax(res_sig_est$A_mat, 1e-10)
				Sig_B_mat_est <- res_sig_est$B_mat
				Gamma_mat_est <- COMPUTE_GAMMA_MATRIX(p_vec = p_vec)
				### p by p
				V_list_est <- list()
				Y_mat_est <- matrix(0, nrow = M, ncol = p)
				### M by p
				Y_bar_vec_est <- rep(0, p)
				### p by 1
				for(m in 1 : M){
					V_list_est[[m]] <- Gamma_mat_est %*% W_list[[m]] %*% t(Gamma_mat_est)
					### p by p
					Y_mat_est[m, ] <- sqrt(n_vec[m]) * Gamma_mat_est %*% X_bar_mat[m, ]
					### p by 1
					Y_bar_vec_est <- Y_bar_vec_est + sqrt(n_vec[m]) * Y_mat_est[m, ] / n
					### p by 1
				}
	
				if(M == 1){
					nu_vec_test_est <- sqrt(n) * drop(Gamma_mat_est %*% mu_vec_test)
					### p by 1
					H_mat_est <- (Y_mat_est[1, ] - nu_vec_test_est) %*% t(Y_mat_est[1, ] - nu_vec_test_est)
					### p by 1
				} else if (M > 1){
					H_mat_est <- matrix(0, nrow = p, ncol = p)
					for(m in 1 : M){
						H_mat_est <- H_mat_est + (Y_mat_est[m, ] - sqrt(n_vec[m]) * Y_bar_vec_est) %*% t(Y_mat_est[m, ] - sqrt(n_vec[m]) * Y_bar_vec_est)
						### p by p
					}
				}

				if(M == 1){
		
					log_Lambda_2_est_vec[rep_Sigma] <- COMPUTE_EMPIRICAL_LOG_LAMBDA_2(n = n, p_vec = p_vec, V_mat = V_list_est[[1]], H_mat = H_mat_est)
		
					The_A_mat <- solve(Sig_A_mat_est)
					The_B_mat <- - solve(Sig_A_mat_est + Sig_B_mat_est %*% diag(p_vec)) %*% Sig_B_mat_est %*% solve(Sig_A_mat_est)
					Theta_mat_est <- BLOCK_HADAMARD_PRODUCT(A_mat = The_A_mat, B_mat = The_B_mat, p_vec = p_vec)
					G_2_est_vec[rep_Sigma] <- n * drop(t(X_bar_mat[1, ] - mu_vec_test) %*% Theta_mat_est %*% (X_bar_mat[1, ] - mu_vec_test))
	
					log_Lambda_4_est_vec[rep_Sigma] <- G_4_est_vec[rep_Sigma] <- NA
	
				} else if (M > 1){
					log_Lambda_2_est_vec[rep_Sigma] <- G_2_est_vec[rep_Sigma] <- NA
	
					log_Lambda_4_est_vec[rep_Sigma] <- COMPUTE_EMPIRICAL_LOG_LAMBDA_4(n_vec = n_vec, p_vec = p_vec, V_list = V_list_est, H_mat = H_mat_est)
		
					The_A_mat <- solve(Sig_A_mat_est)
					The_B_mat <- - solve(Sig_A_mat_est + Sig_B_mat_est %*% diag(p_vec)) %*% Sig_B_mat_est %*% solve(Sig_A_mat_est)
					Theta_mat_est <- BLOCK_HADAMARD_PRODUCT(A_mat = The_A_mat, B_mat = The_B_mat, p_vec = p_vec)
					G_4_est <- 0
					for (m in 1 : M){
						G_4_est <- G_4_est + n_vec[m] * drop(t(X_bar_mat[m, ] - X_bar_vec) %*% Theta_mat_est %*% (X_bar_mat[m, ] - X_bar_vec))
					}
					G_4_est_vec[rep_Sigma] <- G_4_est
				}
			}
			rep_error <- rep_error + 1
		},error = function(e){})
	}
	
	return(rbind(
		log_Lambda_2_est_vec, 
		log_Lambda_4_est_vec, 
		G_2_est_vec, 
		G_4_est_vec)) 
	### 4(2) by dim(miss_prop_vec) + 1
}

COMPUTE_THEORETICAL_DISTRIBUTIONS <- function(n_vec, p_vec, reps_max, nu_mat_0, nu_vec_test, Xi_mat_0, mu_mat_0, mu_vec_test, Sig_A_mat_0, Sig_B_mat_0, BLOCK_HADAMARD_PRODUCT){

	### INPUT
	### n_vec: M by 1
	### p_vec: K by 1
	### reps_max: 1 by 1
	### nu_mat_0: p by 1 
	### nu_vec_test: p by 1
	### Xi_mat_0: p by p 
	### mu_mat_0: M by p
	### mu_vec_test: p by 1
	### Sig_A_mat_0: K by K
	### Sig_B_mat_0: K by K
	### OUTPUT
	### logLambda1_vec: reps_max by 1
	### logLambda2_vec: reps_max by 1
	### logLambda3_vec: reps_max by 1
	### logLambda4_vec: reps_max by 1
	
	COMPUTE_DIAGONAL_BLOCKS <- function(M_mat, p_vec) {
		  if (nrow(M_mat) != ncol(M_mat)) {
			stop("M must be a square matrix.")
		  }
		  if (sum(p_vec) != nrow(M_mat)) {
			stop("Sum of sizes must equal the matrix dimension.")
		  }
		  
		  idx <- cumsum(c(0, p_vec))
		  block_list <- vector("list", length(p_vec))
		  
		  for (i in seq_along(p_vec)) {
			row_idx <- (idx[i] + 1):idx[i + 1]
			col_idx <- (idx[i] + 1):idx[i + 1]
			block_list[[i]] <- M_mat[row_idx, col_idx, drop = FALSE]
		  }
		  
		  return(block_list)
	}
	
	GENERATE_WISHART_VARIATES <- function(n, df_para, Sigma_mat, OmegaI_mat, type = 1) {
		
		### generate Wishart random variates such that their 
		### noncentral parameter is type 1: mu %*% t(mu)
		### mean = df_para * Sigma_mat + mu %*% t(mu)
		### note: OmegaI_mat must be rank 1
		
		### check symmetry ###
		if (!isSymmetric(OmegaI_mat)) stop("OmegaI_mat must be symmetric")
  
		### eigen decomposition ###
		eig <- eigen(OmegaI_mat, symmetric = TRUE)
  
		### check rank 1 ###
		pos_eig <- which(abs(eig$values) > 1e-8)
		if (length(pos_eig) != 1) stop("OmegaI_mat must be rank 1 and positive semidefinite")
  
		### Compose mu_vec ###
		lambda <- eig$values[pos_eig]
		v_vec <- eig$vectors[, pos_eig]
		if (lambda < 0) stop("OmegaI_mat must be positive semidefinite")
  
		mu_vec <- sqrt(lambda) * v_vec
		### p by 1
		p <- nrow(Sigma_mat)
		res_array <- array(0, dim = c(p, p, n))
		### p by p by n
			
		### Generate Wishart matrices ###
		for (i in 1 : n) {
			X <- matrix(0, nrow = p, ncol = df_para)
			for (j in 1 : df_para) {
				X[, j] <- mvtnorm::rmvnorm(1, mean = mu_vec / sqrt(df_para), sigma = Sigma_mat)
			}
			res_array[,,i] <- X %*% t(X)
		}
		return(res_array)
	}

	GENERATE_LOG_DET_MATRIX_DIRICHLET_VARIATES <- function(K, n_vec, Sigma_mat, reps_max){
	
		### K: the dimension of variates
		### n_vec: a M by 1 vector
		### Sigma_mat: a K by K covariance matrix
		
		M <- length(n_vec)
		### 1 by 1
		log_det_mat <- matrix(0, reps_max, M)
		### reps_max by M
		V00_sum_array <- array(0, dim = c(K, K, reps_max))
		### K by K by reps_max
		
		for(m in 1 : M){
			V00_mat_temp <- matrixsampling::rwishart(n = reps_max, nu = n_vec[m] - 1, Sigma = Sigma_mat)
			### K by K by reps_max
			log_det_mat[, m] <- log(apply(V00_mat_temp, 3, det))
			### reps_max by 1
			V00_sum_array <- V00_sum_array + V00_mat_temp
			### K by K by reps_max
		}
		
		n_mat <- matrix(rep(n_vec / 2, reps_max), reps_max, M, byrow = TRUE)
		### reps_max by M, first column is n ^ (1)/2, ..., n ^ (1)/2
				
		return(rowSums(n_mat * log_det_mat) - sum(n_vec) / 2 * log(apply(V00_sum_array, 3, det)))
		### reps_max by 1
	}
	
	GENERATE_LOG_WILKS_LAMBDA_VARIATES <- function(df1, df2, Sigma_mat, OmegaI_mat, reps_max, GENERATE_WISHART_VARIATES){
		
		### df1: the degree of freedoms for the single component
		### df2: the degree of freedoms for the second component
		
		V00_mat_array <- matrixsampling::rwishart(n = reps_max, nu = df1, Sigma = Sigma_mat)
		### p by p by reps_max
		
		if(norm(OmegaI_mat, "2") < 1e-10){
			H00_mat_array <- matrixsampling::rwishart(n = reps_max, nu = df2, Sigma = Sigma_mat)
		} else{
			H00_mat_array <- GENERATE_WISHART_VARIATES(n = reps_max, df_para = df2, Sigma_mat = Sigma_mat, OmegaI_mat = OmegaI_mat, type = 1)
			### Theta refers to OmegaI_mat, the first type of noncentrality parameters
			### p by p by reps_max
		}
		
		return(log(apply(V00_mat_array, 3, det)) - log(apply(V00_mat_array + H00_mat_array, 3, det)))
	}
	
	n <- sum(n_vec)
	M <- length(n_vec)
	p <- sum(p_vec)
	K <- length(p_vec)
	f_vec <- n_vec / n
	### M by 1
	
	P_mat <- diag(p_vec)
	### K by K
	Psq_mat <- diag(p_vec ^ (1 / 2))
	### K by K
	Sig_D_mat_0 <- Sig_A_mat_0 + Sig_B_mat_0 %*% P_mat
	### K by K
	Sig_Dtld_mat_0 <- Sig_A_mat_0 + Psq_mat %*% Sig_B_mat_0 %*% Psq_mat
	### K by K		
	
	C_p_mat <- matrix(0, 1, 1)
	for(k in 1 : K){
		C_p_mat <- Matrix::bdiag(C_p_mat, matrix(1 / p_vec[k], nrow = 1, ncol = p_vec[k]))
	}
	C_p_mat <- as.matrix(C_p_mat[- 1, - 1])
	### K by p
	
	p_bar <- matrix(0, 2, K)
	for(k in 1 : K){
		p_bar[1, k] <- sum(p_vec[0 : (k - 1)]) + 1
		p_bar[2, k] <- sum(p_vec[1 : k])
	}
	
	if(M == 1){
		
		logLambda3_vec <- logLambda3_chisq_vec <- logLambda4B_vec <- logLambda4F_vec <- logLambda4_chisq_vec <- G4_vec <- G4_chisq_vec <- G4F_vec <- NULL
		
		################################
		### calculate logLambda1_vec ###
		################################
		
		V_array <- matrixsampling::rwishart(n = reps_max, nu = n - 1, Sigma = Xi_mat_0)
		### p by p by reps_max

		logLambda1_vec <- apply(V_array, 3, function(V_mat, p_vec, COMPUTE_DIAGONAL_BLOCKS){
			K <- length(p_vec)
			V_diag_list <- COMPUTE_DIAGONAL_BLOCKS(V_mat, c(K, p_vec - 1))
			### (K + 1) by from K to pk - 1 
			res <- log(det(V_mat)) - log(det(V_diag_list[[1]]))
			for(k in 1 : K){
				res <- res - (p_vec[k] - 1) * log(sum(diag(V_diag_list[[k + 1]] / (p_vec[k] - 1))))
			}
			return(res)
		}, p_vec = p_vec, COMPUTE_DIAGONAL_BLOCKS = COMPUTE_DIAGONAL_BLOCKS)
		### reps_max by 1
		logLambda1_vec <- (n / 2) * logLambda1_vec
		### reps_max by 1
		
		f_box <- p * (p + 1) / 2 - K * (K + 3) / 2
		rho_box <- 1 - (2 * (p ^ 3 - K ^ 3) + 9 * (p ^ 2 - K ^ 2) + 5 * p - 17 * K - 4 * sum((p_vec - 1) ^ (- 1))) / (12 * n * f_box)
		omega_box <- (- 6 * (p ^ 2 - K ^ 2 + p - K - 2 * K) * ((1 - rho_box) * n - 1) ^ 2 + 12 * (2 * (1 - rho_box) * n * f_box - (p ^ 2 - K ^ 2) - (p - K) + 2 * K) * ((1 - rho_box) * n - 1) - (p ^ 4 - K ^ 4) - 2 * (p ^ 3 - K ^ 3) + p ^ 2 - K ^ 2 + 2 * (p - K)) / (- 48 * n ^ 2 * rho_box ^ 2)
 		logLambda1_box_vec <- - ((1 - omega_box) * rchisq(reps_max, f_box) / rho_box + omega_box * rchisq(reps_max, f_box + 4) / rho_box) / 2
		### reps_max by 1
		
		mu_norm <- - (p - K) - log(1 - p / (n - 1)) * (n - p - 3 / 2) + log(1 - K / (n - 1)) * (n - K - 3 / 2) + K / (n - 1)
		### 1 by 1
		sigma2_norm <- - 2 * (log(1 - p / (n - 1)) - log(1 - K / (n - 1)) + (p - K) / (n - 1))
		### 1 by 1
		logLambda1_norm_vec <- (n / 2) * rnorm(reps_max, mean = mu_norm, sd = sqrt(sigma2_norm))
		### reps_max by 1
		
		logLambda1_chisq_vec <- - rchisq(reps_max, f_box) / 2
		### reps_max by 1
		
		################################
		### calculate logLambda2_vec ###
		################################
				
		OmegaI_mat <- (nu_mat_0[1, ] - nu_vec_test) %*% t(nu_mat_0[1, ] - nu_vec_test)
		### p by p
		OmegaI_diag_list <- COMPUTE_DIAGONAL_BLOCKS(OmegaI_mat, c(K, p_vec - 1))
		### (K + 1) by from K to pk - 1
		OmegaII_mat <- 1 * solve(Xi_mat_0) %*% OmegaI_mat
		### p by p due to df = 1
		OmegaII_diag_list <- COMPUTE_DIAGONAL_BLOCKS(OmegaII_mat, c(K, p_vec - 1))
		### (K + 1) by from K to pk - 1
		
		logLambda2_WilksLambda_vec <- (n / 2) * GENERATE_LOG_WILKS_LAMBDA_VARIATES(df1 = n - 1, df2 = 1, Sigma_mat = Sig_Dtld_mat_0, OmegaI_mat = OmegaI_diag_list[[1]], reps_max = reps_max, GENERATE_WISHART_VARIATES = GENERATE_WISHART_VARIATES)
		### reps_max by 1
		
		Y_k_mat <- matrix(0, reps_max, K)
		### reps_max by K
		for(k in 1 : K){
		 	Y_k_mat[, k] <- (p_vec[k] - 1) * log(1 - rbeta(reps_max, (p_vec[k] - 1) / 2, (n - 1) * (p_vec[k] - 1) / 2, max(0, sum(diag(OmegaII_diag_list[[k + 1]])))))
		}
		logLambda2B_vec <- logLambda2_WilksLambda_vec + (n / 2) * rowSums(Y_k_mat)
		### reps_max by 1
		
		logF_mat <- matrix(0, reps_max, K)
		### reps_max by K
		for(k in 1 : K){
			logF_mat[, k] <- (p_vec[k] - 1) * log1p(rf(reps_max, p_vec[k] - 1, (p_vec[k] - 1) * (n - 1), max(0, sum(diag(OmegaII_diag_list[[k + 1]])))) / (n - 1))
		}
		logLambda2F_vec <- logLambda2_WilksLambda_vec - (n / 2) * rowSums(logF_mat)
		### reps_max by 1
		
		logLambda2_chisq_vec <- - rchisq(reps_max, df = p) / 2
		### reps_max by 1
		
		########################
		### calculate G2_vec ###
		########################
			
		G2_vec <- rep(0, reps_max)
						
		for(k in 1 : K){
			delta_k <- max(0, drop(t((mu_mat_0[1, ] - mu_vec_test)[p_bar[1, k] : p_bar[2, k]]) %*% (1 / Sig_A_mat_0[k, k] * diag(p_vec[k]) - 1 / (Sig_A_mat_0[k, k] * p_vec[k]) * matrix(1, p_vec[k], p_vec[k])) %*% ((mu_mat_0[1, ] - mu_vec_test)[p_bar[1, k] : p_bar[2, k]])))
			
			G2_vec <- G2_vec + (p_vec[k] - 1) * rf(reps_max, df1 = p_vec[k] - 1, df2 = (p_vec[k] - 1) * (n - 1), ncp = delta_k)
		}
		
		delta_kp1 <- max(0, drop(n * t(mu_mat_0[1, ] - mu_vec_test) %*% (t(C_p_mat) %*% P_mat %*% solve(Sig_D_mat_0) %*% C_p_mat) %*% (mu_mat_0[1, ] - mu_vec_test)))
		
		G2_vec <- G2_vec + K * (n - 1) / (n - K) * rf(reps_max, df1 = K, df2 = n - K, ncp = delta_kp1)
		
		G2_chisq_vec <- rchisq(reps_max, df = p)
		### reps_max by 1
		
	} else if(M > 1){
		
		logLambda1_vec <- logLambda1_box_vec <- logLambda1_norm_vec <- logLambda1_chisq_vec <- logLambda2B_vec <- logLambda2F_vec <- logLambda2_chisq_vec <- G2_vec <- G2_chisq_vec <- NULL
		
		################################
		### calculate logLambda3_vec ###
		################################
		
		logLambda30_vec <- GENERATE_LOG_DET_MATRIX_DIRICHLET_VARIATES(K = K, n_vec = n_vec, Sigma_mat = Sig_Dtld_mat_0, reps_max = reps_max)
		### reps_max by 1
		
		logLambda3k_mat <- matrix(0, reps_max, K)
		### reps_max by K
		for(k in 1 : K){
			logLambda3k_mat_temp <- (p_vec[k] - 1) * matrix(rep(n_vec / 2, reps_max), reps_max, M, byrow = TRUE) * log(rdirichlet(reps_max, (p_vec[k] - 1) * (n_vec - 1) / 2)) 
			### reps_max by M
			logLambda3k_mat[, k] <- rowSums(logLambda3k_mat_temp)
			### reps_max by 1
		}
		logLambda3k_vec <- rowSums(logLambda3k_mat)
		### reps_max by 1
		
		logLambda3_vec <- - p * n / 2 * sum(f_vec * log(f_vec)) + logLambda30_vec + logLambda3k_vec
		### reps_max by 1
		
		logLambda3_chisq_vec <- - rchisq(reps_max, df = (M - 1) * K * (K + 3) / 2) / 2
		### reps_max by 1
	
		################################
		### calculate logLambda4_vec ###
		################################
		
		AY_mat <- diag(M) - sqrt(f_vec) %*% t(sqrt(f_vec))
		### M by M
		MY_mat <- matrix(0, nrow = p, ncol = M)
		### p by M
		for(m in 1 : M){
			MY_mat[, m] <- nu_mat_0[m, ]
		}
		
		OmegaI_mat <- MY_mat %*% AY_mat %*% t(MY_mat)
		### p by p
		OmegaI_diag_list <- COMPUTE_DIAGONAL_BLOCKS(OmegaI_mat, c(K, p_vec - 1))
		### (K + 1) by from K to pk - 1
		OmegaII_mat <- (M - 1) * solve(Xi_mat_0) %*% OmegaI_mat
		### p by p
		OmegaII_diag_list <- COMPUTE_DIAGONAL_BLOCKS(OmegaII_mat, c(K, p_vec - 1))
		### (K + 1) by from K to pk - 1
		
		logLambda4_WilksLambda_vec <- (n / 2) * GENERATE_LOG_WILKS_LAMBDA_VARIATES(df1 = n - M, df2 = M - 1, Sigma_mat = Sig_Dtld_mat_0, OmegaI_mat = OmegaI_diag_list[[1]], reps_max = reps_max, GENERATE_WISHART_VARIATES = GENERATE_WISHART_VARIATES)
		### reps_max by 1
		
		Y_k_mat <- matrix(0, reps_max, K)
		### reps_max by K 
		for(k in 1 : K){
			Y_k_mat[, k] <- (p_vec[k] - 1) * log(1 - rbeta(reps_max, (M - 1) * (p_vec[k] - 1) / 2, (n - M) * (p_vec[k] - 1) / 2, max(0, sum(diag(OmegaII_diag_list[[k + 1]])))))
		}
		logLambda4B_vec <- logLambda4_WilksLambda_vec + (n / 2) * rowSums(Y_k_mat)
		### reps_max by 1
		
		logF_mat <- matrix(0, reps_max, K)
		### reps_max by K
		for(k in 1 : K){
			logF_mat[, k] <- (p_vec[k] - 1) * log1p((M - 1) * rf(reps_max, (p_vec[k] - 1) * (M - 1), (p_vec[k] - 1) * (n - M), max(0, sum(diag(OmegaII_diag_list[[k + 1]])))) / (n - M))
		}
		logLambda4F_vec <- logLambda4_WilksLambda_vec - (n / 2) * rowSums(logF_mat)
		### reps_max by 1
		
		logLambda4_chisq_vec <- - rchisq(reps_max, df = (M - 1) * p) / 2
		### reps_max by 1
		
		########################
		### calculate G4_vec ###
		########################
		
		G4Fsum_vec <- rep(0, reps_max)
		### reps_max by 1
		
		mu_long_vec <- as.vector(t(mu_mat_0))
		### (Mp) by 1
		MMt_mat <- t(diag(1 / sqrt(n_vec)) %*% (diag(M) - matrix(1, M, M) %*% diag(n_vec) / n)) %*% (diag(1 / sqrt(n_vec)) %*% (diag(M) - matrix(1, M, M) %*% diag(n_vec) / n))
		### M by M
		
		for(k in 1 : K){
			Bdiag_mat <- matrix(0, p, p)
			### p by p
			Bdiag_mat[p_bar[1, k] : p_bar[2, k], p_bar[1, k] : p_bar[2, k]] <- 1 / Sig_A_mat_0[k, k] * diag(p_vec[k]) - 1 / (Sig_A_mat_0[k, k] * p_vec[k]) * matrix(1, p_vec[k], p_vec[k])
			### p by p
			delta_k <- max(0, drop(t(mu_long_vec) %*% kronecker(MMt_mat, Bdiag_mat) %*% (mu_long_vec)))
		
			G4Fsum_vec <- G4Fsum_vec + (M - 1) * (p_vec[k] - 1) * rf(reps_max, df1 = (M - 1) * (p_vec[k] - 1), df2 = (p_vec[k] - 1) * (n - M), ncp = delta_k)
			### reps_max by 1
		}
		
		Sigma_Y_mat <- Sig_A_mat_0 %*% solve(diag(p_vec)) + Sig_B_mat_0
		### K by K
		Omega_Y_mat <- matrix(0, nrow = K, ncol = K)
		### K by K
		mu_bar_vec <- rep(0, p)
		### p by 1
		for(m in 1 : M){
			mu_bar_vec <- mu_bar_vec + n_vec[m] * mu_mat_0[m, ]
		}
		mu_bar_vec <- mu_bar_vec / n
		
		for(m in 1 : M){
			Omega_Y_mat <- Omega_Y_mat + n_vec[m] * C_p_mat %*% (mu_mat_0[m, ] - mu_bar_vec) %*% t(mu_mat_0[m, ] - mu_bar_vec)  %*% t(C_p_mat) 
		}
		### K by K
		
		if(norm(Omega_Y_mat, "2") < 1e-10){
			W1_array <- matrixsampling::rwishart(n = reps_max, nu = M - 1, Sigma = Sigma_Y_mat)
			### K by K by reps_max
		} else{
			W1_array <- GENERATE_WISHART_VARIATES(n = reps_max, df_para = M - 1, Sigma_mat = Sigma_Y_mat, OmegaI_mat = Omega_Y_mat, type = 1)
			### K by K by reps_max
		}
			
		W2_array <- matrixsampling::rwishart(n = reps_max, nu = n - M, Sigma = Sigma_Y_mat)
		### K by K by reps_max
		
		G4_vec <- G4Fsum_vec + (n - M) * sapply(1 : dim(W1_array)[3], function(i) sum(diag(W1_array[,,i] %*% solve(W2_array[,,i]))))
		### reps_max by 1
		
		G4_chisq_vec <- rchisq(reps_max, (M - 1) * p)
		### reps_max by 1
		
		### Betz (1987) uses F-variate to approximate T0^2
		### (1) para_l <- n - M - p - 1
		### (2) para_b <- (para_l + para_q) * (para_l + p)/ ((para_l - 2) * (para_l + 1))
		### (3) df_1 <- p * para_q
		### (4) df_2 <- 4 + (p * para_q + 2) / (para_b - 1)
		### (5) para_a <- p * para_q * (df_2 - 2) / (para_l * df_2)
			
		delta_kp1 <- sum(diag(solve(Sigma_Y_mat) %*% Omega_Y_mat))
		
		para_q <- M - 1
		para_p <- K
		para_l <- n - M - para_p - 1
		para_g <- (para_q + 2 * delta_kp1 / para_p) / (para_q + delta_kp1 / para_p)
		para_h <- (para_q + delta_kp1 / para_p) ^ 2 / (para_q + 2 * delta_kp1 / para_p)
		
		df_1 <- para_p * para_h
		para_b <- (para_l + para_h) * (para_l + para_p)/ ((para_l - 2) * (para_l + 1))
		df_2 <- 4 + (para_p * para_h + 2) / (para_b - 1)
		para_a <- para_p * para_h * (df_2 - 2) / (para_l * df_2)
		
		G4F_vec <- G4Fsum_vec + (n - M) * para_g * para_a * rf(reps_max, df1 = df_1, df2 = df_2, ncp = 0)
	}
	
	return(list(
		logLambda1_vec = logLambda1_vec,
	logLambda1_box_vec = logLambda1_box_vec,
   logLambda1_norm_vec = logLambda1_norm_vec,
  logLambda1_chisq_vec = logLambda1_chisq_vec,    
	   logLambda2B_vec = logLambda2B_vec, 
	   logLambda2F_vec = logLambda2F_vec,
  logLambda2_chisq_vec = logLambda2_chisq_vec,
		logLambda3_vec = logLambda3_vec,
  logLambda3_chisq_vec = logLambda3_chisq_vec,
	   logLambda4B_vec = logLambda4B_vec,
	   logLambda4F_vec = logLambda4F_vec, 
  logLambda4_chisq_vec = logLambda4_chisq_vec,
			    G2_vec = G2_vec,
		  G2_chisq_vec = G2_chisq_vec,	
				G4_vec = G4_vec,
		       G4F_vec = G4F_vec,
		  G4_chisq_vec = G4_chisq_vec
	))
}

MEAN_VECTOR_DESIGN <- function(true_null_zero_prop, p, sq_sum){
	
	equal_case <- function(x, sq_sum) {
		### input must be binary 0 or 1
		if(all(x == 0)){
			return(x)
		} else {
			return(x * sqrt(sq_sum / sum(x)))
		}
	}
	
	increase_case <- function(x, sq_sum) {
		### input must be binary 0 or 1
		if(all(x == 0)){
			return(x)
		} else {
			return(c(seq(1 / sum(x), 1, 1 / sum(x)), rep(0, length(x) - length(seq(1 / sum(x), 1, 1 / sum(x))))) * sqrt(sq_sum / sum(seq(1 / sum(x), 1, 1 / sum(x)) ^ 2)))
		}
	}
	
	decrease_case <- function(x, sq_sum) {
		### input must be binary 0 or 1
		if(all(x == 0)){
			return(x)
		} else {
			return(- c(seq(1 / sum(x), 1, 1 / sum(x)), rep(0, length(x) - length(seq(1 / sum(x), 1, 1 / sum(x))))) * sqrt(sq_sum / sum(seq(1 / sum(x), 1, 1 / sum(x)) ^ 2)))
		}
	}

	true_null_mat_temp <- matrix(0, nrow = length(true_null_zero_prop), ncol = p, byrow = TRUE)
	for(perp in 1 : length(true_null_zero_prop)){
		num_1 <- floor((1 - true_null_zero_prop[perp]) * p)
		num_0 <- p - num_1
		true_null_mat_temp[perp, ] <- c(rep(1, num_1), rep(0, num_0))
	}
	true_null_mat_list <- rep(list(true_null_mat_temp), 3)
	names(true_null_mat_list) <- c("equal", "increase", "decrease")
	### list_1: equal; list_2: increasing; list_3: decreasing
	true_null_mat_list$equal <- t(apply(true_null_mat_list$equal, 1, equal_case, sq_sum))
	true_null_mat_list$increase <- t(apply(true_null_mat_list$increase, 1, increase_case, sq_sum))
	true_null_mat_list$decrease <- t(apply(true_null_mat_list$decrease, 1, decrease_case, sq_sum))
	return(true_null_mat_list = true_null_mat_list)
}

COMPARE_POWERS_FOR_MEAN_TESTS <- function(n_vec, p_vec, mu_mat_0, mu_vec_test, Sigma_mat_0, Gamma_mat_0, Sig_A_mat_0, Sig_B_mat_0, alpha, reps_emp_max, reps_the_max, model_seed,  miss_prop_vec, t_df, COMPUTE_THEORETICAL_DISTRIBUTIONS, COMPUTE_EMPIRICAL_TEST_STATISTICS_SIMPLIFIED, COMPUTE_EMPIRICAL_LOG_LAMBDA_1, COMPUTE_EMPIRICAL_LOG_LAMBDA_2, COMPUTE_EMPIRICAL_LOG_LAMBDA_3, COMPUTE_EMPIRICAL_LOG_LAMBDA_4, BLOCK_HADAMARD_PRODUCT, BEST_UNBIASED_ESTIMATOR, COMPUTE_GAMMA_MATRIX){

	### INPUT
	### n_vec: M by 1
	### p_vec: K by 1
	### mu_mat_0: M by p
	### mu_vec_test: p by 1, for M = 1
	### Sigma_mat_0: p by p
	### Gamma_mat_0: p by p
	### Sig_A_mat_0: K by K
	### Sig_B_mat_0: K by K
	### alpha: 1 by 1
	### reps_emp_max: 1 by 1
	### reps_the_max: 1 by 1
	### model_seed: 1 by 1
	### miss_prop_vec: dim by 1
	### t_df: 1 by 1
	
	M <- length(n_vec)
	n <- sum(n_vec)
	
	Xi_mat_0 <- Gamma_mat_0 %*% Sigma_mat_0 %*% t(Gamma_mat_0)
	Xi_mat_0 <- (Xi_mat_0 + t(Xi_mat_0)) / 2
	### p by p
	
	### calculate the theoretical alpha-quantiles ###

	set.seed(model_seed)
	
	### Note: under the null hypotheses ###
	### M = 1, null -> mu_mat_0 = nu_mat_0 = zero vector
	###		   null -> mu_vec_test = nu_vec_test = zero vector
	###	M > 1, null -> mu_mat_0 and nu_mat_0 have same rows
	###		   null -> mu_vec_test = nu_vec_test = NULL
	
	nu_mat_0_the <- mu_mat_0_the <- matrix(0, M, p)
	if(!is.null(mu_vec_test)){
		mu_vec_test_the <- nu_vec_test_the <- rep(0, p)
	} else{
		mu_vec_test_the <- nu_vec_test_the <- NULL
	}
	
	res_the <- COMPUTE_THEORETICAL_DISTRIBUTIONS(
					 n_vec = n_vec, 
					 p_vec = p_vec, 
				  reps_max = reps_the_max, 
			      nu_mat_0 = nu_mat_0_the, 
			   nu_vec_test = nu_vec_test_the,
				  Xi_mat_0 = Xi_mat_0, 
			      mu_mat_0 = mu_mat_0_the, 
			   mu_vec_test = mu_vec_test_the,
			   Sig_A_mat_0 = Sig_A_mat_0, 
			   Sig_B_mat_0 = Sig_B_mat_0, 
	BLOCK_HADAMARD_PRODUCT = BLOCK_HADAMARD_PRODUCT)
		
	### generate the empirical test statistics ###
	
	res_emp <- pbapply::pbreplicate(
			   n = reps_emp_max, 
			expr = COMPUTE_EMPIRICAL_TEST_STATISTICS_SIMPLIFIED(
		   n_vec = n_vec, 
	       p_vec = p_vec, 
		mu_mat_0 = mu_mat_0, 
	 mu_vec_test = mu_vec_test, 
	 Sigma_mat_0 = Sigma_mat_0,
   miss_prop_vec = miss_prop_vec, 
		    t_df = t_df, 
  COMPUTE_EMPIRICAL_LOG_LAMBDA_1 = COMPUTE_EMPIRICAL_LOG_LAMBDA_1, 
  COMPUTE_EMPIRICAL_LOG_LAMBDA_2 = COMPUTE_EMPIRICAL_LOG_LAMBDA_2, 
  COMPUTE_EMPIRICAL_LOG_LAMBDA_3 = COMPUTE_EMPIRICAL_LOG_LAMBDA_3, 
  COMPUTE_EMPIRICAL_LOG_LAMBDA_4 = COMPUTE_EMPIRICAL_LOG_LAMBDA_4,
		  BLOCK_HADAMARD_PRODUCT = BLOCK_HADAMARD_PRODUCT, 
		 BEST_UNBIASED_ESTIMATOR = BEST_UNBIASED_ESTIMATOR, 
			COMPUTE_GAMMA_MATRIX = COMPUTE_GAMMA_MATRIX))
  ### [1,2,3] = 4 by (dim(miss_prop_vec) + 1) by reps_emp_max
		
	if(M == 1){
		
		W2B_the <- - res_the$logLambda2B_vec
		W2F_the <- - res_the$logLambda2F_vec
		G2_the <- res_the$G2_vec
		
		W2B_alpha <- quantile(x = W2B_the, probs = 1 - alpha)
		W2F_alpha <- quantile(x = W2F_the, probs = 1 - alpha)
		G2_alpha <- quantile(x = G2_the, probs = 1 - alpha)
		
		W2_emp_est <- - matrix(res_emp[1, , ], nrow = length(miss_prop_vec) + 1, ncol = reps_emp_max)
		### (dim(miss_prop_vec) + 1) by reps_emp_max
		G2_emp_est <- matrix(res_emp[3, , ], nrow = length(miss_prop_vec) + 1, ncol = reps_emp_max)
		### (dim(miss_prop_vec) + 1) by reps_emp_max
		
		W2B_rej <- apply(W2_emp_est, 1, function(x, alpha) mean(1 * (x >= alpha)), alpha = W2B_alpha)
		### (dim(miss_prop_vec) + 1)
		W2F_rej <- apply(W2_emp_est, 1, function(x, alpha) mean(1 * (x >= alpha)), alpha = W2F_alpha)
		### (dim(miss_prop_vec) + 1)
		G2_rej <- apply(G2_emp_est, 1, function(x, alpha) mean(1 * (x >= alpha)), alpha = G2_alpha)
		### (dim(miss_prop_vec) + 1)
		
		W4B_rej <- NULL
		W4F_rej <- NULL
		G4_rej <- NULL
		
	} else if(M > 1){
		
		W4B_the <- - res_the$logLambda4B_vec
		W4F_the <- - res_the$logLambda4F_vec
		G4_the <- res_the$G4_vec
		
		W4B_alpha <- quantile(x = W4B_the, probs = 1 - alpha)
		W4F_alpha <- quantile(x = W4F_the, probs = 1 - alpha)
		G4_alpha <- quantile(x = G4_the, probs = 1 - alpha)
		
		W4_emp_est <- - matrix(res_emp[2, , ], nrow = length(miss_prop_vec) + 1, ncol = reps_emp_max)
		### (dim(miss_prop_vec) + 1) by reps_emp_max
		G4_emp_est <- matrix(res_emp[4, , ], nrow = length(miss_prop_vec) + 1, ncol = reps_emp_max)
		### (dim(miss_prop_vec) + 1) by reps_emp_max
		
		W2B_rej <- NULL 
		W2F_rej <- NULL
		G2_rej <- NULL
		
		W4B_rej <- apply(W4_emp_est, 1, function(x, alpha) mean(1 * (x >= alpha)), alpha = W4B_alpha)
		### (dim(miss_prop_vec) + 1)
		W4F_rej <- apply(W4_emp_est, 1, function(x, alpha) mean(1 * (x >= alpha)), alpha = W4F_alpha)
		### (dim(miss_prop_vec) + 1)
		G4_rej <- apply(G4_emp_est, 1, function(x, alpha) mean(1 * (x >= alpha)), alpha = G4_alpha)
		### (dim(miss_prop_vec) + 1)
	}
	return(c(W2B_rej, W2F_rej, W4B_rej, W4F_rej, G2_rej, G4_rej
	))
}

##############################
### Simulation Study Setup ###
##############################

INPUT_ADDRESS <- OUTPUT_ADDRESS <- "..."

SET_NO <- 1

SET_UP <- matrix(c(
	1, 50,   0,   0, 1e4, 1e4, 1e-2, 0e-2, 0, 4, 0.05, 2024, Inf, ### p = 100, benchmark
	1, 50,   0,   0, 1e4, 1e4, 1e-2, 1e-2, 0, 4, 0.05, 2024, Inf, ### p = 100, noise
	1, 50,   0,   0, 1e4, 1e4, 1e-2, 5e-2, 0, 4, 0.05, 2024, Inf, ### p = 100, noise
	1, 50,   0,   0, 1e4, 1e4, 1e-2, 0e-2, 1, 4, 0.05, 2024, Inf, ### p = 100, miss
	1, 50,   0,   0, 1e4, 1e4, 1e-2, 0e-2, 0, 4, 0.05, 2024,   1, ### p = 100, rmvt
	1, 50,   0,   0, 1e4, 1e4, 1e-2, 0e-2, 0, 4, 0.05, 2024,   3, ### p = 100, rmvt
	1, 50,   0,   0, 1e4, 1e4, 1e-2, 0e-2, 0, 4, 0.05, 2024,   5, ### p = 100, rmvt
	1, 50,   0,   0, 1e4, 1e4, 1e-2, 0e-2, 0, 4, 0.05, 2024,  10, ### p = 100, rmvt
	3, 50,   50, 50, 1e4, 1e4, 5e-1, 0e-2, 0, 4, 0.05, 2024, Inf, ### p = 100, benchmark
	3, 50,   50, 50, 1e4, 1e4, 5e-1, 1e-2, 0, 4, 0.05, 2024, Inf, ### p = 100, noise
	3, 50,   50, 50, 1e4, 1e4, 5e-1, 5e-2, 0, 4, 0.05, 2024, Inf, ### p = 100, noise
	3, 50,   50, 50, 1e4, 1e4, 5e-1, 0e-2, 1, 4, 0.05, 2024, Inf, ### p = 100, miss
	3, 50,   50, 50, 1e4, 1e4, 5e-1, 0e-2, 0, 4, 0.05, 2024,   1, ### p = 100, rmvt
	3, 50,   50, 50, 1e4, 1e4, 5e-1, 0e-2, 0, 4, 0.05, 2024,   3, ### p = 100, rmvt
	3, 50,   50, 50, 1e4, 1e4, 5e-1, 0e-2, 0, 4, 0.05, 2024,   5, ### p = 100, rmvt
	3, 50,   50, 50, 1e4, 1e4, 5e-1, 0e-2, 0, 4, 0.05, 2024,  10  ### p = 100, rmvt
	), 
	nrow = 16, ncol = 13, byrow = TRUE)
### M = 1, 3 
### sample size(s)    = 50
### MC replicate no 1 = 1e4
### MC replicate no 2 = 1e4
### eta = || mu_0 || ^ 2 / sqrt(tr(Sigma_0 ^ 2)) = 1e-2, 5e-1
### eps = 0e-2, 1e-2, 5e-2, mean = eps * p * Ip
### missing_or_not = 0, 1: 0.1, 0.2, 0.3
### scale_p_vec = 4
### significance level = 0.05
### random seed = 2024
### distribution: Inf for normal df for t

M <- SET_UP[SET_NO, 1]
n_vec <- SET_UP[SET_NO, 2 : 4]
n_vec <- n_vec[n_vec != 0]
### M by 1
n <- sum(n_vec)
### 1 by 1
reps_emp_max <- SET_UP[SET_NO, 5]
reps_the_max <- SET_UP[SET_NO, 6]
eta_scale <- SET_UP[SET_NO, 7]
eps <- SET_UP[SET_NO, 8]
if(SET_UP[SET_NO, 9] == 0){
	miss_prop_vec <- NULL
} else if (SET_UP[SET_NO, 9] == 1){
	miss_prop_vec <- c(0.05, 0.10, 0.15)
}
scale_p_vec <- SET_UP[SET_NO, 10]
sig_level <- SET_UP[SET_NO, 11]
model_seed <- SET_UP[SET_NO, 12]
t_df <- SET_UP[SET_NO, 13]

### create the UB covariance matrix ###
p_vec <- c(3, 4, 5, 6, 7) * scale_p_vec
### K by 1
K <- length(p_vec)
p <- sum(p_vec)
Sig_A_mat_0 <- diag(c(
		0.01595042, 0.21392707, 0.74912381, 0.06771268, 0.10017260))
### K by 1
Sig_B_mat_0 <- matrix(c(
		6.73139386,-1.69034339, 0.69591280,-2.93647430, 1.91315819, 
	   -1.69034339, 5.21462208, 3.81497235,-1.01011751, 0.70298054, 
        0.69591280, 3.81497235, 4.32780351,-3.35737580,-0.26890092,
	   -2.93647430,-1.01011751,-3.35737580, 6.78768893, 0.00018746,
        1.91315819, 0.70298054,-0.26890092, 0.00018746, 3.95418249), nrow = K, ncol = K, byrow = TRUE)
### K by K

if(eps == 0){
	Sigma_mat_0 <- BLOCK_HADAMARD_PRODUCT(A_mat = Sig_A_mat_0, B_mat = Sig_B_mat_0, p_vec = p_vec)
	### p by p
} else if(eps > 0){
	set.seed(2025)
	Sigma_mat_0 <- BLOCK_HADAMARD_PRODUCT(A_mat = Sig_A_mat_0, B_mat = Sig_B_mat_0, p_vec = p_vec) + rWishart(n = 1, df = p, Sigma = eps * diag(p))[,,1]
	### p by p
	set.seed(NULL)
	res_sig_0 <- BEST_UNBIASED_ESTIMATOR(S_mat = Sigma_mat_0, p_vec = p_vec)
	Sig_A_mat_0 <- res_sig_0$A_mat
	### K by K
	Sig_B_mat_0 <- res_sig_0$B_mat
	### K by K
} 
Gamma_mat_0 <- COMPUTE_GAMMA_MATRIX(p_vec = p_vec)
### p by p


### create the population mean vector ###

sq_tr_Sq <- sqrt(sum(diag(Sigma_mat_0 %*% Sigma_mat_0)))
### 1 by 1
true_null_zero_prop <- c(0.00, 0.10, 0.20, 0.50, 0.80, 0.90, 1.00)
### among p nulls, there are floor(null_zero_prop * p) are zeros (true null)
### true_null_zero_prop = prop of true nulls
true_null_zero_prop_name <- paste(true_null_zero_prop * 100, "%", sep = "")

if(M == 1){
	eta_vec <- eta_scale
	### M by 1
	true_null_mat_list <- MEAN_VECTOR_DESIGN(true_null_zero_prop, p, eta_vec * sq_tr_Sq)
} else if(M > 1) {
	eta_vec <- seq(1, 0.5, length.out = M) * eta_scale
	### M by 1
	true_null_mat_list <- list()
	for(m in 1 : M){
		true_null_mat_list[[m]] <- MEAN_VECTOR_DESIGN(true_null_zero_prop, p, eta_vec[m] * sq_tr_Sq)
	}
}

rejection_mat <- c()
### rows: T, U for equal; 
###       T, U for increasing; 
###       T, U for decreasing

if(M == 1) {
	for (types in 1 : length(true_null_mat_list)){
		true_null_mat_temp <- true_null_mat_list[[types]]
		for(sub_types in 1 : nrow(true_null_mat_temp)){
			mu_mat_temp <- true_null_mat_temp[sub_types, , drop = FALSE]
			### M by p
			power_comparison_temp <- COMPARE_POWERS_FOR_MEAN_TESTS(
					   n_vec = n_vec, 
					   p_vec = p_vec, 
					mu_mat_0 = mu_mat_temp, 
				 mu_vec_test = rep(0, p), 
				 Sigma_mat_0 = Sigma_mat_0, 
			     Gamma_mat_0 = Gamma_mat_0, 
			     Sig_A_mat_0 = Sig_A_mat_0, 
				 Sig_B_mat_0 = Sig_B_mat_0, 
					   alpha = sig_level, 
			    reps_emp_max = reps_emp_max, 
			    reps_the_max = reps_the_max, 
				  model_seed = model_seed, 
			   miss_prop_vec = miss_prop_vec,
					    t_df = t_df,			   
			   COMPUTE_THEORETICAL_DISTRIBUTIONS = COMPUTE_THEORETICAL_DISTRIBUTIONS, 
	COMPUTE_EMPIRICAL_TEST_STATISTICS_SIMPLIFIED =COMPUTE_EMPIRICAL_TEST_STATISTICS_SIMPLIFIED, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_1 = COMPUTE_EMPIRICAL_LOG_LAMBDA_1, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_2 = COMPUTE_EMPIRICAL_LOG_LAMBDA_2, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_3 = COMPUTE_EMPIRICAL_LOG_LAMBDA_3, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_4 = COMPUTE_EMPIRICAL_LOG_LAMBDA_4,
			BLOCK_HADAMARD_PRODUCT = BLOCK_HADAMARD_PRODUCT, 
		   BEST_UNBIASED_ESTIMATOR = BEST_UNBIASED_ESTIMATOR, 
			  COMPUTE_GAMMA_MATRIX = COMPUTE_GAMMA_MATRIX)
		### 3 by 1
		rejection_mat <- rbind(rejection_mat, power_comparison_temp)
		### W2B, W2F, G2; W4B, W4F, G4
		}
	}
	
} else if(M > 1) {
	for (types in 1 : length(true_null_mat_list[[1]])){
	### M 
		for (sub_types in 1 : nrow(true_null_mat_list[[1]][[1]])){
		### length(true_null_zero_prop)	
			mu_mat_temp <- matrix(0, nrow = M, ncol = p)
			### M by p
			for(m in 1 : M){
				mu_mat_temp[m, ] <- true_null_mat_list[[m]][[types]][sub_types, ]
			}
			
			power_comparison_temp <- COMPARE_POWERS_FOR_MEAN_TESTS(
					   n_vec = n_vec, 
					   p_vec = p_vec, 
					mu_mat_0 = mu_mat_temp, 
				 mu_vec_test = NULL, 
				 Sigma_mat_0 = Sigma_mat_0, 
			     Gamma_mat_0 = Gamma_mat_0, 
			     Sig_A_mat_0 = Sig_A_mat_0, 
				 Sig_B_mat_0 = Sig_B_mat_0, 
					   alpha = sig_level, 
			    reps_emp_max = reps_emp_max, 
			    reps_the_max = reps_the_max, 
				  model_seed = model_seed,
			   miss_prop_vec = miss_prop_vec,
					    t_df = t_df,			   
			   COMPUTE_THEORETICAL_DISTRIBUTIONS = COMPUTE_THEORETICAL_DISTRIBUTIONS, 
	COMPUTE_EMPIRICAL_TEST_STATISTICS_SIMPLIFIED =COMPUTE_EMPIRICAL_TEST_STATISTICS_SIMPLIFIED, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_1 = COMPUTE_EMPIRICAL_LOG_LAMBDA_1, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_2 = COMPUTE_EMPIRICAL_LOG_LAMBDA_2, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_3 = COMPUTE_EMPIRICAL_LOG_LAMBDA_3, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_4 = COMPUTE_EMPIRICAL_LOG_LAMBDA_4,
			BLOCK_HADAMARD_PRODUCT = BLOCK_HADAMARD_PRODUCT, 
		   BEST_UNBIASED_ESTIMATOR = BEST_UNBIASED_ESTIMATOR, 
			  COMPUTE_GAMMA_MATRIX = COMPUTE_GAMMA_MATRIX)
		### 3 by 1
		rejection_mat <- rbind(rejection_mat, power_comparison_temp)
		### W2B, W2F, G2; W4B, W4F, G4
		}
	}
}

rejection_mat <- data.frame(rejection_mat)

colnames(rejection_mat) <- c(t(outer(c("WB", "WF", "G"), paste0("NA", c(0, miss_prop_vec) * 100, "%"), paste, sep = "_")))

rownames(rejection_mat) <- c(
	paste("equal", true_null_zero_prop_name, sep = "_"), 
	paste("increase", true_null_zero_prop_name, sep = "_"), 
	paste("decrease", true_null_zero_prop_name, sep = "_"))

round(rejection_mat, 3)

save.image(paste(OUTPUT_ADDRESS, paste("S4_No", SET_NO, "Dim", p, "Eps", eps, "miss", ((!is.null(miss_prop_vec)) * 1), "t_df", t_df, "UB.RData", sep = "_"), sep = "/"))	