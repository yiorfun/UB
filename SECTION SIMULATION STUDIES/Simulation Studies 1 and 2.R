######################################################################
### SIMULATION STUDY 1 and 2 		    						   ###
### - Lambda1: LRT testing the covariance matrix is a UB matrix    ###
### - Lambda2: LRT testing a specified mean given a UB matrix      ###
### - Lambda3: LRT testing the equality of UB matrices             ###
### - Lambda4: LRT testing the equality of means given UB matrices ###
### - U2: Geisser's a specified mean given a UB matrix  		   ###
### - U4: Geisser's the equality of means given UB matrices        ###
### - Study 1: distribution comparison: covariance structure 	   ###
### - Study 2: distribution comparison: mean structure             ###
### - M = 1, Lambda2 with noncentral parameters					   ###
### - M > 1, Lambda4 with noncentral parameters					   ###
### - M = 1, G2 with noncentral parameters					       ###
### - M > 1, G4 with noncentral parameters					       ###
### - add the high-dimensional normal approximation for H1K1       ###
######################################################################

############################
### Loading the packages ###
############################

REQUIRED_PACKAGES <- c(
	"mvtnorm",		
	### mvtnorm::dmvnorm() and mvtnorm::rmvnorm(), compute the density and generate random vector of multivariate normal distribution
	"ggplot2", 
	### ggplot2::ggplot(), initializes a ggplot object
	"Matrix", 
	### Matrix::bdiag(), builds a block diagonal matrix given several building block matrices
	"Compositional",
	### Compositional::helm(), creates the Helmert sub-matrix
	"MCMCpack",
	### MCMCpack::rdirichlet(), generates random deviates from the Dirichlet distribution
	"pbapply"
	### pbapply::pbreplicate(), adds progress bar to replicate functions
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

COMPUTE_GAMMA_MATRIX <- function(A_mat, B_mat, p_vec){
	
	### INPUT
	### A_mat: K by K 
	### B_mat: K by K
	### p_vec: K by 1, p = sum(p_vec)
	### OUTPUT
	### Gamma_mat: p by p
	
	K <- length(p_vec)
	p <- sum(p_vec)
	D_mat <- A_mat + B_mat %*% diag(p_vec)
	### K by K
	### eigen(D_mat)$values  
	### in decreasing order
	D_eig_mat <- eigen(D_mat)$vectors ### not orthogonal
	### K by K
	Xi_mat <- matrix(0, p, K)
	### p by K
	for(k in 1 : K){
		xi_vec <- c()
		for(kp in 1 : K){
			xi_vec <- c(xi_vec, rep(D_eig_mat[kp, k], p_vec[kp]))
		}
		Xi_mat[, k] <- xi_vec / sqrt(sum(xi_vec ^ 2))
	}

	Q_mat_temp <- matrix(0, 1, 1)
	for(k in 1 : K){
		Q_mat_temp <- Matrix::bdiag(Q_mat_temp, rbind(Compositional::helm(p_vec[k]), rep(0, p_vec[k])))
	}
	Q_mat_temp <- as.matrix(Q_mat_temp[-1, -1]) 
	### deleting the first one
	for(k in 1 : K){
		 Q_mat_temp[sum(p_vec[0 : k]), ] <- Xi_mat[, k]
	}
	Gamma_mat <- Q_mat_temp
	return(Gamma_mat)
}

COMPUTE_EMPIRICAL_LOG_LAMBDA_1 <- function(n, p_vec, V_mat){
	
	### INPUT
	### n: 1 by 1, the grand sample size 
	### p_vec: K by 1
	### V_mat: p by p
	### OUTPUT
	### logLambda1: 1 by 1
	
	K <- length(p_vec)
	p_bar <- matrix(0, 2, K)
	for(k in 1 : K){
		p_bar[1, k] <- sum(p_vec[0 : (k - 1)]) + 1
		p_bar[2, k] <- sum(p_vec[1 : k])
	}
	diag_V_vec <- diag(V_mat)
	### p by 1
	
	Item_1 <- sum((p_vec - 1) * log(p_vec - 1))
	Item_2 <- log(det(V_mat))
	Item_3 <- 0
	Item_4 <- 0
	
	for(k in 1 : K){
		end_p_bar_k <- p_bar[2, k]
		within_p_bar_k <- p_bar[1, k] : (p_bar[2, k] - 1)
		Item_3 <- Item_3 - log(diag_V_vec)[end_p_bar_k]
		Item_4 <- Item_4 - (p_vec[k] - 1) * log(sum(diag_V_vec[within_p_bar_k]))
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
	
	K <- length(p_vec)
	p <- sum(p_vec)
	p_bar <- matrix(0, 2, K)
	for(k in seq(K)){
		p_bar[1, k] <- sum(p_vec[0 : (k - 1)]) + 1
		p_bar[2, k] <- sum(p_vec[1 : k])
	}
	n <- sum(n_vec)
	M <- length(n_vec)
	f_vec <- n_vec / n
	
	V_sum_mat <- Reduce("+", V_list)
	### p by p
	diag_V_sum_vec <- diag(V_sum_mat)
	### p by 1

	Item_0 <- - p * sum(f_vec * log(f_vec))
	Item_1 <- 0
	Item_2 <- 0
	Item_3 <- 0
	Item_4 <- 0
	
	for(m in 1 : M){
		for(k in 1 : K){
			end_p_bar_k <- p_bar[2, k]
			within_p_bar_k <- p_bar[1, k] : (p_bar[2, k] - 1)
			diag_Vm_vec <- diag(V_list[[m]])
			### p by 1
			Item_1 <- Item_1 + f_vec[m] * log(diag_Vm_vec[end_p_bar_k])
			Item_2 <- Item_2 + f_vec[m] * (p_vec[k] - 1) * log(sum(diag_Vm_vec[within_p_bar_k]))
			Item_3 <- Item_3 - f_vec[m] * log(diag_V_sum_vec[end_p_bar_k])
			Item_4 <- Item_4 - f_vec[m] * (p_vec[k] - 1) * log(sum(diag_V_sum_vec[within_p_bar_k]))
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
	
	K <- length(p_vec)
	p_bar <- matrix(0, 2, K)
	for(k in 1 : K){
		p_bar[1, k] <- sum(p_vec[0 : (k - 1)]) + 1
		p_bar[2, k] <- sum(p_vec[1 : k])
	}
	diag_V_vec <- diag(V_mat)
	### p by 1
	diag_D_vec <- diag(H_mat + V_mat)
	### p by 1
	
	Item_1 <- 0
	Item_2 <- 0
	Item_3 <- 0
	Item_4 <- 0
	
	for(k in 1 : K){
		end_p_bar_k <- p_bar[2, k]
		within_p_bar_k <- p_bar[1, k] : (p_bar[2, k] - 1)
		Item_1 <- Item_1 + log(diag_V_vec[end_p_bar_k])
		Item_2 <- Item_2 + (p_vec[k] - 1) * log(sum(diag_V_vec[within_p_bar_k]))
		Item_3 <- Item_3 - log(diag_D_vec[end_p_bar_k])
		Item_4 <- Item_4 - (p_vec[k] - 1) * log(sum(diag_D_vec[within_p_bar_k]))
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
	
	K <- length(p_vec)
	p_bar <- matrix(0, 2, K)
	for(k in 1 : K){
		p_bar[1, k] <- sum(p_vec[0 : (k - 1)]) + 1
		p_bar[2, k] <- sum(p_vec[1 : k])
	}
	n <- sum(n_vec)
	
	V_sum_mat <- Reduce("+", V_list)
	### p by p
	diag_V_vec <- diag(V_sum_mat)
	### p by 1
	diag_D_vec <- diag(H_mat + V_sum_mat)
	### p by 1
	
	Item_1 <- 0
	Item_2 <- 0
	Item_3 <- 0
	Item_4 <- 0
	
	for(k in seq(K)){
		end_p_bar_k <- p_bar[2, k]
		within_p_bar_k <- p_bar[1, k] : (p_bar[2, k] - 1)
		Item_1 <- Item_1 + log(diag_V_vec)[end_p_bar_k]
		Item_2 <- Item_2 + (p_vec[k] - 1) * log(sum(diag_V_vec[within_p_bar_k]))
		Item_3 <- Item_3 - log(diag_D_vec[end_p_bar_k])
		Item_4 <- Item_4 - (p_vec[k] - 1) * log(sum(diag_D_vec[within_p_bar_k]))
	}
	TwoNlogLambda4 <- Item_1 + Item_2 + Item_3 + Item_4
	logLambda4 <- (n / 2) * TwoNlogLambda4
	return(logLambda4)
}

COMPUTE_EMPIRICAL_TEST_STATISTICS <- function(n_vec, p_vec, mu_mat_0, mu_vec_test, Sigma_mat_0, Gamma_mat_0, COMPUTE_EMPIRICAL_LOG_LAMBDA_1, COMPUTE_EMPIRICAL_LOG_LAMBDA_2, COMPUTE_EMPIRICAL_LOG_LAMBDA_3, COMPUTE_EMPIRICAL_LOG_LAMBDA_4){

	### INPUT
	### n_vec: M by 1
	### p_vec: K by 1
	### mu_mat_0: M by p
	### mu_vec_test: p by 1
	### Sigma_mat_0: p by p
	### Gamma_mat_0: p by p
	### OUTPUT
	### logLambda1_truth: 1 by 1
	### logLambda1_est: 1 by 1
	### logLambda2_truth: 1 by 1
	### logLambda2_est: 1 by 1
	### logLambda3_truth: 1 by 1
	### logLambda3_est: 1 by 1
	### logLambda4_truth: 1 by 1
	### logLambda4_est: 1 by 1
	### G_2_est: 1 by 1
	### G_4_est: 1 by 1
	
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
	for(m in 1 : M){
		X_list[[m]] <- mvtnorm::rmvnorm(n = n_vec[m], mean = mu_mat_0[m, ], sigma = Sigma_mat_0)
		### n ^ (m) by p
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
	res_sig_est <- BEST_UNBIASED_ESTIMATOR(S_mat = S_mat_pool, p_vec = p_vec)
	Sig_A_mat_est <- res_sig_est$A_mat
	Sig_B_mat_est <- res_sig_est$B_mat
	Gamma_mat_est <- COMPUTE_GAMMA_MATRIX(A_mat = Sig_A_mat_est, B_mat = Sig_B_mat_est, p_vec = p_vec)
	### p by p
	V_list_truth <- V_list_est <- list()
	Y_mat_truth <- Y_mat_est <- matrix(0, nrow = M, ncol = p)
	### M by p
	Y_bar_vec_truth <- Y_bar_vec_est <- rep(0, p)
	### p by 1
	for(m in 1 : M){
		V_list_truth[[m]] <- Gamma_mat_0 %*% W_list[[m]] %*% t(Gamma_mat_0)
		### p by p
		V_list_est[[m]] <- Gamma_mat_est %*% W_list[[m]] %*% t(Gamma_mat_est)
		### p by p
		Y_mat_truth[m, ] <- sqrt(n_vec[m]) * Gamma_mat_0 %*% X_bar_mat[m, ]
		### p by 1
		Y_mat_est[m, ] <- sqrt(n_vec[m]) * Gamma_mat_est %*% X_bar_mat[m, ]
		### p by 1
		Y_bar_vec_truth <- Y_bar_vec_truth + sqrt(n_vec[m]) * Y_mat_truth[m, ] / n
		### p by 1
		Y_bar_vec_est <- Y_bar_vec_est + sqrt(n_vec[m]) * Y_mat_est[m, ] / n
		### p by 1
	}
	
	if(M == 1){
		nu_vec_test_truth <- sqrt(n) * drop(Gamma_mat_0 %*% mu_vec_test)
		### p by 1
		nu_vec_test_est <- sqrt(n) * drop(Gamma_mat_est %*% mu_vec_test)
		### p by 1
		
		H_mat_truth <- (Y_mat_truth[1, ] - nu_vec_test_truth) %*% t(Y_mat_truth[1, ] - nu_vec_test_truth)
		### p by 1
		H_mat_est <- (Y_mat_est[1, ] - nu_vec_test_est) %*% t(Y_mat_est[1, ] - nu_vec_test_est)
		### p by 1
	} else if (M > 1){
		H_mat_truth <- H_mat_est <- matrix(0, nrow = p, ncol = p)
		for(m in 1 : M){
			H_mat_truth <- H_mat_truth + (Y_mat_truth[m, ] - sqrt(n_vec[m]) * Y_bar_vec_truth) %*% t(Y_mat_truth[m, ] - sqrt(n_vec[m]) * Y_bar_vec_truth)
			### p by p
			H_mat_est <- H_mat_est + (Y_mat_est[m, ] - sqrt(n_vec[m]) * Y_bar_vec_est) %*% t(Y_mat_est[m, ] - sqrt(n_vec[m]) * Y_bar_vec_est)
			### p by p
		}
	}

	if(M == 1){

		log_Lambda_1_truth <- COMPUTE_EMPIRICAL_LOG_LAMBDA_1(n = n, p_vec = p_vec, V_mat = V_list_truth[[1]])
		log_Lambda_1_est <- COMPUTE_EMPIRICAL_LOG_LAMBDA_1(n = n, p_vec = p_vec, V_mat = V_list_est[[1]])
		
		log_Lambda_2_truth <- COMPUTE_EMPIRICAL_LOG_LAMBDA_2(n = n, p_vec = p_vec, V_mat = V_list_truth[[1]], H_mat = H_mat_truth)
		log_Lambda_2_est <- COMPUTE_EMPIRICAL_LOG_LAMBDA_2(n = n, p_vec = p_vec, V_mat = V_list_est[[1]], H_mat = H_mat_est)
		
		The_A_mat <- solve(Sig_A_mat_est)
		The_B_mat <- - solve(Sig_A_mat_est + Sig_B_mat_est %*% diag(p_vec)) %*% Sig_B_mat_est %*% solve(Sig_A_mat_est)
		Theta_mat_est <- BLOCK_HADAMARD_PRODUCT(A_mat = The_A_mat, B_mat = The_B_mat, p_vec = p_vec)
		G_2_est <- n * drop(t(X_bar_mat[1, ] - mu_vec_test) %*% Theta_mat_est %*% (X_bar_mat[1, ] - mu_vec_test))
	
		log_Lambda_3_truth <- log_Lambda_3_est <- log_Lambda_4_truth <- log_Lambda_4_est <- G_4_est <- NULL
	
	} else if (M > 1){
		log_Lambda_1_truth <- log_Lambda_1_est <- log_Lambda_2_truth <- log_Lambda_2_est <- G_2_truth <- G_2_est <- NULL
	
		log_Lambda_3_truth <- COMPUTE_EMPIRICAL_LOG_LAMBDA_3(n_vec = n_vec, p_vec = p_vec, V_list = V_list_truth)
		log_Lambda_3_est <- COMPUTE_EMPIRICAL_LOG_LAMBDA_3(n_vec = n_vec, p_vec = p_vec, V_list = V_list_est)
	
		log_Lambda_4_truth <- COMPUTE_EMPIRICAL_LOG_LAMBDA_4(n_vec = n_vec, p_vec = p_vec, V_list = V_list_truth, H_mat = H_mat_truth)
		log_Lambda_4_est <- COMPUTE_EMPIRICAL_LOG_LAMBDA_4(n_vec = n_vec, p_vec = p_vec, V_list = V_list_est, H_mat = H_mat_est)
		
		The_A_mat <- solve(Sig_A_mat_est)
		The_B_mat <- - solve(Sig_A_mat_est + Sig_B_mat_est %*% diag(p_vec)) %*% Sig_B_mat_est %*% solve(Sig_A_mat_est)
		Theta_mat_est <- BLOCK_HADAMARD_PRODUCT(A_mat = The_A_mat, B_mat = The_B_mat, p_vec = p_vec)
		G_4_est <- 0
		for (m in 1 : M){
			G_4_est <- G_4_est + n_vec[m] * drop(t(X_bar_mat[m, ] - X_bar_vec) %*% Theta_mat_est %*% (X_bar_mat[m, ] - X_bar_vec))
		}
	}

	return(c(
		log_Lambda_1_truth, log_Lambda_1_est, 
		log_Lambda_2_truth, log_Lambda_2_est, 
		log_Lambda_3_truth, log_Lambda_3_est, 
		log_Lambda_4_truth, log_Lambda_4_est, 
		G_2_est, G_4_est
	))
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
	
	n <- sum(n_vec)
	M <- length(n_vec)
	p <- sum(p_vec)
	K <- length(p_vec)
	f_vec <- n_vec / n
	### M by 1
	
	P_mat <- diag(p_vec)
	### K by K	
	Sig_D_mat_0 <- Sig_A_mat_0 + Sig_B_mat_0 %*% P_mat
	### K by K	
	
	C_p_mat <- matrix(0, 1, 1)
	for(k in 1 : K){
		C_p_mat <- Matrix::bdiag(C_p_mat, matrix(1 / p_vec[k], nrow = 1, ncol = p_vec[k]))
	}
	C_p_mat <- as.matrix(C_p_mat[- 1, - 1])
	### K by p
	
	if(M == 1){
		
		logLambda3_vec <- logLambda4B_vec <- logLambda4F_vec <- G4_vec <- NULL
		
		################################
		### calculate logLambda1_vec ###
		################################
		
		logLambda10_mat <- matrix(0, reps_max, p - 1)
		### reps_max by (p - 1)
		for(j in 1 : (p - 1)){
			logLambda10_mat[, j] <- log(rbeta(reps_max, (n - 1) / 2 - (p - j) / 2, (p - j) / 2))
		}
		logLambda10_vec <- (n / 2) * rowSums(logLambda10_mat)
		### reps_max by 1
		
		Y_k <- c()
		for(k in 1 : K){
			Y_k_j <- c()
			for(j in 2 : (p_vec[k] - 1)){
				Y_k_j_temp <- log(rbeta(reps_max, (n - 1) / 2, (j - 1) / (p_vec[k] - 1)))
				Y_k_j <- cbind(Y_k_j, Y_k_j_temp)
			}
			### reps_max by (p_vec[k] - 1)
			Y_k <- cbind(Y_k, Y_k_j)
			### reps_max by (p - 1)
		}
		logLambda1k_vec <- (n / 2) * rowSums(Y_k)
		### reps_max by 1
		
		logLambda1_vec <- logLambda10_vec + logLambda1k_vec
		### reps_max by 1
		
		mu_app <- (2 * K) / (n - 1) - p - (n - p - 3 / 2) * log(1 - p / (n - 1))
		sigma2_app <- - 2 * (log(1 - p / (n - 1)) + p / (n - 1))
		log_Lambda1_app_vec <- rnorm(reps_max, mean = mu_app, sd = sqrt(sigma2_app))
		### reps_max by 1
		
		################################
		### calculate logLambda2_vec ###
		################################
		
		Omega_mat <- (nu_mat_0[1, ] - nu_vec_test) %*% t(nu_mat_0[1, ] - nu_vec_test)
		### p by p
		diag_Omega_vec <- diag(diag(diag(Xi_mat_0) ^ (- 1 / 2)) %*% Omega_mat %*% diag(diag(Xi_mat_0) ^ (- 1 / 2)))
		### p by 1
		
		p_bar <- matrix(0, 2, K)
		for(k in 1 : K){
			p_bar[1, k] <- sum(p_vec[0 : (k - 1)]) + 1
			p_bar[2, k] <- sum(p_vec[1 : k])
		}
		
		logLambda20_mat <- matrix(0, reps_max, K) 
	    ### reps_max by K
		for(k in 1 : K){
			end_p_bar_k <- p_bar[2, k]
			### logLambda20_mat[, k] <- log(1 - rbeta(reps_max, (n - 1) / 2, 1 / 2, diag_Omega_vec[end_p_bar_k]))
			logLambda20_mat[, k] <- log(1 - rbeta(reps_max, 1 / 2, (n - 1) / 2, diag_Omega_vec[end_p_bar_k]))
		}
		logLambda20_vec <- (n / 2) * rowSums(logLambda20_mat)
		### reps_max by 1
		
		Y_k_mat <- matrix(0, reps_max, K)
		### reps_max by K
		for(k in 1 : K){
			within_p_bar_k <- p_bar[1, k] : (p_bar[2, k] - 1)
			### Y_k_mat[, k] <- (p_vec[k] - 1) * log(1 - rbeta(reps_max, (n - 1) * (p_vec[k] - 1) / 2, (p_vec[k] - 1) / 2, sum(diag_Omega_vec[within_p_bar_k])))
			Y_k_mat[, k] <- (p_vec[k] - 1) * log(1 - rbeta(reps_max, (p_vec[k] - 1) / 2, (n - 1) * (p_vec[k] - 1) / 2, sum(diag_Omega_vec[within_p_bar_k])))
		}
		logLambda2k_vec <- (n / 2) * rowSums(Y_k_mat)
		### reps_max by 1
		
		logLambda2B_vec <- logLambda20_vec + logLambda2k_vec
		### reps_max by 1
		
		logF_mat <- matrix(0, reps_max, K)
		### reps_max by K
		for(k in 1 : K){
			end_p_bar_k <- p_bar[2, k]
			within_p_bar_k <- p_bar[1, k] : (p_bar[2, k] - 1)
			logF_mat[, k] <- log1p(rf(reps_max, 1, n - 1, diag_Omega_vec[end_p_bar_k]) / (n - 1)) + (p_vec[k] - 1) * log1p(rf(reps_max, p_vec[k] - 1, (p_vec[k] - 1) * (n - 1), sum(diag_Omega_vec[within_p_bar_k])) / (n - 1))
		}
		logLambda2F_vec <- - (n / 2) * rowSums(logF_mat)
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
		
	} else if(M > 1){
	
		logLambda1_vec <- log_Lambda1_app_vec <- logLambda2B_vec <- logLambda2F_vec <- G2_vec <- NULL
		
		################################
		### calculate logLambda3_vec ###
		################################
		
		logLambda30_mat <- matrix(0, reps_max, K)
		### reps_max by K
		for(k in 1 : K){	
			logLambda30_mat_temp <- matrix(rep(n_vec / 2, reps_max), reps_max, M, byrow = TRUE) * (log(MCMCpack::rdirichlet(reps_max, (n_vec - 1) / 2))) 
			### reps_max by M
			logLambda30_mat[, k] <- rowSums(logLambda30_mat_temp)
			### reps_max by 1
		}
		logLambda30_vec <- rowSums(logLambda30_mat)
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
	
		################################
		### calculate logLambda4_vec ###
		################################
		
		A_Y_mat <- diag(M) - sqrt(f_vec) %*% t(sqrt(f_vec))
		### M by M
		M_Y_mat <- matrix(0, nrow = p, ncol = M)
		for(m in 1 : M){
			M_Y_mat[, m] <- nu_mat_0[m, ]
		}
		Omega_mat <- M_Y_mat %*% A_Y_mat %*% t(M_Y_mat)
		### p by p
		diag_Omega_vec <- diag(diag(diag(Xi_mat_0) ^ (- 1 / 2)) %*% Omega_mat %*% diag(diag(Xi_mat_0) ^ (- 1 / 2)))
		### p by 1
		
		p_bar <- matrix(0, 2, K)
		for(k in 1 : K){
			p_bar[1, k] <- sum(p_vec[0 : (k - 1)]) + 1
			p_bar[2, k] <- sum(p_vec[1 : k])
		}
		
		logLambda40_mat <- matrix(0, reps_max, K) 
		### reps_max by K
		for(k in 1 : K){
			end_p_bar_k <- p_bar[2, k]
			### logLambda40_mat[, k] <- log(rbeta(reps_max, (n - M) / 2, (M - 1) / 2))
			logLambda40_mat[, k] <- log(1 - rbeta(reps_max, (M - 1) / 2, (n - M) / 2, diag_Omega_vec[end_p_bar_k]))
		}
		logLambda40_vec <- (n / 2) * rowSums(logLambda40_mat)
		### reps_max by 1 
	
		Y_k_mat <- matrix(0, reps_max, K)
		### reps_max by K 
		for(k in seq(K)){
			within_p_bar_k <- p_bar[1, k] : (p_bar[2, k] - 1)
			### Y_k_mat[, k] <- (p_vec[k] - 1) * log(rbeta(reps_max, (n - M) * (p_vec[k] - 1) / 2, (M - 1) * (p_vec[k] - 1) / 2))
			Y_k_mat[, k] <- (p_vec[k] - 1) * log(1 - rbeta(reps_max, (M - 1) * (p_vec[k] - 1) / 2, (n - M) * (p_vec[k] - 1) / 2, sum(diag_Omega_vec[within_p_bar_k])))
		}
		logLambda4k_vec <- (n / 2) * rowSums(Y_k_mat)
		### reps_max by 1 
		
		logLambda4B_vec <- logLambda40_vec + logLambda4k_vec
		### reps_max by 1
		
		logF_mat <- matrix(0, reps_max, K)
		### reps_max by K
		for(k in 1 : K){
			end_p_bar_k <- p_bar[2, k]
			within_p_bar_k <- p_bar[1, k] : (p_bar[2, k] - 1)
			logF_mat[, k] <- log1p((M - 1) * rf(reps_max, M - 1, n - M, diag_Omega_vec[end_p_bar_k]) / (n - M)) + (p_vec[k] - 1) * log1p((M - 1) * rf(reps_max, (p_vec[k] - 1) * (M - 1), (p_vec[k] - 1) * (n - M), sum(diag_Omega_vec[within_p_bar_k])) / (n - M))
		}
		logLambda4F_vec <- - (n / 2) * rowSums(logF_mat)
		### reps_max by 1
		
		########################
		### calculate G4_vec ###
		########################
		
		G4_vec <- rep(0, reps_max)
		
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
		
			G4_vec <- G4_vec + (M - 1) * (p_vec[k] - 1) * rf(reps_max, df1 = (M - 1) * (p_vec[k] - 1), df2 = (p_vec[k] - 1) * (n - M), ncp = delta_k)
		}
		
		### Betz (1987) uses F-variate to approximate T0^2
		### (1) para_l <- n - M - p - 1
		### (2) para_b <- (para_l + para_q) * (para_l + p)/ ((para_l - 2) * (para_l + 1))
		### (3) df_1 <- p * para_q
		### (4) df_2 <- 4 + (p * para_q + 2) / (para_b - 1)
		### (5) para_a <- p * para_q * (df_2 - 2) / (para_l * df_2)
			
		Sigma_Y_mat <- Sig_A_mat_0 %*% solve(diag(p_vec)) + Sig_B_mat_0
		### K by K
		Omega_Y_mat <- matrix(0, nrow = K, ncol = K)
		### K by 1
		mu_bar_vec <- rep(0, p)
		for(m in 1 : M){
			mu_bar_vec <- mu_bar_vec + n_vec[m] * mu_mat_0[m, ]
		}
		mu_bar_vec <- mu_bar_vec / n
		
		for(m in 1 : M){
			Omega_Y_mat <- Omega_Y_mat + n_vec[m] * C_p_mat %*% (mu_mat_0[m, ] - mu_bar_vec) %*% t(mu_mat_0[m, ] - mu_bar_vec)  %*% t(C_p_mat) 
		}
		
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
		
		G4_vec <- G4_vec + (n - M) * para_g * para_a * rf(reps_max, df1 = df_1, df2 = df_2, ncp = 0)
	}
	
	return(list(
		logLambda1_vec = logLambda1_vec,
   log_Lambda1_app_vec = log_Lambda1_app_vec,		
	   logLambda2B_vec = logLambda2B_vec, 
	   logLambda2F_vec = logLambda2F_vec,
		logLambda3_vec = logLambda3_vec, 
	   logLambda4B_vec = logLambda4B_vec,
	   logLambda4F_vec = logLambda4F_vec, 
			    G2_vec = G2_vec, 
				G4_vec = G4_vec
	))
}

##############################
### Simulation Study Setup ###
##############################

INPUT_ADDRESS <- OUTPUT_ADDRESS <- "..."

SET_NO <- 1

SET_UP <- matrix(c(
	1,  50,   0,   0, 1e5, 1e5, 1,   1, ### study 1,  p = 25
	1,  50,   0,   0, 1e5, 1e5, 1, 1.9, ### study 1,  p = 45
	1, 100,   0,   0, 1e5, 1e5, 1,   3, ### study 1,  p = 75
	1, 100,   0,   0, 1e5, 1e5, 1, 3.9, ### study 1,  p = 95
	1,  50,   0,   0, 1e5, 1e5, 1,   8, ### study 2,  p = 200 (43 mins)
	1,  50,   0,   0, 1e5, 1e5, 1,  16, ### study 2,  p = 400
	1, 100,   0,   0, 1e5, 1e5, 1,   8, ### study 2,  p = 200
	1, 100,   0,   0, 1e5, 1e5, 1,  16, ### study 2,  p = 400 (4 hours)			
	3,  50,  50,  50, 1e5, 1e5, 1,   8, ### study 12, p = 200
	3,  50,  50,  50, 1e5, 1e5, 1,  16, ### study 12, p = 400 (11 hours)
	3,  50,  75, 100, 1e5, 1e5, 1,   8, ### study 12, p = 200
	3,  50,  75, 100, 1e5, 1e5, 1,  16  ### study 12, p = 400
	), 
	nrow = 12, ncol = 8, byrow = TRUE)
### M = 1, 3 
### sample size(s) no = 1, 2, 3
### MC replicate no 1 = 1e5
### MC replicate no 2 = 1e5
### H24 holds: 0; K24 holds: 1
### scale_p_vec

M <- SET_UP[SET_NO, 1]
n_vec <- SET_UP[SET_NO, 2 : 4]
n_vec <- n_vec[n_vec != 0]
### M by 1
n <- sum(n_vec)
### 1 by 1
reps_emp_max <- SET_UP[SET_NO, 5]
reps_the_max <- SET_UP[SET_NO, 6]

### create the population mean and UB covariance matrix ###
scale_p_vec <- SET_UP[SET_NO, 8]
p_vec <- c(floor(3 * scale_p_vec), floor(4 * scale_p_vec), floor(5 * scale_p_vec), floor(6 * scale_p_vec), floor(7 * scale_p_vec))
### K by 1
K <- length(p_vec)
p <- sum(p_vec)

if(SET_UP[SET_NO, 7] == 0){
	### M = 1, H1K1, mu_1 = 1_vec;        H2K2, mu_1 = 1_vec = mu_0;
	### M > 1, H3K3, mu_1 = 1_vec = mu_M; H4K4, mu_1 = 1_vec = mu_M;
	mu_mat_0 <- matrix(1, nrow = M, ncol = p)
	### M by p
	mu_vec_test <- mu_mat_0[1, ]
	### p by 1
} else if (SET_UP[SET_NO, 7] == 1){
	### M = 1, H1K1, mu_1 = 1_vec;        H2K2, mu_1 = 1_vec != 2_vec = mu_0;
	### M > 1, H3K3, mu_1 != ... != mu_M; H4K4, mu_1 != ... != mu_M;
	mu_mat_0 <- matrix(rep(seq(M), times = p), nrow = M, ncol = p, byrow = FALSE)
	### M by p
	mu_vec_test <- mu_mat_0[1, ] + 1
	### p by 1
}

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
Sig_D_mat_0 <- Sig_A_mat_0 + Sig_B_mat_0 %*% diag(p_vec)
### K by K
Sigma_mat_0 <- BLOCK_HADAMARD_PRODUCT(A_mat = Sig_A_mat_0, B_mat = Sig_B_mat_0, p_vec = p_vec)
### p by p
Gamma_mat_0 <- COMPUTE_GAMMA_MATRIX(A_mat = Sig_A_mat_0, B_mat = Sig_B_mat_0, p_vec = p_vec)
### p by p
Xi_mat_0 <- diag(diag(Gamma_mat_0 %*% Sigma_mat_0 %*% t(Gamma_mat_0)))
### p by p
nu_mat_0 <- matrix(0, nrow = M, ncol = p)
### M by p
for(m in 1 : M){
	nu_mat_0[m, ] <- sqrt(n_vec[m]) * Gamma_mat_0 %*% mu_mat_0[m, ]
	### p by 1
}
if(!is.null(mu_vec_test)){
	nu_vec_test <- sqrt(n) * drop(Gamma_mat_0 %*% mu_vec_test)
	### p by 1
} else {
	nu_vec_test <- NULL
}

quantile_vec <- c(0.01, 0.05, 0.10, 0.50, 0.90, 0.95, 0.99)

res_the <- COMPUTE_THEORETICAL_DISTRIBUTIONS(n_vec = n_vec, p_vec = p_vec, reps_max = reps_the_max, nu_mat_0 = nu_mat_0, nu_vec_test = nu_vec_test, Xi_mat_0 = Xi_mat_0, mu_mat_0 = mu_mat_0, mu_vec_test = mu_vec_test, Sig_A_mat_0 = Sig_A_mat_0, Sig_B_mat_0 = Sig_B_mat_0, BLOCK_HADAMARD_PRODUCT = BLOCK_HADAMARD_PRODUCT)

res_emp <- pbapply::pbreplicate(
	   n = reps_emp_max, 
	expr = COMPUTE_EMPIRICAL_TEST_STATISTICS(
		n_vec = n_vec, 
		p_vec = p_vec, 
	 mu_mat_0 = mu_mat_0, 
  mu_vec_test = mu_vec_test, 
  Sigma_mat_0 = Sigma_mat_0, 
  Gamma_mat_0 = Gamma_mat_0, 
  COMPUTE_EMPIRICAL_LOG_LAMBDA_1 = COMPUTE_EMPIRICAL_LOG_LAMBDA_1, 
  COMPUTE_EMPIRICAL_LOG_LAMBDA_2 = COMPUTE_EMPIRICAL_LOG_LAMBDA_2, 
  COMPUTE_EMPIRICAL_LOG_LAMBDA_3 = COMPUTE_EMPIRICAL_LOG_LAMBDA_3, 
  COMPUTE_EMPIRICAL_LOG_LAMBDA_4 = COMPUTE_EMPIRICAL_LOG_LAMBDA_4))

if(M == 1){
	
	W1_the <- - res_the$logLambda1_vec
	W1_app_the <- - res_the$log_Lambda1_app_vec / (2 / n)
	W1_emp_truth <- - res_emp[1, ]
	W1_emp_est <- - res_emp[2, ]
	
	W2B_the <- - res_the$logLambda2B_vec
	W2F_the <- - res_the$logLambda2F_vec
	W2_emp_truth <- - res_emp[3, ]
	W2_emp_est <- - res_emp[4, ]
	
	G2_the <- res_the$G2_vec
	G2_emp_est <- res_emp[5, ]
	
	W1_mat <- rbind(
		quantile(W1_the, probs = quantile_vec, na.rm = TRUE),
		quantile(W1_app_the, probs = quantile_vec, na.rm = TRUE),
		quantile(W1_emp_truth, probs = quantile_vec, na.rm = TRUE),
		quantile(W1_emp_est, probs = quantile_vec, na.rm = TRUE))
	W2_mat <- rbind(
		quantile(W2B_the, probs = quantile_vec),
		quantile(W2F_the, probs = quantile_vec),
		quantile(W2_emp_truth, probs = quantile_vec),
		quantile(W2_emp_est, probs = quantile_vec))
	W3_mat <- rbind(
		quantile(G2_the, probs = quantile_vec),
		quantile(G2_emp_est, probs = quantile_vec)
	)	
	
	rownames(W1_mat) <- c("theoretical", "normal_app", "empirical_true", "empirical_estimated")
	
	rownames(W2_mat) <- c("theoretical_beta", "theoretical_F", "empirical_true", "empirical_estimated")
	
	rownames(W3_mat) <- c("theoretical", "empirical_estimated")
	
	print(W1_mat)
	
	print(W2_mat)
	
	print(W3_mat)
	
	P_1_vec <- c(W1_the, W1_app_the, W1_emp_truth, W1_emp_est)
	Den_1_vec <- c(
				 rep("Theoretical", length(W1_the)), 
				 rep("Normal-Approximation", length(W1_app_the)),
				 rep("Empirical-True Gamma", length(W1_emp_truth)), 
				 rep("Empirical-Estd Gamma", length(W1_emp_est)))
	DATA_PLOT_1 <- data.frame(x = P_1_vec, approaches = Den_1_vec)
	
	P_2_vec <- c(W2B_the, W2F_the, W2_emp_truth, W2_emp_est)
	Den_2_vec <- c(
				 rep("Theoretical-Beta", length(W2B_the)), 
				 rep("Theoretical-F", length(W2F_the)), 
				 rep("Empirical-True Gamma", length(W2_emp_truth)), 
				 rep("Empirical-Estd Gamma", length(W2_emp_est)))
	DATA_PLOT_2 <- data.frame(x = P_2_vec, approaches = Den_2_vec)
	
	P_3_vec <- c(G2_the, G2_emp_est)
	Den_3_vec <- c(
				 rep("Theoretical", length(G2_the)), 
				 rep("Empirical", length(G2_emp_est)))
	DATA_PLOT_3 <- data.frame(x = P_3_vec, approaches = Den_3_vec)
	
} else if(M > 1){

	W3_the <- - res_the$logLambda3_vec
	W3_emp_truth <- - res_emp[1, ]
	W3_emp_est <- - res_emp[2, ]
	
	W4B_the <- - res_the$logLambda4B_vec
	W4F_the <- - res_the$logLambda4F_vec
	W4_emp_truth <- - res_emp[3, ]
	W4_emp_est <- - res_emp[4, ]
	
	G4_the <- res_the$G4_vec
	G4_emp_est <- res_emp[5, ]
	
	W3_mat <- rbind(
		quantile(W3_the, probs = quantile_vec),
		quantile(W3_emp_truth, probs = quantile_vec),
		quantile(W3_emp_est, probs = quantile_vec))
	W4_mat <- rbind(
		quantile(W4B_the, probs = quantile_vec),
		quantile(W4F_the, probs = quantile_vec),
		quantile(W4_emp_truth, probs = quantile_vec),
		quantile(W4_emp_est, probs = quantile_vec))
	W5_mat <- rbind(
		quantile(G4_the, probs = quantile_vec),
		quantile(G4_emp_est, probs = quantile_vec)
	)
	
	
	rownames(W3_mat) <- c("theoretical", "empirical_true", "empirical_estimated")
	
	rownames(W4_mat) <- c("theoretical_beta", "theoretical_F", "empirical_true", "empirical_estimated")
	
	rownames(W5_mat) <- c("theoretical", "empirical_estimated")
	
	print(W3_mat)
	
	print(W4_mat)
	
	print(W5_mat)
	
	P_1_vec <- c(W3_the, W3_emp_truth, W3_emp_est)
	Den_1_vec <- c(
				 rep("Theoretical", length(W3_the)), 
				 rep("Empirical-True Gamma", length(W3_emp_truth)), 
				 rep("Empirical-Estd Gamma", length(W3_emp_est)))
	DATA_PLOT_1 <- data.frame(x = P_1_vec, approaches = Den_1_vec)
	
	P_2_vec <- c(W4B_the, W4F_the, W4_emp_truth, W4_emp_est)
	Den_2_vec <- c(
				 rep("Theoretical-Beta", length(W4B_the)), 
				 rep("Theoretical-F", length(W4F_the)), 
				 rep("Empirical-True Gamma", length(W4_emp_truth)), 
				 rep("Empirical-Estd Gamma", length(W4_emp_est)))
	DATA_PLOT_2 <- data.frame(x = P_2_vec, approaches = Den_2_vec) 
	
	P_3_vec <- c(G4_the, G4_emp_est)
	Den_3_vec <- c(
				 rep("Theoretical", length(G4_the)), 
				 rep("Empirical", length(G4_emp_est)))
	DATA_PLOT_3 <- data.frame(x = P_3_vec, approaches = Den_3_vec)			 
}

ggplot(data = DATA_PLOT_1, mapping = aes(x = x, color = approaches)) +
	geom_density(linewidth = 1, alpha = 0.1) +
	labs(x = expression(- log(Lambda[1]))) + 
	scale_color_discrete(limits = c("Theoretical", "Normal-App", "Empirical-True Gamma", "Empirical-Estd Gamma"))

ggplot(data = DATA_PLOT_2, mapping = aes(x = x, color = approaches)) +
	geom_density(linewidth = 1, alpha = 0.1) +
	labs(x = expression(- log(Lambda[2]))) + 
	scale_color_discrete(limits = c("Theoretical-Beta", "Theoretical-F", "Empirical-True Gamma", "Empirical-Estd Gamma"))
	
ggplot(data = DATA_PLOT_3, mapping = aes(x = x, color = approaches)) +
	geom_density(linewidth = 1, alpha = 0.1) +
	labs(x = expression(G[2])) + 
	scale_color_discrete(limits = c("Theoretical", "Empirical"))
	
	
save.image(paste(OUTPUT_ADDRESS, paste("S12_No", SET_NO, "Pops", M, "Sizes", paste(n_vec, collapse = "_"), "Dim", p, "UB.RData", sep = "_"), sep = "/"))	




