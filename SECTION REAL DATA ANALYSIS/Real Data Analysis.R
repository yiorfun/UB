######################################################################
### REAL DATA STUDY 				   							   ###
######################################################################

############################
### Loading the packages ###
############################

REQUIRED_PACKAGES <- c(
	"gplots",		
	### gplots::heatmap.2(), create a simplified heatmap
	"reshape2",
	### reshape2::melt(), melt a matrix to a data frame
	"pals", 
	### pals::coolwarm(), create a colormap 
	"ggplot2", 
	### ggplot2::ggplot(), create a complex heatmap
	"missForest",
	### missForest::missForest(), impute the missing values
	"dplyr",
	### dplyr::%>%: loads the infix operator
	"Matrix", 
	### Matrix::bdiag(), builds a block diagonal matrix given several building block matrices
	"Compositional",
	### Compositional::helm(), creates the Helmert sub-matrix
	"MCMCpack"
	### MCMCpack::rdirichlet(), generates random deviates from the Dirichlet distribution
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

COMPUTE_EMPIRICAL_TEST_STATISTICS_SAMPLE <- function(n_vec, p_vec, X_bar_mat, mu_vec_test, S_list, COMPUTE_EMPIRICAL_LOG_LAMBDA_1, COMPUTE_EMPIRICAL_LOG_LAMBDA_2, COMPUTE_EMPIRICAL_LOG_LAMBDA_3, COMPUTE_EMPIRICAL_LOG_LAMBDA_4, BEST_UNBIASED_ESTIMATOR, BLOCK_HADAMARD_PRODUCT, COMPUTE_GAMMA_MATRIX){
	
	##### SAMPLE VERSION does not include truth competitors
	##### for both covariance and mean tests
	### INPUT
	### n_vec: M by 1
	### p_vec: K by 1
	### X_bar_mat: M by p
	### mu_vec_test: p by 1
	### S_list: M by p by p
	### OUTPUT
	### logLambda1_est: 1 by 1
	### logLambda2_est: 1 by 1
	### logLambda3_est: 1 by 1
	### logLambda4_est: 1 by 1
	### G_2_est: 1 by 1
	### G_4_est: 1 by 1
	
	M <- length(n_vec)
	n <- sum(n_vec)
	p <- ncol(X_bar_mat)

	X_bar_vec <- rep(0, p)
	### p by 1
	S_mat <- matrix(0, nrow = p, ncol = p)
	### p by p
	for(m in 1 : M){
		X_bar_vec <- X_bar_vec + n_vec[m] * X_bar_mat[m, ]
		### p by 1
		S_mat <- S_mat + S_list[[m]] * (n_vec[m] - 1)
		### p by p
	}
	X_bar_vec <- X_bar_vec / n 
	### p by 1
	S_mat_pool <- S_mat / (n - M)
	### p by p
	
	res_sig_est <- BEST_UNBIASED_ESTIMATOR(
		S_mat = S_mat_pool, 
		p_vec = p_vec)
	Sig_A_mat_est <- res_sig_est$A_mat
	### K by K
	Sig_B_mat_est <- res_sig_est$B_mat
	### K by K
	Gamma_mat_est <- COMPUTE_GAMMA_MATRIX(
		A_mat = Sig_A_mat_est, 
		B_mat = Sig_B_mat_est, 
		p_vec = p_vec)
	### p by p
	
	The_A_mat_est <- solve(Sig_A_mat_est)
	### K by K
	The_B_mat_est <- - solve(Sig_A_mat_est + Sig_B_mat_est %*% diag(p_vec)) %*% Sig_B_mat_est %*% solve(Sig_A_mat_est)
	### K by K
	Theta_mat_est <- BLOCK_HADAMARD_PRODUCT(
		A_mat = The_A_mat_est, 
		B_mat = The_B_mat_est, 
		p_vec = p_vec)
	### p by p
	
	V_list_est <- list()
	Y_mat_est <- matrix(0, nrow = M, ncol = p)
	### M by p
	Y_bar_vec_est <- rep(0, p)
	### p by 1
	for(m in 1 : M){
		V_list_est[[m]] <- Gamma_mat_est %*% (S_list[[m]] * (n_vec[m] - 1)) %*% t(Gamma_mat_est)
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

		log_Lambda_1_est <- COMPUTE_EMPIRICAL_LOG_LAMBDA_1(
			n = n, 
		p_vec = p_vec, 
		V_mat = V_list_est[[1]])
		
		log_Lambda_2_est <- COMPUTE_EMPIRICAL_LOG_LAMBDA_2(
			n = n, 
		p_vec = p_vec, 
		V_mat = V_list_est[[1]], 
		H_mat = H_mat_est)
		
		G_2_est <- n * drop(t(X_bar_mat[1, ] - mu_vec_test) %*% Theta_mat_est %*% (X_bar_mat[1, ] - mu_vec_test))
	
		log_Lambda_3_est <- log_Lambda_4_est <- G_4_est <- NULL
	
	} else if (M > 1){
		log_Lambda_1_est <- log_Lambda_2_est <- G_2_est <- NULL
	
		log_Lambda_3_est <- COMPUTE_EMPIRICAL_LOG_LAMBDA_3(
			n_vec = n_vec, 
			p_vec = p_vec, 
		   V_list = V_list_est)
	
		log_Lambda_4_est <- COMPUTE_EMPIRICAL_LOG_LAMBDA_4(
			n_vec = n_vec, 
			p_vec = p_vec, 
		   V_list = V_list_est, 
		    H_mat = H_mat_est)
		
		G_4_est <- 0
		for (m in 1 : M){
			G_4_est <- G_4_est + n_vec[m] * drop(t(X_bar_mat[m, ] - X_bar_vec) %*% Theta_mat_est %*% (X_bar_mat[m, ] - X_bar_vec))
		}
	}

	return(c(
		log_Lambda_1_est, 
		log_Lambda_2_est, 
		log_Lambda_3_est, 
		log_Lambda_4_est, 
		G_2_est, 
		G_4_est
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
	
	p_bar <- matrix(0, 2, K)
	for(k in 1 : K){
		p_bar[1, k] <- sum(p_vec[0 : (k - 1)]) + 1
		p_bar[2, k] <- sum(p_vec[1 : k])
	}
	
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
		
		### mu_app <- (2 * K) / (n - 1) - p - (n - p - 3 / 2) * log(1 - p / (n - 1))
		### sigma2_app <- - 2 * (log(1 - p / (n - 1)) + p / (n - 1))
		### log_Lambda1_app_vec <- rnorm(reps_max, mean = mu_app, sd = sqrt(sigma2_app))
		### reps_max by 1
		
		################################
		### calculate logLambda2_vec ###
		################################
		
		Omega_mat <- (nu_mat_0[1, ] - nu_vec_test) %*% t(nu_mat_0[1, ] - nu_vec_test)
		### p by p
		diag_Omega_vec <- diag(diag(diag(Xi_mat_0) ^ (- 1 / 2)) %*% Omega_mat %*% diag(diag(Xi_mat_0) ^ (- 1 / 2)))
		### p by 1
		
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
	   logLambda2B_vec = logLambda2B_vec, 
	   logLambda2F_vec = logLambda2F_vec,
		logLambda3_vec = logLambda3_vec, 
	   logLambda4B_vec = logLambda4B_vec,
	   logLambda4F_vec = logLambda4F_vec, 
			    G2_vec = G2_vec, 
				G4_vec = G4_vec
	))
}

COMPUTE_P_VALUES <- function(n_vec, p_vec, X_bar_mat, mu_vec_test, reps_the_max, S_list, sig_level, COMPUTE_THEORETICAL_DISTRIBUTIONS, COMPUTE_GAMMA_MATRIX, COMPUTE_EMPIRICAL_TEST_STATISTICS_SAMPLE, BLOCK_HADAMARD_PRODUCT, COMPUTE_EMPIRICAL_LOG_LAMBDA_1, COMPUTE_EMPIRICAL_LOG_LAMBDA_2, COMPUTE_EMPIRICAL_LOG_LAMBDA_3, COMPUTE_EMPIRICAL_LOG_LAMBDA_4){
	
	### INPUT
	### n_vec: M by 1
	### p_vec: K by 1
	### X_bar_mat: M by p
	### mu_vec_test: p by 1
	### reps_the_max: 1 by 1
	### S_list: M by p by p
	
	M <- length(n_vec)
	n <- sum(n_vec)
	K <- length(p_vec)
	p <- sum(p_vec)
	P_mat <- diag(p_vec)
	### K by K
	
	X_bar_vec <- rep(0, p)
	### p by 1
	S_mat <- matrix(0, nrow = p, ncol = p)
	### p by p
	for(m in 1 : M){
		X_bar_vec <- X_bar_vec + n_vec[m] * X_bar_mat[m, ]
		### p by 1
		S_mat <- S_mat + S_list[[m]] * (n_vec[m] - 1)
		### p by p
	}
	X_bar_vec <- X_bar_vec / n 
	### p by 1
	S_mat_pool <- S_mat / (n - M)
	### p by p
	
	res_sig_est <- BEST_UNBIASED_ESTIMATOR(
		S_mat = S_mat_pool, 
		p_vec = p_vec)
	Sig_A_mat_est <- res_sig_est$A_mat
	### K by K
	Sig_B_mat_est <- res_sig_est$B_mat
	### K by K
	Sigma_mat_est <- BLOCK_HADAMARD_PRODUCT(
		A_mat = Sig_A_mat_est, 
		B_mat = Sig_B_mat_est, 
		p_vec = p_vec)
	### p by p
	
	Gamma_mat_est <- COMPUTE_GAMMA_MATRIX(
		A_mat = Sig_A_mat_est, 
		B_mat = Sig_B_mat_est, 
		p_vec = p_vec)
	### p by p
	
	Xi_mat_est <- diag(diag(Gamma_mat_est %*% Sigma_mat_est %*% t(Gamma_mat_est)))
	### p by p
	
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
				      Xi_mat_0 = Xi_mat_est, 
					  mu_mat_0 = mu_mat_0_the, 
				   mu_vec_test = mu_vec_test_the, 
				   Sig_A_mat_0 = Sig_A_mat_est, 
				   Sig_B_mat_0 = Sig_B_mat_est, 
		BLOCK_HADAMARD_PRODUCT = BLOCK_HADAMARD_PRODUCT)
	
	res_emp <- COMPUTE_EMPIRICAL_TEST_STATISTICS_SAMPLE(
							 n_vec = n_vec, 
						     p_vec = p_vec, 
						 X_bar_mat = X_bar_mat, 
					   mu_vec_test = mu_vec_test, 
						    S_list = S_list, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_1 = COMPUTE_EMPIRICAL_LOG_LAMBDA_1, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_2 = COMPUTE_EMPIRICAL_LOG_LAMBDA_2, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_3 = COMPUTE_EMPIRICAL_LOG_LAMBDA_3, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_4 = COMPUTE_EMPIRICAL_LOG_LAMBDA_4, 
		   BEST_UNBIASED_ESTIMATOR = BEST_UNBIASED_ESTIMATOR, 
			BLOCK_HADAMARD_PRODUCT = BLOCK_HADAMARD_PRODUCT, 
			  COMPUTE_GAMMA_MATRIX = COMPUTE_GAMMA_MATRIX)
	
	if(M == 1){
		W1_the <- - res_the$logLambda1_vec
		W2B_the <- - res_the$logLambda2B_vec
		W2F_the <- - res_the$logLambda2F_vec
		G2_the <- res_the$G2_vec

		Wodd_emp_est <- - res_emp[1]
		Weve_emp_est <- - res_emp[2]
		G_emp_est <- res_emp[3]
		
		W_alpha <- quantile(x = W1_the, probs = 1 - sig_level, na.rm = TRUE)
		WB_alpha <- quantile(x = W2B_the, probs = 1 - sig_level)
		WF_alpha <- quantile(x = W2F_the, probs = 1 - sig_level)
		G_alpha <- quantile(x = G2_the, probs = 1 - sig_level)
		
		W_rej <- 1 * (Wodd_emp_est >= W_alpha)
		WB_rej <- 1 * (Weve_emp_est >= WB_alpha)
		WF_rej <- 1 * (Weve_emp_est >= WF_alpha)
		G_rej <- 1 * (G_emp_est >= G_alpha)
		
		W_p <- mean(1 * (Wodd_emp_est <= W1_the))
		WB_p <- mean(1 * (Weve_emp_est <= W2B_the))
		WF_p <- mean(1 * (Weve_emp_est <= W2F_the))
		G_p <- mean(1 * (G_emp_est <= G2_the))
	
	} else if(M > 1){
		W3_the <- - res_the$logLambda3_vec
		W4B_the <- - res_the$logLambda4B_vec
		W4F_the <- - res_the$logLambda4F_vec
		G4_the <- res_the$G4_vec
		
		Wodd_emp_est <- - res_emp[1]
		Weve_emp_est <- - res_emp[2]
		G_emp_est <- res_emp[3]
		
		W_alpha <- quantile(x = W3_the, probs = 1 - sig_level)
		WB_alpha <- quantile(x = W4B_the, probs = 1 - sig_level)
		WF_alpha <- quantile(x = W4F_the, probs = 1 - sig_level)
		G_alpha <- quantile(x = G4_the, probs = 1 - sig_level)
		
		W_rej <- 1 * (Wodd_emp_est >= W_alpha)
		WB_rej <- 1 * (Weve_emp_est >= WB_alpha)
		WF_rej <- 1 * (Weve_emp_est >= WF_alpha)
		G_rej <- 1 * (G_emp_est >= G_alpha)
		
		W_p <- mean(1 * (Wodd_emp_est <= W3_the))
		WB_p <- mean(1 * (Weve_emp_est <= W4B_the))
		WF_p <- mean(1 * (Weve_emp_est <= W4F_the))
		G_p <- mean(1 * (G_emp_est <= G4_the))
	}
	
	res_mat <- rbind(
		c(Wodd_emp_est, Weve_emp_est, Weve_emp_est, G_emp_est), 
		c(W_alpha, WB_alpha, WF_alpha, G_alpha), 
		c(W_rej, WB_rej, WF_rej, G_rej), 
		c(W_p, WB_p, WF_p, G_p)
	) 
	### 4 by 4
	colnames(res_mat) <- c("Lambda13", "Lambda24B", "Lambda24F", "G")
	rownames(res_mat) <- c("statistics", "cutpoint", "rejection", "p_value")
	
	return(res_mat)
}

ESTIMATE_FDP <- function(est_method, Z_vec, v_vec, Sigma_mat, t_threshold_vec, reg_method = "L1", eps = .05, gama, kappa_0, plot_method = "-log"){
	
###################################################################
### this function is modified based on the original R package   ###
### "pfa" at https://CRAN.R-project.org/package=pfa, with 		###
### maintainer Tracy Ke <zke@galton.uchicago.edu> and reference ###
### Fan, Han and Gu (2012) JASA paper 							###
###################################################################
  
	### Z_vec: p by 1 test statistics
	###        for "UB", it follows t-distribution with df of vk
	###        for "general", it follows Z-distribution
	### v_vec: p by 1 degrees of freedom parameter vector
	### Sigma_mat: p by p covariance matrix for Z_vec
	###		   for "UB", it is correlation matrix used UB formula
	###        for "general", it is the estimated covariance matrix
	### t_threshold_vec: candidate threshold values 
	### reg_method: methods for estimating unobserved random vector w:
	###				"L1", "L2", "huber"
    ### eps: number determining kappa_0
	### gama: a parameter determining the estimate of p0 
	### kappa_0: the predetermined number of selected principal components
	### plot_method: "-log", "linear", "log", and NULL
    ### est_method: estimating methods: "UB", "general"
  
	Z_vec <- as.vector(Z_vec)
	### p by 1
	kappa_max <- p <- length(Z_vec)
	### 1 by 1
	Sigma_mat <- as.matrix(Sigma_mat)
	### p by p 
	
    ### standardize the data ###
	if(est_method == "UB"){
		### Z_vec is already standardized
		Z_vec <- Z_vec
		Sigma_mat <- Sigma_mat
	} else if (est_method == "general"){
		Z_vec <- Z_vec / sqrt(diag(Sigma_mat))
		Sigma_mat <- diag(1 / sqrt(diag(Sigma_mat))) %*% Sigma_mat %*% diag(1 / sqrt(diag(Sigma_mat)))
	}

	### principal components analysis process ### 
	pca <- svd(Sigma_mat, nu = 0, nv = kappa_max)
	lambda <- pca$d
	eigvec <- pca$v
    
    ### determine the factor loadings ###
	if (missing(kappa_0)) {
      kappa_0 <- 1
      while(kappa_0 < kappa_max & sqrt(sum(lambda[(kappa_0 + 1) : length(lambda)] ^ 2)) >= eps * sum(lambda)) 
         kappa_0 <- kappa_0 + 1 
	}    
	sqrt_lambda <- as.matrix(sqrt(lambda[1 : kappa_0]))
	b <- as.matrix(eigvec[, 1 : kappa_0])
    for (i in 1 : kappa_0)  {
		b[,i] <- b[,i] * sqrt_lambda[i]  # factor loadings
    }

    ### estimate the factors, with 5% largest |Z_vec| eliminated ###
	if (reg_method == "L1") {
		### L_1 regression (no intercept)
		W.hat <- quantreg::rq(Z_vec ~ b - 1, 0.5)$coef  
		### perform quantile regression
		### W.hat <- W.hat[2:(kappa_0+1)] 
	} else if (reg_method == "L2"){
		### L_2 regression (no intercept) 
		### temp<-sort(abs(Z_vec),decreasing=TRUE,index.return=TRUE)
		### len=round(length(Z_vec)*0.05)
		### Ztemp<-temp$x
		### btemp<-as.matrix(b[temp$ix,])
		### Ztemp<-Ztemp[(len+1):length(Z_vec)]
		### btemp<-btemp[(len+1):length(Z_vec),]
		### W.hat<-lm(Ztemp ~ btemp - 1)$coef
		Zperm <- Z_vec[order(abs(Z_vec))]
		Lperm <- as.matrix(b[order(abs(Z_vec)), ])
		Z.reduce <- Zperm[1 : (p * 0.95)]
		L.reduce <- as.matrix(Lperm[1 : (p * 0.95), ]) 
		W.hat <- lsfit(x = L.reduce, y = Z.reduce, intercept = F)$coef
	} else if (reg_method == "huber") {
		### robust/huber regression
		W.hat <- rlm(Z_vec ~ b, 0.5)$coef	  
	}

	rs <- rowSums(b ^ 2)
	inv_a <- sqrt(((1 - rs) + abs(1 - rs)) / 2)
	bW.est <- b %*% W.hat

	### compute p-values & estimate p0 ###
	if(est_method == "UB"){
		P <- 2 * (1 - pt(abs(Z_vec), df = v_vec))
	} else if (est_method == "general"){
		P <- 2 * (1 - pnorm(abs(Z_vec)))
	}
	P_sort <- sort(P, index.return = TRUE)
	index <- P_sort$ix
	P <- P_sort$x
	if (missing(gama))  
		gama <- as.numeric(quantile(P, probs = 0.4))
	p0.est <- min(p, sum(P > gama) / (1 - gama))

	### estimate FDP ###
	t.default <- TRUE
	if (!missing(t_threshold_vec)){
		if (t_threshold_vec[1] == "pval")  { 
			### original t_threshold_vec == "pval" ###
			t_threshold_vec <- P
			t.default <- FALSE
		} 
		if (is.numeric(t_threshold_vec)){
			t.default <- (sum(t_threshold_vec >= 0) + sum(t_threshold_vec <= 1) < 2 * length(t_threshold_vec))
		}
	}
	if (t.default) {
		logt.l <- max(min(log(P)), log(1e-14))
		logt.u <- max(log(P))
		log_t_threshold_vec <- (logt.u - logt.l) * seq(from = 0.01, to = 1, by = 0.025) * 0.5 + 0.85 * logt.l + 0.15 * logt.u
		t_threshold_vec <- exp(log_t_threshold_vec)
	}
       
	FDPt <- Vt <- Rt <- rep(0, length(t_threshold_vec))
	for (l in 1 : length(t_threshold_vec)) {
		if(est_method == "UB"){
			P1 <- 2 * (1 - pt(abs(Z_vec), df = v_vec))
		} else if (est_method == "general"){
			P1 <- 2 * (1 - pnorm(abs(Z_vec)))
		}
		Rt[l] <- sum(P1 <= t_threshold_vec[l])
		a_vec <- rep(0, p)
		for (j in 1 : p)  {
			qtl <- qnorm(t_threshold_vec[l] / 2)
			if (inv_a[j] > 0)  {
				a_vec[j] <- pnorm((qtl + bW.est[j]) / inv_a[j]) + pnorm((qtl - bW.est[j]) / inv_a[j])
			} else {
                a_vec[j] <- as.numeric(abs(bW.est[j]) > abs(qtl))
			}
		}
		Vt[l] <- min(sum(a_vec), Rt[l]) 
		if (Rt[l]== 0) {
			FDPt[l] <- 0
		} else {
			FDPt[l] <- Vt[l] / Rt[l]
		}
	} 
	
    ### factor adjusted procedure ###
	adj.P <- as.vector(rep(0, p))
	for (j in 1 : p) {
		if (inv_a[j] > 0) {
			adj.P[j] <- 2 * (1 - pnorm(abs(Z_vec[j] - bW.est[j]) / inv_a[j]))
		} else {
			adj.P[j] <- as.numeric(abs(Z_vec[j] - bW.est[j]) == 0)
		}
	}
	adjP_sort <- sort(adj.P, index.return = TRUE)
	adj.index <- adjP_sort$ix
	adj.P <- adjP_sort$x
  
	### output ###
	Pvals <- data.frame(p.value = P, Index = index)
	adjPvals <- data.frame(p.value = adj.P, Index = adj.index)
	if (t.default) {
		FDPvals <- data.frame(minus.logt= - log(t_threshold_vec), rejects = Rt, false.rejects = Vt, FDP = FDPt)
	} else {
		FDPvals <- data.frame(t_threshold_vec = t_threshold_vec, rejects= Rt, false.rejects=Vt, FDP=FDPt )
	}
	results <- list("Pvalue" = Pvals, "adjPvalue" = adjPvals, "FDP" = FDPvals, "pi0" = p0.est / p, "kappa_0" = kappa_0, "sigma" = NULL)
    class(results) <- "FDPresults"
	
	if(!is.null(plot_method)){
		if (plot_method == "-log") {
			par(mfrow=c(2,2))
			hist(P, main = "Histogram of p-values", xlab = "p-values")
			plot(-log(t_threshold_vec), Rt, xlab = "-log(t)", ylab = "", main = "Number of total rejections", type = 'o')
			plot(-log(t_threshold_vec), Vt, xlab = "-log(t)", ylab = "", main = "Number of estimated false rejections", type = 'o')
			plot(-log(t_threshold_vec), FDPt, xlab = "-log(t)", ylab = "", main = "Estimated FDP", type = 'o')
		} else if (plot_method == "linear") {
			par(mfrow = c(2,2))
			hist(P, main = "Histogram of p-values", xlab = "p-values")
			plot(t_threshold_vec, Rt, xlab = "t", ylab = "", main = "Number of total rejections", type = 'o')
			plot(t_threshold_vec, Vt, xlab = "t", ylab = "", main = "Number of estimated false rejections", type = 'o')
			plot(t_threshold_vec, FDPt, xlab = "t", ylab = "", main = "Estimated FDP", type = 'o')
		} else if (plot_method == "log") {
			par(mfrow = c(2,2))
			hist(P, main = "Histogram of p-values", xlab = "p-values")
			plot(log(t_threshold_vec), Rt, xlab = "log(t)", ylab = "", main = "Number of total rejections", type = 'o')
			plot(log(t_threshold_vec), Vt, xlab = "log(t)", ylab = "", main = "Number of estimated false rejections", type = 'o')
			plot(log(t_threshold_vec), FDPt, xlab = "log(t)", ylab = "", main = "Estimated FDP", type = 'o')
		}
	}
	return(results)
}

TABLE_SUMMARY <- function(pfa_object){

	########################################################
	### this function is modified based on the reference ###
	### Vutov and Dickhaus (2022) Biometrical paper 	 ###
	########################################################

    summarise_table <- pfa_object %>% group_by(t)  %>% summarise(mean(R), sd(R), mean(S_adjP), sd(S_adjP), median(FDP), sd(FDP)) %>% as.data.frame()
    
    return(summarise_table)
}

EXTRACT_RAW_ADJ_FDP <- function(pfa_object, cutoff_vec, false_null_index_vec){

	########################################################
	### this function is modified based on the reference ###
	### Vutov and Dickhaus (2022) Biometrical paper 	 ###
	########################################################

	count_p1 <- count_adj_p1 <- p_val_p1 <- adj_p1 <- adj_total <- adj_p <- c()
  
    for(i in 1 : length(cutoff_vec)){
      p_val_p1 <- dim(pfa_object$Pvalue[pfa_object$Pvalue$p.value <= cutoff_vec[i] & pfa_object$Pvalue$Index %in% false_null_index_vec, ])[1]
      
      adj_p1 <- dim(pfa_object$adjPvalue[pfa_object$adjPvalue$p.value <= cutoff_vec[i] & pfa_object$adjPvalue$Index %in% false_null_index_vec, ])[1]
      
      adj_p <- dim(pfa_object$adjPvalue[pfa_object$adjPvalue$p.value <= cutoff_vec[i], ])[1]
      
      count_p1 <- rbind(count_p1, p_val_p1)
      
      count_adj_p1 <- rbind(count_adj_p1, adj_p1)
      
      adj_total <- rbind(adj_total, adj_p)
    }
	res <- data.frame(
		't'        = cutoff_vec,
		'R'        = pfa_object$FDP$rejects,        
		### number of total rejections 
		'V'        = pfa_object$FDP$false.rejects,  
		### number of false rejections
		'pi0'      = pfa_object$pi0,
		'FDP'      = pfa_object$FDP$FDP, 
		'kappa_0'  = pfa_object$kappa_0, 
		'S_unadjP' = count_p1, 
		### number of correct rejections using unadj. p-values
		'R_adjP'   = adj_total,
		### number of total rejections using adj. p-values
		'S_adjP'   = count_adj_p1) 
		### number of correct rejections using adj. p-values
  
	return(res)
}


#############################
### Loading the real data ###
#############################

INPUT_ADDRESS <- "..."
OUTPUT_ADDRESS <- "..."
DATA_INPUT_FILENAME <- paste(INPUT_ADDRESS, "EPSI_DATASET_445.RData", sep = "/")
### The real dataset is available upon request from the authors.
load(DATA_INPUT_FILENAME)
subject_names <- rownames(EPSI_X)
covariate_names <- colnames(EPSI_X)
variable_names <- colnames(EPSI_Y)

covariate <- data.frame(
				Age = as.numeric(EPSI_X[, 1]), 
				Gender = EPSI_X[, 2], 
				Total_Cholesterol = as.numeric(EPSI_X[, 3]), 
				CRP = as.numeric(EPSI_X[, 4]), 
				Working_Memory = as.numeric(EPSI_X[, 5]), 
				Processing_Speed = as.numeric(EPSI_X[, 6])
			)
rownames(covariate) <- subject_names
colnames(covariate) <- covariate_names

EPSI_Y_scale <- EPSI_Y * 1e-4
### 78 by 445, re-scale the dataset
set.seed(2024)
EPSI_Y_impt_scale <- missForest::missForest(xmis = EPSI_Y_scale)$ximp
### 78 by 445

##############################################
### Data analysis for the whole population ###
##############################################

M <- 1
reps_the_max <- 1e5
p_vec <- EPSI_p_vec
K <- length(p_vec)
p <- sum(p_vec)
n_vec <- EPSI_n
n <- sum(n_vec)

X_bar_mat <- matrix(apply(EPSI_Y_scale, 2, mean, na.rm = TRUE), 1, p)
### 1 by p
###   Min. 1st Qu.  Median    Mean 3rd Qu.    Max. 
### 0.2825  1.3225  1.7325  1.6446  2.1161  2.9953 
### mean = 1.644591 = 1.645

S_list_full <- S_list_pair <- S_list_impt <- list()
S_list_full[[1]] <- cov(EPSI_Y_scale, use = "everything")
S_list_pair[[1]] <- cov(EPSI_Y_scale, use = "pairwise.complete.obs")
S_list_impt[[1]] <- cov(EPSI_Y_impt_scale)

### S_mat_full <- cov(EPSI_Y_scale, use = "everything")
### na% = 0.767, non-na% = 0.233
### S_mat_pair <- cov(EPSI_Y_scale, use = "pairwise.complete.obs")
### S_mat_impt <- cov(EPSI_Y_impt_scale)
res_S_full <- BEST_UNBIASED_ESTIMATOR(S_list_full[[1]], p_vec)
res_S_pair <- BEST_UNBIASED_ESTIMATOR(S_list_pair[[1]], p_vec)
res_S_impt <- BEST_UNBIASED_ESTIMATOR(S_list_impt[[1]], p_vec)
res_S_full$A_mat
res_S_full$B_mat
res_S_pair$A_mat
res_S_pair$B_mat
res_S_impt$A_mat
res_S_impt$B_mat
### eigen(res_S_full$A_mat)$values
### [1] 0.033422667 0.031827502 0.027734469 0.018134177 0.001453949
### eigen(res_S_full$A_mat + res_S_full$B_mat %*% diag(p_vec))$values
### [1] 6.83710786 3.38301073 0.82278479 0.44391934 0.07194174
### eigen(res_S_pair$A_mat)$values
### [1] 0.058146545 0.057259145 0.039535641 0.032403287 0.002614149
### eigen(res_S_pair$A_mat + res_S_pair$B_mat %*% diag(p_vec))$values
### [1] 5.89287977 2.44235246 0.83860218 0.44186765 0.07401528
### eigen(res_S_impt$A_mat)$values
### [1] 0.051673928 0.051154211 0.036186303 0.028875697 0.002352752
### eigen(res_S_impt$A_mat + res_S_impt$B_mat %*% diag(p_vec))$values
### [1] 5.76163714 2.46442531 0.79816515 0.41394246 0.06965058
### the above matrices are p.d.

set.seed(2024)
COMPUTE_P_VALUES(
		  n_vec = n_vec, 
		  p_vec = p_vec, 
	  X_bar_mat = X_bar_mat, 
	mu_vec_test = rep(1.645, p), 
   reps_the_max = reps_the_max, 
		 S_list = S_list_full,
	  sig_level = 0.05,		 
		 COMPUTE_THEORETICAL_DISTRIBUTIONS = COMPUTE_THEORETICAL_DISTRIBUTIONS, 
	COMPUTE_GAMMA_MATRIX = COMPUTE_GAMMA_MATRIX, 
	COMPUTE_EMPIRICAL_TEST_STATISTICS_SAMPLE = COMPUTE_EMPIRICAL_TEST_STATISTICS_SAMPLE, 
			BLOCK_HADAMARD_PRODUCT = BLOCK_HADAMARD_PRODUCT, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_1 = COMPUTE_EMPIRICAL_LOG_LAMBDA_1, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_2 = COMPUTE_EMPIRICAL_LOG_LAMBDA_2, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_3 = COMPUTE_EMPIRICAL_LOG_LAMBDA_3, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_4 = COMPUTE_EMPIRICAL_LOG_LAMBDA_4)
### S_list_full 
###          Lambda13  Lambda24B  Lambda24F           G
### statistics       NA        NA        NA 310365.1292
### cutpoint         NA  249.3716  249.2493    496.2119
### rejection        NA        NA        NA      1.0000
### p_value          NA        NA        NA      0.0000
### S_list_pair
###            Lambda13  Lambda24B  Lambda24F           G
### statistics      Inf 21855.5479 21855.5479 239953.8668
### cutpoint         NA   249.1284   249.1281    496.0704
### rejection        NA     1.0000     1.0000      1.0000
### p_value          NA     0.0000     0.0000      0.0000
### S_list_impt
###            Lambda13  Lambda24B Lambda24F           G
### statistics      Inf 23129.4892 23129.489 259189.2379
### cutpoint         NA   249.4065   249.287    495.9341
### rejection        NA     1.0000     1.000      1.0000
### p_value          NA     0.0000     0.000      0.0000

X_bar_vec <- X_bar_mat[1, ] - rep(1.645, p)
### p by 1
res_S_mat_full <- BEST_UNBIASED_ESTIMATOR(S_list_full[[1]], p_vec)
res_S_mat_pair <- BEST_UNBIASED_ESTIMATOR(S_list_pair[[1]], p_vec)
res_S_mat_impt <- BEST_UNBIASED_ESTIMATOR(S_list_impt[[1]], p_vec)

v_vec_full <- rep((n - 1) * p_vec * (diag(res_S_mat_full$A_mat) + diag(res_S_mat_full$B_mat)) ^ 2 / (diag(res_S_mat_full$A_mat) ^ 2 + p_vec * diag(res_S_mat_full$B_mat) ^ 2 + 2 * diag(res_S_mat_full$A_mat) * diag(res_S_mat_full$B_mat)), times = p_vec)
### p by 1

v_vec_pair <- rep((n - 1) * p_vec * (diag(res_S_mat_pair$A_mat) + diag(res_S_mat_pair$B_mat)) ^ 2 / (diag(res_S_mat_pair$A_mat) ^ 2 + p_vec * diag(res_S_mat_pair$B_mat) ^ 2 + 2 * diag(res_S_mat_pair$A_mat) * diag(res_S_mat_pair$B_mat)), times = p_vec)
### p by 1

v_vec_impt <- rep((n - 1) * p_vec * (diag(res_S_mat_impt$A_mat) + diag(res_S_mat_impt$B_mat)) ^ 2 / (diag(res_S_mat_impt$A_mat) ^ 2 + p_vec * diag(res_S_mat_impt$B_mat) ^ 2 + 2 * diag(res_S_mat_impt$A_mat) * diag(res_S_mat_impt$B_mat)), times = p_vec)
### p by 1

T_vec_full <- sqrt(n) * drop(solve(BLOCK_HADAMARD_PRODUCT(A_mat = diag(sqrt(diag(diag(diag(res_S_mat_full$A_mat) + diag(res_S_mat_full$B_mat))))), B_mat = matrix(0, K, K), p_vec = p_vec)) %*% X_bar_vec)
### p by 1
T_vec_pair <- sqrt(n) * drop(solve(BLOCK_HADAMARD_PRODUCT(A_mat = diag(sqrt(diag(diag(diag(res_S_mat_pair$A_mat) + diag(res_S_mat_pair$B_mat))))), B_mat = matrix(0, K, K), p_vec = p_vec)) %*% X_bar_vec)
### p by 1
T_vec_impt <- sqrt(n) * drop(solve(BLOCK_HADAMARD_PRODUCT(A_mat = diag(sqrt(diag(diag(diag(res_S_mat_impt$A_mat) + diag(res_S_mat_impt$B_mat))))), B_mat = matrix(0, K, K), p_vec = p_vec)) %*% X_bar_vec)
### p by 1

Psi_mat_est_full <- BLOCK_HADAMARD_PRODUCT(A_mat = diag(1 / sqrt(diag(diag(diag(res_S_mat_full$A_mat) + diag(res_S_mat_full$B_mat))))) %*% res_S_mat_full$A_mat %*% diag(1 / sqrt(diag(diag(diag(res_S_mat_full$A_mat) + diag(res_S_mat_full$B_mat))))), B_mat = diag(1 / sqrt(diag(diag(diag(res_S_mat_full$A_mat) + diag(res_S_mat_full$B_mat))))) %*% res_S_mat_full$B_mat %*% diag(1 / sqrt(diag(diag(diag(res_S_mat_full$A_mat) + diag(res_S_mat_full$B_mat))))), p_vec = p_vec)
### p by p

Psi_mat_est_pair <- BLOCK_HADAMARD_PRODUCT(A_mat = diag(1 / sqrt(diag(diag(diag(res_S_mat_pair$A_mat) + diag(res_S_mat_pair$B_mat))))) %*% res_S_mat_pair$A_mat %*% diag(1 / sqrt(diag(diag(diag(res_S_mat_pair$A_mat) + diag(res_S_mat_pair$B_mat))))), B_mat = diag(1 / sqrt(diag(diag(diag(res_S_mat_pair$A_mat) + diag(res_S_mat_pair$B_mat))))) %*% res_S_mat_pair$B_mat %*% diag(1 / sqrt(diag(diag(diag(res_S_mat_pair$A_mat) + diag(res_S_mat_pair$B_mat))))), p_vec = p_vec)
### p by p

Psi_mat_est_impt <- BLOCK_HADAMARD_PRODUCT(A_mat = diag(1 / sqrt(diag(diag(diag(res_S_mat_impt$A_mat) + diag(res_S_mat_impt$B_mat))))) %*% res_S_mat_impt$A_mat %*% diag(1 / sqrt(diag(diag(diag(res_S_mat_impt$A_mat) + diag(res_S_mat_impt$B_mat))))), B_mat = diag(1 / sqrt(diag(diag(diag(res_S_mat_impt$A_mat) + diag(res_S_mat_impt$B_mat))))) %*% res_S_mat_impt$B_mat %*% diag(1 / sqrt(diag(diag(diag(res_S_mat_impt$A_mat) + diag(res_S_mat_impt$B_mat))))), p_vec = p_vec)
### p by p

log_t_threshold_vec <- - seq(130, 150, length.out = 100)
### 100 by 1
t_threshold_vec <- exp(log_t_threshold_vec)
### 100 by 1

set.seed(2024)
res_pfa_est_full <- ESTIMATE_FDP(
				est_method = "UB", 
				     Z_vec = T_vec_full, 
					 v_vec = v_vec_full, 
				 Sigma_mat = Psi_mat_est_full, 
		   t_threshold_vec = t_threshold_vec, 
		        reg_method = "L1", 
				       eps = .05, 
			###	   kappa_0 = K, 
			   plot_method = NULL)
			   
TABLE_SUMMARY(EXTRACT_RAW_ADJ_FDP(pfa_object = res_pfa_est_full, cutoff_vec = t_threshold_vec, false_null_index_vec = NULL))
### 5.637989E-63
variable_names[res_pfa_est_full$adjPvalue$Index[res_pfa_est_full$adjPvalue$p.value < 5.637989E-63]]
### 351

set.seed(2024)
res_pfa_est_pair <- ESTIMATE_FDP(
				est_method = "UB", 
				     Z_vec = T_vec_pair, 
					 v_vec = v_vec_pair, 
				 Sigma_mat = Psi_mat_est_pair, 
		   t_threshold_vec = t_threshold_vec, 
		        reg_method = "L1", 
				       eps = .05, 
			###	   kappa_0 = K, 
			   plot_method = NULL)
			   
TABLE_SUMMARY(EXTRACT_RAW_ADJ_FDP(pfa_object = res_pfa_est_pair, cutoff_vec = t_threshold_vec, false_null_index_vec = NULL))
### 3.6198E-60
variable_names[res_pfa_est_pair$adjPvalue$Index[res_pfa_est_pair$adjPvalue$p.value < 3.6198E-60]]
### 334

set.seed(2024)
res_pfa_est_impt <- ESTIMATE_FDP(
				est_method = "UB", 
				     Z_vec = T_vec_impt, 
					 v_vec = v_vec_impt, 
				 Sigma_mat = Psi_mat_est_impt, 
		   t_threshold_vec = t_threshold_vec, 
		        reg_method = "L1", 
				       eps = .05, 
			###	   kappa_0 = K, 
			   plot_method = NULL)
			   
TABLE_SUMMARY(EXTRACT_RAW_ADJ_FDP(pfa_object = res_pfa_est_impt, cutoff_vec = t_threshold_vec, false_null_index_vec = NULL))
### 3.764018e-63
variable_names[res_pfa_est_pair$adjPvalue$Index[res_pfa_est_pair$adjPvalue$p.value < 3.764018E-63]]
### 334


################################################
### Data analysis for the sex sub-population ###
################################################

Y_list <- Y_impt_list <- list()
### M by n by p
Y_list[[1]] <- EPSI_Y_scale[rownames(subset(covariate, Gender == "Male")), ]
### 39 by 445
Y_list[[2]] <- EPSI_Y_scale[rownames(subset(covariate, Gender == "Female")), ]
### 39 by 445
Y_impt_list[[1]] <- EPSI_Y_impt_scale[rownames(subset(covariate, Gender == "Male")), ]
### 39 by 445
Y_impt_list[[2]] <- EPSI_Y_impt_scale[rownames(subset(covariate, Gender == "Female")), ]
### 39 by 445

M <- 2
reps_the_max <- 1e5
p_vec <- EPSI_p_vec
p <- sum(p_vec)
n_vec <- unlist(lapply(Y_list, nrow))
n <- sum(n_vec)

res_S_full_1 <- BEST_UNBIASED_ESTIMATOR(cov(Y_list[[1]], use = "everything"), p_vec)
res_S_full_2 <- BEST_UNBIASED_ESTIMATOR(cov(Y_list[[2]], use = "everything"), p_vec)
res_S_pair_1 <- BEST_UNBIASED_ESTIMATOR(cov(Y_list[[1]], use = "pairwise.complete.obs"), p_vec)
res_S_pair_2 <- BEST_UNBIASED_ESTIMATOR(cov(Y_list[[2]], use = "pairwise.complete.obs"), p_vec)
res_S_impt_1 <- BEST_UNBIASED_ESTIMATOR(cov(Y_impt_list[[1]]), p_vec)
res_S_impt_2 <- BEST_UNBIASED_ESTIMATOR(cov(Y_impt_list[[2]]), p_vec)

res_S_full_1$A_mat
res_S_full_1$B_mat
res_S_full_2$A_mat
res_S_full_2$B_mat

res_S_pair_1$A_mat
res_S_pair_1$B_mat
res_S_pair_2$A_mat
res_S_pair_2$B_mat

res_S_impt_1$A_mat
res_S_impt_1$B_mat
res_S_impt_2$A_mat
res_S_impt_2$B_mat

### eigen(res_S_full_1$A_mat)$values
### [1] 0.044201640 0.036598133 0.028684172 0.018996229 0.001421158
### eigen(res_S_full_1$A_mat + res_S_full_1$B_mat %*% diag(p_vec))$values
### [1] 7.65947014 3.34428094 0.83628940 0.19767087 0.06882667
### eigen(res_S_full_2$A_mat)$values
### [1] 0.037679548 0.036163372 0.030634340 0.021916172 0.001982911
### eigen(res_S_full_2$A_mat + res_S_full_2$B_mat %*% diag(p_vec))$values
### [1] 6.9297950 1.9978298 0.8940038 0.6657509 0.0494033
### eigen(res_S_pair_1$A_mat)$values
### [1] 0.06189206 0.05889223 0.03927825 0.03262717 0.00258133
### eigen(res_S_pair_1$A_mat + res_S_pair_1$B_mat %*% diag(p_vec))$values
### [1] 5.8415337 2.5167944 0.8251106 0.1885787 0.0751556
### eigen(res_S_pair_2$A_mat)$values
### [1] 0.054735808 0.053999447 0.039103494 0.030569062 0.002613425
### eigen(res_S_pair_2$A_mat + res_S_pair_2$B_mat %*% diag(p_vec))$values
### [1] 6.46819174 1.64761907 0.84258428 0.66558660 0.04618525

### eigen(res_S_impt_1$A_mat)$values
### [1] 0.055964807 0.052273504 0.034521893 0.028593453 0.002255068
### eigen(res_S_impt_1$A_mat + res_S_impt_1$B_mat %*% diag(p_vec))$values
### [1] 5.99637328 2.44217070 0.77866862 0.18338471 0.07033503
### eigen(res_S_impt_2$A_mat)$values
### [1] 0.049679870 0.046584197 0.036756182 0.027743807 0.002399256
### eigen(res_S_impt_2$A_mat + res_S_impt_2$B_mat %*% diag(p_vec))$values
### [1] 6.23113518 1.61469123 0.80645926 0.63331182 0.04539787

X_bar_mat <- matrix(0, nrow = M, ncol = p)
### 2 by 445
### summary(X_bar_mat[2, ] - X_bar_mat[1, ])
###      Min.   1st Qu.    Median      Mean   3rd Qu.      Max. 
### -0.357810 -0.038635 -0.003153 -0.001094  0.052460  0.334254 

S_list_full <- S_list_pair <- S_list_impt <- list()
for(m in 1 : M){
	X_bar_mat[m, ] <- apply(Y_list[[m]], 2, mean, na.rm = TRUE)
	### 445 by 1
	S_list_full[[m]] <- cov(Y_list[[m]], use = "everything")
	S_list_pair[[m]] <- cov(Y_list[[m]], use = "pairwise.complete.obs")
	S_list_impt[[m]] <- cov(Y_impt_list[[m]])	
}

set.seed(2024)
COMPUTE_P_VALUES(
		  n_vec = n_vec, 
		  p_vec = p_vec, 
	  X_bar_mat = X_bar_mat, 
	mu_vec_test = NULL, 
   reps_the_max = reps_the_max, 
		 S_list = S_list_full, 
	  sig_level = 0.05,
		 COMPUTE_THEORETICAL_DISTRIBUTIONS = COMPUTE_THEORETICAL_DISTRIBUTIONS, 
	COMPUTE_GAMMA_MATRIX = COMPUTE_GAMMA_MATRIX, 
	COMPUTE_EMPIRICAL_TEST_STATISTICS_SAMPLE = COMPUTE_EMPIRICAL_TEST_STATISTICS_SAMPLE, 
			BLOCK_HADAMARD_PRODUCT = BLOCK_HADAMARD_PRODUCT, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_1 = COMPUTE_EMPIRICAL_LOG_LAMBDA_1, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_2 = COMPUTE_EMPIRICAL_LOG_LAMBDA_2, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_3 = COMPUTE_EMPIRICAL_LOG_LAMBDA_3, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_4 = COMPUTE_EMPIRICAL_LOG_LAMBDA_4)

### S_list_full
###            Lambda13 Lambda24B Lambda24F         G
### statistics       NA        NA        NA 1711.9013
### cutpoint   9.459623  252.5214  252.6089  496.1173
### rejection        NA        NA        NA    1.0000
### p_value          NA        NA        NA    0.0000
### S_list_pair
###             Lambda13 Lambda24B Lambda24F         G
### statistics 20.898064  510.5662  510.5662 1011.3286
### cutpoint    9.442711  252.5747  252.5052  496.3611
### rejection   1.000000    1.0000    1.0000    1.0000
### p_value     0.000010    0.0000    0.0000    0.0000
### S_list_impt
###             Lambda13 Lambda24B Lambda24F         G
### statistics 27.983891  567.5910  567.5910 1126.2402
### cutpoint    9.434125  252.6117  252.4896  495.9007
### rejection   1.000000    1.0000    1.0000    1.0000
### p_value     0.000000    0.0000    0.0000    0.0000

################################################
### Data analysis for the age sub-population ###
################################################

Y_list <- Y_impt_list <- list()
### M by n by p
Y_list[[1]] <- EPSI_Y_scale[rownames(subset(covariate, Age <= 30)), ]
### 24 by 445
Y_list[[2]] <- EPSI_Y_scale[rownames(subset(covariate, Age > 30 & Age <= 50)), ]
### 27 by 445
Y_list[[3]] <- EPSI_Y_scale[rownames(subset(covariate, Age > 50)), ]
### 27 by 445
Y_impt_list[[1]] <- EPSI_Y_impt_scale[rownames(subset(covariate, Age <= 30)), ]
### 24 by 445
Y_impt_list[[2]] <- EPSI_Y_impt_scale[rownames(subset(covariate, Age > 30 & Age <= 50)), ]
### 27 by 445
Y_impt_list[[3]] <- EPSI_Y_impt_scale[rownames(subset(covariate, Age > 50)), ]
### 27 by 445

M <- 3
reps_the_max <- 1e5
p_vec <- EPSI_p_vec
p <- sum(p_vec)
n_vec <- unlist(lapply(Y_list, nrow))
n <- sum(n_vec)

res_S_full_1 <- BEST_UNBIASED_ESTIMATOR(cov(Y_list[[1]], use = "everything"), p_vec)
res_S_full_2 <- BEST_UNBIASED_ESTIMATOR(cov(Y_list[[2]], use = "everything"), p_vec)
res_S_full_3 <- BEST_UNBIASED_ESTIMATOR(cov(Y_list[[3]], use = "everything"), p_vec)
res_S_pair_1 <- BEST_UNBIASED_ESTIMATOR(cov(Y_list[[1]], use = "pairwise.complete.obs"), p_vec)
res_S_pair_2 <- BEST_UNBIASED_ESTIMATOR(cov(Y_list[[2]], use = "pairwise.complete.obs"), p_vec)
res_S_pair_3 <- BEST_UNBIASED_ESTIMATOR(cov(Y_list[[3]], use = "pairwise.complete.obs"), p_vec)
res_S_impt_1 <- BEST_UNBIASED_ESTIMATOR(cov(Y_impt_list[[1]]), p_vec)
res_S_impt_2 <- BEST_UNBIASED_ESTIMATOR(cov(Y_impt_list[[2]]), p_vec)
res_S_impt_3 <- BEST_UNBIASED_ESTIMATOR(cov(Y_impt_list[[3]]), p_vec)

res_S_full_1$A_mat
res_S_full_1$B_mat
res_S_full_2$A_mat
res_S_full_2$B_mat
res_S_full_3$A_mat
res_S_full_3$B_mat

res_S_pair_1$A_mat
res_S_pair_1$B_mat
res_S_pair_2$A_mat
res_S_pair_2$B_mat
res_S_pair_3$A_mat
res_S_pair_3$B_mat

res_S_impt_1$A_mat
res_S_impt_1$B_mat
res_S_impt_2$A_mat
res_S_impt_2$B_mat
res_S_impt_3$A_mat
res_S_impt_3$B_mat

### eigen(res_S_full_1$A_mat)$values
### [1] 0.053350926 0.046277222 0.029753252 0.021366650 0.001825706
### eigen(res_S_full_1$A_mat + res_S_full_1$B_mat %*% diag(p_vec))$values
### [1] 7.53600902 1.51036103 0.64065973 0.42692385 0.04787724
### eigen(res_S_full_2$A_mat)$values
### [1] 0.035795920 0.035137335 0.022520712 0.017365453 0.001427441
### eigen(res_S_full_2$A_mat + res_S_full_2$B_mat %*% diag(p_vec))$values
### [1] 2.8136713 1.5157808 0.7476768 0.3002051 0.0684199
### eigen(res_S_full_3$A_mat)$values
### [1] 0.04179828 0.03883030 0.03446221 0.02600713 0.00191751
### eigen(res_S_full_3$A_mat + res_S_full_3$B_mat %*% diag(p_vec))$values
### [1] 3.79089335 1.90023350 0.89320526 0.23677298 0.09200392
### eigen(res_S_pair_1$A_mat)$values
### [1] 0.062057464 0.059649342 0.038759132 0.034896836 0.002794045
### eigen(res_S_pair_1$A_mat + res_S_pair_1$B_mat %*% diag(p_vec))$values
### [1] 4.19144130 1.01010556 0.65710342 0.27772721 0.06211394
### eigen(res_S_pair_2$A_mat)$values
### [1] 0.059320545 0.049907920 0.028023137 0.025702080 0.001941917
### eigen(res_S_pair_2$A_mat + res_S_pair_2$B_mat %*% diag(p_vec))$values
### [1] 2.8835565 1.7162349 0.7214563 0.2823036 0.0623552
### eigen(res_S_pair_3$A_mat)$values
### [1] 0.056037606 0.049568509 0.043730484 0.034145290 0.002623045
### eigen(res_S_pair_3$A_mat + res_S_pair_3$B_mat %*% diag(p_vec))$values
### [1] 3.3021339 1.6923830 0.8384606 0.1914089 0.0828767
### eigen(res_S_impt_1$A_mat)$values
### [1] 0.057748329 0.054646582 0.035820792 0.031251166 0.002552982
### eigen(res_S_impt_1$A_mat + res_S_impt_1$B_mat %*% diag(p_vec))$values
### [1] 4.38111914 1.10261411 0.62655781 0.29319395 0.05478817
### eigen(res_S_impt_2$A_mat)$values
### [1] 0.045368266 0.043477349 0.025624045 0.022916805 0.001762165
### eigen(res_S_impt_2$A_mat + res_S_impt_2$B_mat %*% diag(p_vec))$values
### [1] 2.6869521 1.6834754 0.6873597 0.2820097 0.0603412
### eigen(res_S_impt_3$A_mat)$values
### [1] 0.049104708 0.044334627 0.039424316 0.029969615 0.002306695
### eigen(res_S_impt_3$A_mat + res_S_impt_3$B_mat %*% diag(p_vec))$values
### [1] 3.24485781 1.68413378 0.77891118 0.19432088 0.07665291

X_bar_mat <- matrix(0, nrow = M, ncol = p)
### 3 by 445
### summary(X_bar_mat[2, ] - X_bar_mat[1, ])
###     Min.  1st Qu.   Median     Mean  3rd Qu.     Max. 
### -0.42145 -0.18835 -0.01410 -0.05794  0.03118  0.60525 
### summary(X_bar_mat[3, ] - X_bar_mat[1, ])
###     Min.  1st Qu.   Median     Mean  3rd Qu.     Max. 
### -0.73015 -0.28272 -0.01058 -0.08890  0.07233  0.64906 

S_list_full <- S_list_pair <- S_list_impt <- list()
for(m in 1 : M){
	X_bar_mat[m, ] <- apply(Y_list[[m]], 2, mean, na.rm = TRUE)
	### 445 by 1
	S_list_full[[m]] <- cov(Y_list[[m]], use = "everything")
	S_list_pair[[m]] <- cov(Y_list[[m]], use = "pairwise.complete.obs")
	S_list_impt[[m]] <- cov(Y_impt_list[[m]])	
}

set.seed(2024)
COMPUTE_P_VALUES(
		  n_vec = n_vec, 
		  p_vec = p_vec, 
	  X_bar_mat = X_bar_mat, 
	mu_vec_test = NULL, 
   reps_the_max = reps_the_max, 
		 S_list = S_list_full, 
	  sig_level = 0.05,
		 COMPUTE_THEORETICAL_DISTRIBUTIONS = COMPUTE_THEORETICAL_DISTRIBUTIONS, 
	COMPUTE_GAMMA_MATRIX = COMPUTE_GAMMA_MATRIX, 
	COMPUTE_EMPIRICAL_TEST_STATISTICS_SAMPLE = COMPUTE_EMPIRICAL_TEST_STATISTICS_SAMPLE, 
			BLOCK_HADAMARD_PRODUCT = BLOCK_HADAMARD_PRODUCT, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_1 = COMPUTE_EMPIRICAL_LOG_LAMBDA_1, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_2 = COMPUTE_EMPIRICAL_LOG_LAMBDA_2, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_3 = COMPUTE_EMPIRICAL_LOG_LAMBDA_3, 
	COMPUTE_EMPIRICAL_LOG_LAMBDA_4 = COMPUTE_EMPIRICAL_LOG_LAMBDA_4)

### S_list_full
###            Lambda13 Lambda24B Lambda24F         G
### statistics       NA        NA        NA 5036.7394
### cutpoint   16.53294  493.1566  493.0732  963.5867
### rejection        NA        NA        NA    1.0000
### p_value          NA        NA        NA    0.0000
### S_list_pair
###             Lambda13 Lambda24B Lambda24F         G
### statistics 166.80104 1496.8884 1496.8884 3053.1449
### cutpoint    16.55976  493.2534  493.0556  962.6126
### rejection    1.00000    1.0000    1.0000    1.0000
### p_value      0.00000    0.0000    0.0000    0.0000
### S_list_impt
###             Lambda13 Lambda24B Lambda24F         G
### statistics 172.01010 1667.3736 1667.3736 3417.4794
### cutpoint    16.52212  493.0129  493.3332  963.2381
### rejection    1.00000    1.0000    1.0000    1.0000
### p_value      0.00000    0.0000    0.0000    0.0000


#################################################
### Plot the Heatmap for Correlation Matrices ###
#################################################

Y_a <- EPSI_Y
Y_m <- EPSI_Y[rownames(subset(covariate, Gender == "Male")), ]
Y_f <- EPSI_Y[rownames(subset(covariate, Gender == "Female")), ]
Y_low <- EPSI_Y[rownames(subset(covariate, Age <= 30)), ]
Y_mid <- EPSI_Y[rownames(subset(covariate, Age > 30 & Age <= 50)), ]
Y_upp <- EPSI_Y[rownames(subset(covariate, Age > 50)), ]

set.seed(2024)
EPSI_Z <- missForest::missForest(xmis = EPSI_Y)$ximp
Z_a <- EPSI_Z
Z_m <- EPSI_Z[rownames(subset(covariate, Gender == "Male")), ]
Z_f <- EPSI_Z[rownames(subset(covariate, Gender == "Female")), ]
Z_low <- EPSI_Z[rownames(subset(covariate, Age <= 30)), ]
Z_mid <- EPSI_Z[rownames(subset(covariate, Age > 30 & Age <= 50)), ]
Z_upp <- EPSI_Z[rownames(subset(covariate, Age > 50)), ]

cor_Y_a <- cor(x = Y_a, use = "pairwise.complete.obs")
cor_Y_m <- cor(x = Y_m, use = "pairwise.complete.obs")
cor_Y_f <- cor(x = Y_f, use = "pairwise.complete.obs")
cor_Y_low <- cor(x = Y_low, use = "pairwise.complete.obs")
cor_Y_mid <- cor(x = Y_mid, use = "pairwise.complete.obs")
cor_Y_upp <- cor(x = Y_upp, use = "pairwise.complete.obs")

cor_Z_a <- cor(x = Z_a, use = "everything")
cor_Z_m <- cor(x = Z_m, use = "everything")
cor_Z_f <- cor(x = Z_f, use = "everything")
cor_Z_low <- cor(x = Z_low, use = "everything")
cor_Z_mid <- cor(x = Z_mid, use = "everything")
cor_Z_upp <- cor(x = Z_upp, use = "everything")

### check the correct order of Cho, Cre, Glx, Mi, NAA
### colnames(EPSI_Y) <- c(rep("Cho", 89), rep("Cre", 89), rep("Glx", 89), rep("Mi", 89), rep("NAA", 89))
### using scale_y_discrete(limits=rev)
### rev x or y does not work

plot_Y_a <- ggplot2::ggplot(
				data = reshape2::melt(cor_Y_a), 
			 mapping = aes(x = Var1, y = Var2, fill = value)) + 
  ggplot2::geom_tile() +
  ggplot2::scale_fill_gradientn(colours = pals::coolwarm(100), 
								  guide = "colourbar") +
  scale_y_discrete(limits = rev) + 
  theme_void()
   
plot_Y_m <- ggplot2::ggplot(
				data = reshape2::melt(cor_Y_m), 
			 mapping = aes(x = Var1, y = Var2, fill = value)) + 
  ggplot2::geom_tile() +
  ggplot2::scale_fill_gradientn(colours = pals::coolwarm(100), 
								  guide = "colourbar") +
  scale_y_discrete(limits = rev) + 
  theme_void()
   
plot_Y_f <- ggplot2::ggplot(
				data = reshape2::melt(cor_Y_f), 
			 mapping = aes(x = Var1, y = Var2, fill = value)) + 
  ggplot2::geom_tile() +
  ggplot2::scale_fill_gradientn(colours = pals::coolwarm(100), 
								  guide = "colourbar") +
  scale_y_discrete(limits = rev) + 
  theme_void()   

plot_Y_low <- ggplot2::ggplot(
				data = reshape2::melt(cor_Y_low), 
			 mapping = aes(x = Var1, y = Var2, fill = value)) + 
  ggplot2::geom_tile() +
  ggplot2::scale_fill_gradientn(colours = pals::coolwarm(100), 
								  guide = "colourbar") +
  scale_y_discrete(limits = rev) + 
  theme_void()  

plot_Y_mid <- ggplot2::ggplot(
				data = reshape2::melt(cor_Y_mid), 
			 mapping = aes(x = Var1, y = Var2, fill = value)) + 
  ggplot2::geom_tile() +
  ggplot2::scale_fill_gradientn(colours = pals::coolwarm(100), 
								  guide = "colourbar") +
  scale_y_discrete(limits = rev) + 
  theme_void()

plot_Y_upp <- ggplot2::ggplot(
				data = reshape2::melt(cor_Y_upp), 
			 mapping = aes(x = Var1, y = Var2, fill = value)) + 
  ggplot2::geom_tile() +
  ggplot2::scale_fill_gradientn(colours = pals::coolwarm(100), 
								  guide = "colourbar") +
  scale_y_discrete(limits = rev) + 
  theme_void()
   
plot_Z_a <- ggplot2::ggplot(
				data = reshape2::melt(cor_Z_a), 
			 mapping = aes(x = Var1, y = Var2, fill = value)) + 
  ggplot2::geom_tile() +
  ggplot2::scale_fill_gradientn(colours = pals::coolwarm(100), 
								  guide = "colourbar") +
  scale_y_discrete(limits = rev) + 
  theme_void() 

plot_Z_m <- ggplot2::ggplot(
				data = reshape2::melt(cor_Z_m), 
			 mapping = aes(x = Var1, y = Var2, fill = value)) + 
  ggplot2::geom_tile() +
  ggplot2::scale_fill_gradientn(colours = pals::coolwarm(100), 
								  guide = "colourbar") +
  scale_y_discrete(limits = rev) + 
  theme_void()
   
plot_Z_f <- ggplot2::ggplot(
				data = reshape2::melt(cor_Z_f), 
			 mapping = aes(x = Var1, y = Var2, fill = value)) + 
  ggplot2::geom_tile() +
  ggplot2::scale_fill_gradientn(colours = pals::coolwarm(100), 
								  guide = "colourbar") +
  scale_y_discrete(limits = rev) + 
  theme_void()   
 
plot_Z_low <- ggplot2::ggplot(
				data = reshape2::melt(cor_Z_low), 
			 mapping = aes(x = Var1, y = Var2, fill = value)) + 
  ggplot2::geom_tile() +
  ggplot2::scale_fill_gradientn(colours = pals::coolwarm(100), 
								  guide = "colourbar") +
  scale_y_discrete(limits = rev) + 
  theme_void()

plot_Z_mid <- ggplot2::ggplot(
				data = reshape2::melt(cor_Z_mid), 
			 mapping = aes(x = Var1, y = Var2, fill = value)) + 
  ggplot2::geom_tile() +
  ggplot2::scale_fill_gradientn(colours = pals::coolwarm(100), 
								  guide = "colourbar") +
  scale_y_discrete(limits = rev) + 
  theme_void()

plot_Z_upp <- ggplot2::ggplot(
				data = reshape2::melt(cor_Z_upp), 
			 mapping = aes(x = Var1, y = Var2, fill = value)) + 
  ggplot2::geom_tile() +
  ggplot2::scale_fill_gradientn(colours = pals::coolwarm(100), 
								  guide = "colourbar") +
  scale_y_discrete(limits = rev) + 
  theme_void()   
 
DATA_OUTPUT_FILENAME_Y_a <- paste(OUTPUT_ADDRESS, "plot_Y_a.pdf", sep = "/")
DATA_OUTPUT_FILENAME_Y_m <- paste(OUTPUT_ADDRESS, "plot_Y_m.pdf", sep = "/")
DATA_OUTPUT_FILENAME_Y_f <- paste(OUTPUT_ADDRESS, "plot_Y_f.pdf", sep = "/")
DATA_OUTPUT_FILENAME_Y_low <- paste(OUTPUT_ADDRESS, "plot_Y_low.pdf", sep = "/")
DATA_OUTPUT_FILENAME_Y_mid <- paste(OUTPUT_ADDRESS, "plot_Y_mid.pdf", sep = "/")
DATA_OUTPUT_FILENAME_Y_upp <- paste(OUTPUT_ADDRESS, "plot_Y_upp.pdf", sep = "/")

DATA_OUTPUT_FILENAME_Z_a <- paste(OUTPUT_ADDRESS, "plot_Z_a.pdf", sep = "/")
DATA_OUTPUT_FILENAME_Z_m <- paste(OUTPUT_ADDRESS, "plot_Z_m.pdf", sep = "/")
DATA_OUTPUT_FILENAME_Z_f <- paste(OUTPUT_ADDRESS, "plot_Z_f.pdf", sep = "/")

DATA_OUTPUT_FILENAME_Z_low <- paste(OUTPUT_ADDRESS, "plot_Z_low.pdf", sep = "/")
DATA_OUTPUT_FILENAME_Z_mid <- paste(OUTPUT_ADDRESS, "plot_Z_mid.pdf", sep = "/")
DATA_OUTPUT_FILENAME_Z_upp <- paste(OUTPUT_ADDRESS, "plot_Z_upp.pdf", sep = "/")

ggsave(file = DATA_OUTPUT_FILENAME_Y_a, plot = plot_Y_a, width = 3.5, height = 3)
ggsave(file = DATA_OUTPUT_FILENAME_Y_m, plot = plot_Y_m, width = 3.5, height = 3)
ggsave(file = DATA_OUTPUT_FILENAME_Y_f, plot = plot_Y_f, width = 3.5, height = 3)
ggsave(file = DATA_OUTPUT_FILENAME_Y_low, plot = plot_Y_low, width = 3.5, height = 3)
ggsave(file = DATA_OUTPUT_FILENAME_Y_mid, plot = plot_Y_mid, width = 3.5, height = 3)
ggsave(file = DATA_OUTPUT_FILENAME_Y_upp, plot = plot_Y_upp, width = 3.5, height = 3)

ggsave(file = DATA_OUTPUT_FILENAME_Z_a, plot = plot_Z_a, width = 3.5, height = 3)
ggsave(file = DATA_OUTPUT_FILENAME_Z_m, plot = plot_Z_m, width = 3.5, height = 3)
ggsave(file = DATA_OUTPUT_FILENAME_Z_f, plot = plot_Z_f, width = 3.5, height = 3)
ggsave(file = DATA_OUTPUT_FILENAME_Z_low, plot = plot_Z_low, width = 3.5, height = 3)
ggsave(file = DATA_OUTPUT_FILENAME_Z_mid, plot = plot_Z_mid, width = 3.5, height = 3)
ggsave(file = DATA_OUTPUT_FILENAME_Z_upp, plot = plot_Z_upp, width = 3.5, height = 3)








