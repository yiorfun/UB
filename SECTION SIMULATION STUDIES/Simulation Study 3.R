######################################################################
### SIMULATION STUDY 3 			    		   				       ###
### - Lambda1: LRT testing the covariance matrix is a UB matrix    ###
### - Study 3: FDP estimation						               ###
######################################################################

############################
### Loading the packages ###
############################

REQUIRED_PACKAGES <- c(
	"mvtnorm",		
	### mvtnorm::dmvnorm() and mvtnorm::rmvnorm(), compute the density and generate random vector of multivariate normal distribution
	"quantreg",
	### quantreg：：rq(): computes an estimate on the conditional quantile function of the response
	"POET", 
	### POET::POET(): estimates large covariance matrices in approximate factor models by thresholding principal orthogonal complements
	"dplyr" 
	### dplyr::%>%: loads the infix operator
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

##############################
### Simulation Study Setup ###
##############################

INPUT_ADDRESS <- OUTPUT_ADDRESS <- "..."

SET_NO <- 1

SET_UP <- matrix(c(
			12, 0.5, ### study 3, p = 300
			12, 1.0, ### study 3, p = 300
			12, 1.5, ### study 3, p = 300
			24, 0.5, ### study 3, p = 600
			24, 1.0, ### study 3, p = 600
			24, 1.5  ### study 3, p = 600
			), 
			nrow = 6, ncol = 2, byrow = TRUE)
### scale_p_vec
### scale_kappa, effect size

M <- 1
n_vec <- 100
### M by 1
n <- sum(n_vec)
### 1 by 1
reps_max <- 1e3
### number of replications for Monte Carlo simulations
alpha_level <- 0.05
### nominal significance level
log_t_threshold_vec <- - seq(2, 7, length.out = 200)
### 200 by 1
t_threshold_vec <- exp(log_t_threshold_vec)
### 200 by 1

### create the population mean and UB covariance matrix ###
scale_p_vec <- SET_UP[SET_NO, 1]
scale_kappa <- SET_UP[SET_NO, 2]
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
Sig_C_mat_0 <- diag(diag(Sig_A_mat_0) + diag(Sig_B_mat_0))
### K by K
Sigma_mat_0 <- BLOCK_HADAMARD_PRODUCT(A_mat = Sig_A_mat_0, B_mat = Sig_B_mat_0, p_vec = p_vec)
### p by p
Psi_mat_0 <- BLOCK_HADAMARD_PRODUCT(A_mat = diag(1 / sqrt(diag(Sig_C_mat_0))) %*% Sig_A_mat_0 %*% diag(1 / sqrt(diag(Sig_C_mat_0))), B_mat = diag(1 / sqrt(diag(Sig_C_mat_0))) %*% Sig_B_mat_0 %*% diag(1 / sqrt(diag(Sig_C_mat_0))), p_vec = p_vec)
### Psi_mat_0 <- cov2cor(Sigma_mat_0)
### p by p
v_short_vec <- (n - 1) * p_vec * (diag(Sig_A_mat_0) + diag(Sig_B_mat_0)) ^ 2 / (diag(Sig_A_mat_0) ^ 2 + p_vec * diag(Sig_B_mat_0) ^ 2 + 2 * diag(Sig_A_mat_0) * diag(Sig_B_mat_0))
### K by 1
v_vec <- rep(v_short_vec, times = p_vec)
### p by 1

mu_vec_0 <- rep(0, p)
### p by 1
for(k in 1 : K){
	if(k == 1){
		mu_vec_0[c(1, 2, 3)] <- 1
	} else {
		mu_vec_0[(c(1, 2, 3) + cumsum(p_vec)[k - 1])] <- 1
	}
}
### (3K) non-zero mean components
mu_vec_0 <- mu_vec_0 * scale_kappa * sqrt(diag(Sigma_mat_0)) / sqrt(n)
### p by 1
false_null_index_vec <- which(mu_vec_0 != 0)
### p by 1

set.seed(2025)
res_TRUE <- res_POET <- res_UB <- K_hat_vec <- C_hat_vec <- c()
reps <- 1
pb <- txtProgressBar(min = 1, max = reps_max, style = 3)
while(reps <= reps_max){
	
	setTxtProgressBar(pb, reps)
	### show the progress bar
	
	tryCatch({	
				
		X_mat <- rmvnorm(n = n, mean = mu_vec_0, sigma = Sigma_mat_0)
		### n by p
		X_bar_vec <- apply(X_mat, 2, mean)
		### p by 1
		S_mat <- cov(X_mat)
		### p by p
		res_AB <- BEST_UNBIASED_ESTIMATOR(S_mat = S_mat, p_vec = p_vec)
		A_mat_est <- res_AB$A_mat
		### K by K
		B_mat_est <- res_AB$B_mat
		### K by K
		C_mat_est <- diag(diag(A_mat_est) + diag(B_mat_est))
		### K by K
		D_mat_est <- BLOCK_HADAMARD_PRODUCT(A_mat = diag(sqrt(diag(C_mat_est))), B_mat = matrix(0, K, K), p_vec = p_vec)
		### p by p
		T_vec <- sqrt(n) * drop(solve(D_mat_est) %*% X_bar_vec)
		### p by 1
		
		### the proposed estimate ###
		Psi_mat_est_UB <- BLOCK_HADAMARD_PRODUCT(A_mat = diag(1 / sqrt(diag(C_mat_est))) %*% A_mat_est %*% diag(1 / sqrt(diag(C_mat_est))), B_mat = diag(1 / sqrt(diag(C_mat_est))) %*% B_mat_est %*% diag(1 / sqrt(diag(C_mat_est))), p_vec = p_vec)
		### p by p
		
		res_pfa_est_UB <- ESTIMATE_FDP(
				est_method = "UB", 
				     Z_vec = T_vec, 
					 v_vec = v_vec, 
				 Sigma_mat = Psi_mat_est_UB, 
		   t_threshold_vec = t_threshold_vec, 
		        reg_method = "L1", 
				       eps = .05, 
			###	   kappa_0 = K, 
			   plot_method = NULL)

		res_UB <- rbind(res_UB, EXTRACT_RAW_ADJ_FDP(pfa_object = res_pfa_est_UB, cutoff_vec = t_threshold_vec, false_null_index_vec = false_null_index_vec))
	
		### the "true" estimate ###
		
		res_pfa_TRUE <- ESTIMATE_FDP(
				est_method = "general", 
				     Z_vec = sqrt(n) * X_bar_vec, 
					 v_vec = NULL, 
				 Sigma_mat = Sigma_mat_0, 
		   t_threshold_vec = t_threshold_vec, 
		        reg_method = "L1", 
				       eps = .05, 
			###	   kappa_0 = K, 
			   plot_method = NULL)
			   
		res_TRUE <- rbind(res_TRUE, EXTRACT_RAW_ADJ_FDP(pfa_object = res_pfa_TRUE, cutoff_vec = t_threshold_vec, false_null_index_vec = false_null_index_vec))
	
		### the POET estimate ###		
		X_mat_cent <- scale(x = X_mat, center = TRUE)
		### n by p
		K_hat <- POET::POETKhat(Y = X_mat_cent)$K1HL
		C_hat <- POET::POETCmin(Y = X_mat_cent, K = K_hat, thres = "soft", matrix = "vad")
		K_hat_vec[reps] <- K_hat
		C_hat_vec[reps] <- C_hat
		res_est_POET <- POET::POET(Y = t(X_mat_cent), K = K_hat, C = C_hat, thres = "soft", matrix = "vad") 
		### Y is p by n with zero row mean

		res_pfa_est_POET <- ESTIMATE_FDP(
				est_method = "general", 
				     Z_vec = sqrt(n) * X_bar_vec, 
					 v_vec = NULL, 
				 Sigma_mat = res_est_POET$SigmaY, 
		   t_threshold_vec = t_threshold_vec, 
		        reg_method = "L1", 
				       eps = .05, 
			###	   kappa_0 = K, 
			   plot_method = NULL)
			   
		res_POET <- rbind(res_POET, EXTRACT_RAW_ADJ_FDP(pfa_object = res_pfa_est_POET, cutoff_vec = t_threshold_vec, false_null_index_vec = false_null_index_vec))
			
		### cat(' repetitions:', reps, "\r")
		reps <- reps + 1
	}, error = function(e){})
}

TABLE_SUMMARY(res_TRUE)
TABLE_SUMMARY(res_UB)
TABLE_SUMMARY(res_POET)
summary(K_hat_vec)
summary(C_hat_vec)

save.image(paste(OUTPUT_ADDRESS, paste("S3_No", SET_NO, "Dim", p, "Effect", scale_kappa, "UB.RData", sep = "_"), sep = "/"))	
