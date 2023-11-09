library(mvnTest) # Test for normality
library(MVN) # Test for normality
library(energy) # Test for normality
library(mvtnorm)
library(Matrix)
library(MTS)
library(progress)
library(pryr)
library(compositions)
library(foreach)
library(doSNOW)

library(ccgarch)
library(DEoptim)
library(fMultivar) # rcauchy2d
library(statmod) # gauss.quad() used

library(sn)

################### Functions ################### 
# Tools
getDim <- function(x){
  if(is.array(x)){
    n <- dim(x)[1]; dimen <- dim(x)[2]
  }else{
    x <- array(x)
    n <- dim(x)[1]; dimen <- 1
  }
  result <- list("n" = n, "dim" = dimen)
  return(result)
}
find_median_distance <- function(Z){
  
  if(is.data.frame(Z)){
    Z = data.matrix(Z)
  }else{
    Z = as.array(Z)
  }
  size1 <- dim(Z)[1]
  size2 <- dim(Z)[2]
  
  # if size of Z is greater than 100, randomly sample 100 points
  if(size1 > 100){
    if(is.na(size2)){
      Zmed <- Z[sample(size1,100)]
    }else{
      Zmed <- Z[sample(size1,100),]
    }
    size1 = 100
  }else{
    Zmed <- Z
  }
  
  Zmedsq <- Zmed * Zmed;
  if(is.na(dim(Z)[2]))
    G <- Zmedsq
  else
    G <- rowSums(Zmedsq)
  
  # Create row/col repeated matrices
  Q <- rep.col(G,size1)
  R <- rep.row(t(G),size1)
  
  dists <- Q + R - 2 * Zmed %*% t(Zmed)
  dists[lower.tri(dists, diag = TRUE)] = 0
  dists <- array(dists,dim=c(size1^2,1))
  median_dist <- median(dists[dists > 0 ])
  
  return(median_dist)
}
rep.col<-function(x,n){
  matrix(rep(x,each=n), ncol=n, byrow=TRUE)
}
rep.row<-function(x,n){
  matrix(rep(x,each=n),nrow=n)
}
repmat <- function(X,a=1,b=1){
  rows <- dim(X)[1]
  cols <- dim(X)[2]
  if(is.null(cols))
    cols <- 1
  rowRep <- matrix(rep(t(X),a),ncol = cols, byrow = TRUE)
  newX <- matrix(rep(rowRep, b),ncol=cols*b)
  return(newX)
}

d = 5

# ita: d x n
sim.VAR0 = function(ita, A){
  Y = matrix(0, nrow = d, ncol = n + ncut) # d x n
  for (t in (VAR.p+1):(n+ncut)){
    sum = rep(0, d)
    for (i in 1:VAR.p){
      sum = sum + A[,,i] %*% Y[,t-i]
    }
    Y[,t] = sum + ita[,t]
  }
  return(Y[,(ncut+1):(n+ncut)])
}
sim.VAR.par0 = function(ita, coef, order){
  Y = matrix(0, nrow = d, ncol = n + ncut) # d x n
  for (t in (order+1):(n+ncut)){
    sum = rep(0, d)
    for (i in 1:order){
      sum = sum + coef[[i]] %*% Y[,t-i]
    }
    Y[,t] = sum + ita[,t]
  }
  return(Y[,(ncut+1):(n+ncut)])
}
sim.VAR.par1 = function(ita, coef, order){
  Y = matrix(0, nrow = d, ncol = n - order) # d x n
  for (t in (order+1):(n - order)){
    sum = rep(0, d)
    for (i in 1:order){
      sum = sum + coef[[i]] %*% Y[,t-i]
    }
    Y[,t] = sum + ita[,t]
  }
  return(Y[,(order+1):(n-order)])
}
alpha = 15
xi = -sqrt(2*alpha^2/(pi*(1+alpha^2)-2*alpha^2))
omega = 1/sqrt(1-2/pi*alpha^2/(1+alpha^2))
lambda = 1
# temp = (1-lambda) * rnorm(10000) + lambda * rsn(10000,xi,omega,alpha)

GARCH_d = function(dist){
  # Initialization
  if (dist == 'N'){
    ita = t(rmvnorm(n + ncut, mean = rep(0, d), sigma = diag(d), method = "chol"))
  } else if (dist == 't'){
    ita = t(rmvt(n = n + ncut, delta = rep(0, d), sigma = (nu-2)/nu * diag(d),  df = nu))
  } else if (dist == 'N+t'){
    ita = t(((1 - lambda) * rmvnorm(n + ncut, mean = rep(0,d), sigma = diag(d), method = "chol") +
               lambda * rmvt(n = n + ncut, delta = rep(0,d), sigma = (nu - 2) / nu * diag(d), df = nu)) / 
              sqrt(lambda^2 + (1 - lambda)^2))
  } else if (dist == 'N+logN'){
    temp = t(matrix(rlnorm.rplus(n + ncut, meanlog = log(rep(0.3, d)), varlog = diag(d)), nrow = n + ncut))
    temp = t(msqrt(var(t(temp)))$invsqrt %*% (temp - rowMeans(temp)))
    ita = t(((1 - lambda) * rmvnorm(n + ncut, mean = rep(0,d), sigma = diag(d), method = "chol") +
               lambda * temp) / 
              sqrt(lambda^2 + (1 - lambda)^2))
  } else if (dist == 'SN'){
    ita = t(rmsn(n + ncut, dp = DP))
  } else if (dist == 'ST'){
    ita = t(rmst(n + ncut, dp = DP_ST))
  } else if (dist == 'N+SN'){
    temp1 = (1-lambda) * rnorm(n + ncut) + lambda * rsn(n + ncut,xi,omega,alpha)
    temp2 = (1-lambda) * rnorm(n + ncut) + lambda * rsn(n + ncut,xi,omega,alpha)
    temp3 = (1-lambda) * rnorm(n + ncut) + lambda * rsn(n + ncut,xi,omega,alpha)
    temp4 = (1-lambda) * rnorm(n + ncut) + lambda * rsn(n + ncut,xi,omega,alpha)
    temp5 = (1-lambda) * rnorm(n + ncut) + lambda * rsn(n + ncut,xi,omega,alpha)
    ita = rbind(temp1, temp2, temp3, temp4, temp5)
  }
  y = array(rep(0,d*n),dim = c(d,n))
  # y = array(rep(0,d*(n+ncut)),dim = c(d,n+ncut))
  eps_t = rep(0.5, d)
  sigma_ii = rep(0.3, d)
  C_t = R # Constant Correlation Matrix
  # Iteration
  for (t in 1:(n+ncut)){
    sigma_ii = a + B %*% eps_t^2 + G %*% sigma_ii
    D_t = diag(c(sqrt(sigma_ii)))
    sigma_t = D_t %*% C_t %*% D_t
    eps_t = msqrt(sigma_t)$mtxsqrt %*% ita[,t]
    if (t > ncut){y[,t-ncut] = eps_t}}
  # y[,t] = eps_t}
  return(y)
}
GARCH_d. = function(dist, a., B., G., R.){
  # library(MTS)
  # Initialization
  if (dist == 'N'){
    ita = t(rmvnorm(n + ncut, mean = rep(0, d), sigma = diag(d), method = "chol"))
  } else if (dist == 't'){
    ita = t(rmvt(n = n + ncut, delta = rep(0, d), sigma = (nu-2)/nu * diag(d),  df = nu))
  } else if (dist == 'SN'){
    ita = t(rmsn(n = n + ncut, dp = DP))
    # ita = t(rmsn(n = n + ncut, xi = rep(0, d), Omega = diag(3), alpha = alpha))
  } else if (dist == 'N+SN'){
    temp1 = (1-lambda) * rnorm(n + ncut) + lambda * rsn(n + ncut,xi,omega,alpha)
    temp2 = (1-lambda) * rnorm(n + ncut) + lambda * rsn(n + ncut,xi,omega,alpha)
    ita = rbind(temp1, temp2)
  }
  y = array(rep(0,d*(n+ncut)),dim = c(d,n+ncut))
  eps_t = rep(0.5, d)
  sigma_ii = rep(0.3, d)
  C_t = R.
  # Iteration
  for (t in 1:(n+ncut)){
    sigma_ii = a. + B. %*% eps_t^2 + G. %*% sigma_ii
    D_t = diag(c(sqrt(sigma_ii)))
    sigma_t = D_t %*% C_t %*% D_t
    eps_t = msqrt(sigma_t)$mtxsqrt %*% ita[,t]
    # if (t > ncut){y[,t-ncut] = eps_t}
    y[,t] = eps_t
  }
  # detach("package:MTS", unload=TRUE)
  
  return(y)
}
GARCH_d1. = function(ita, a., B., G., R.){
  # library(MTS)
  # Initialization
  y = array(rep(0,d*(n - VAR.p)),dim = c(d,n - VAR.p))
  eps_t = rep(0.5, d)
  sigma_ii = rep(0.3, d)
  C_t = R.
  # Iteration
  for (t in 1:(n - VAR.p)){
    sigma_ii = a. + B. %*% eps_t^2 + G. %*% sigma_ii
    D_t = diag(c(sqrt(sigma_ii)))
    sigma_t = D_t %*% C_t %*% D_t
    eps_t = msqrt(sigma_t)$mtxsqrt %*% ita[,t]
    # if (t > ncut){y[,t-ncut] = eps_t}
    y[,t] = eps_t
  }
  # detach("package:MTS", unload=TRUE)
  
  return(y)
}

Spec_GARCH = function(N){
  if (N == 2.1){
    # Scenario 1 for d = 2
    a <<- c(0.1, 0.1)
    B <<- matrix(c(0.3, 0.1,
                   0.1, 0.2),2,2)
    G <<- matrix(c(0.2, 0.1,
                   0.01, 0.3),2,2)
    R <<- matrix(c(1, 0.5,
                   0.5, 1),2,2)  
  } else if (N == 2.2){
    # Scenario 2 for d = 2 (More persistence for G)
    a <<- c(0.1, 0.1)
    B <<- matrix(c(0.01, 0.01,
                   0.01, 0.01),2,2)
    G <<- matrix(c(0.85, 0.01,
                   0.01, 0.85),2,2)
    R <<- matrix(c(1, 0.5,
                   0.5, 1),2,2)  
  } else if (N == 3.1){
    # Scenario 1 for d = 3
    a <<- rep(0.1, 3)
    B <<- matrix(c(0.3, 0.1, 0.1,
                   0.1, 0.2, 0.1,
                   0.1, 0.1, 0.1), 3, 3)
    G <<- matrix(c(0.2, 0.1, 0.01,
                   0.01, 0.3, 0.1,
                   0.01, 0.01, 0.1), 3, 3)
    R <<- matrix(0.5, d, d) + diag(1-0.5, d)
  } else if (N == 5.1){
    # Scenario 1 for d = 5
    a <<- rep(0.1, 5)
    B <<- matrix(c(0.3, 0.1, 0.1, 0.1, 0.1,
                   0.1, 0.2, 0.1, 0.1, 0.1,
                   0.1, 0.1, 0.25, 0.1, 0.1,
                   0.1, 0.1, 0.1, 0.15, 0.1,
                   0.1, 0.1, 0.1, 0.1, 0.1), 5, 5)
    G <<- matrix(c(0.2, 0.1, 0.01, 0.1, 0.01,
                   0.01, 0.3, 0.1, 0.1, 0.01,
                   0.01, 0.01, 0.1, 0.1, 0.01,
                   0.1, 0.01, 0.01, 0.15, 0.1,
                   0.01, 0.01, 0.1, 0.01, 0.2), 5, 5)
    R <<- matrix(0.5, d, d) + diag(1-0.5, d)
  }
}

# Specify initial parameters for estimation
a_init <<- rep(0.005, d)
B_init <<- diag(rep(0.2 - 0.01, d)) + matrix(0.01, d, d)
G_init <<- diag(rep(0.4 - 0.01, d)) + matrix(0.01, d, d)
R_init <<- diag(rep(1 - 0.1, d)) + matrix(0.1, d, d)

# Repitition Number
nrep = 10000
# Burn-in Obs Generating GARCH Process
ncut = 1000
# d.f. for t dist.
nu = 5
Spec_GARCH(5.1)

# tolerance
tol = .Machine$double.eps^0.25

n = 1000
nB = 1

# skew-normal parameters
# gamma_hat = c(0, -0.6)
# gamma_hat = c(0.15, -0.6)
gamma_hat = c(0, 0.2, -0.2, 0, -0.1)
CP = list(mean = rep(0, d), var.cov = diag(d), gamma1 = gamma_hat)
DP = cp2dp(CP, "SN")


# skew-t parameters
# d = 2
# CP_ST = list(mean = rep(0, d), var.cov = diag(d), gamma1 = gamma_hat, gamma2 = 17.22322)
# DP_ST = cp2dp(CP_ST, "ST")
# DP_ST$nu
# d = 5
# CP_ST = list(mean = rep(0, d), var.cov = diag(d), gamma1 = gamma_hat, gamma2 = 70.55935)
# DP_ST = cp2dp(CP_ST, "ST")
# DP_ST$nu

# gamma_hat = c(0.15, 0.6)
# CP = list(mean = rep(0, d), var.cov = diag(d), gamma1 = gamma_hat)
# DP = cp2dp(CP, "SN")

func = function(cnt){
  ################# Generate Data #################
  Yp = t(GARCH_d('N+SN'))
  ################# Estimation #################
  est_p = tryCatch(eccc.estimation(a = a_init, A = B_init, B = G_init,
                                   R = R_init, dvar = Yp, model = "extended"),
                   error = function(e) {return(NA)},
                   warning = function(w) {return(NA)})
  if (is.na(est_p[1])) {return(NA)}
  
  Yp.res = est_p$std.resid
  
  Rp = est_p$para.mat$R
  
  Rp.invsqrt = tryCatch(msqrt(Rp)$invsqrt,
                        warning = function(w) matrix(NA, d, d),
                        error = function(e) matrix(NA, d, d))
  if (is.na(Rp.invsqrt[1,1])) return(NA)
  
  Xp = Rp.invsqrt %*% t(Yp.res)
  
  #################### IS Test ###################
  norm = function(x){
    return(sqrt(sum(x^2)))
  }
  
  sum1p = 0
  sum2p = 0
  for (i in 1:n){
    sum2p = sum2p + norm(Xp[,i])
    for (j in 1:n){
      sum1p = sum1p + norm(Xp[,i] + Xp[,j]) - norm(Xp[,i] - Xp[,j])
    }
  }
  nIS_p = 1 / 2 * sum1p / sum2p
  
  nB = 1
  for (b in 1:nB){
    wt = (rbinom(n,size = 1, prob = 0.5) - 0.5) * 2
    wt = rbind(wt, wt)
    Xp_b = wt * Xp
    
    sum1p_b = 0
    sum2p_b = 0
    for (i in 1:n){
      sum2p_b = sum2p_b + norm(Xp_b[,i])
      for (j in 1:n){
        sum1p_b = sum1p_b + norm(Xp_b[,i] + Xp_b[,j]) - norm(Xp_b[,i] - Xp_b[,j])
      }
    }
    nIS_p_b = 1 / 2 * sum1p_b / sum2p_b
    
  }
  # pval_s = sum((bootssample_s - nIS_s) > 0) / length(bootssample_s)
  # pval_p = sum((bootssample_p - nIS_p) > 0) / length(bootssample_p)
  # CV = qnorm(1 - 0.05 / 2)^2
  ###################################################
  return(c(nIS_p, nIS_p_b))
}


# result = NULL
# for (cnt in 1:1000){
#   result = rbind(result, func(cnt))
#   print(cnt)
# }
# CV = qnorm(1 - 0.05 / 2)^2
# sum(result[,1] > CV)
# sum(result[,2] > CV)
#################### Size Evaluation ###################
# ---------- Use foreach and doSNOW package ---------- #
n = 1000
nrep = 10000
alpha = 15
xi = -sqrt(2*alpha^2/(pi*(1+alpha^2)-2*alpha^2))
omega = 1/sqrt(1-2/pi*alpha^2/(1+alpha^2))
lambda = 0.2
cl <- makeCluster(40)
registerDoSNOW(cl)
pb = txtProgressBar(max = nrep, style = 3)
progress <- function(n) setTxtProgressBar(pb, n)
opts = list(progress = progress)
result = foreach(cnt = 1:nrep,
                 .combine = 'rbind',
                 .options.snow = opts,
                 .packages = c("mvtnorm",
                               "Matrix",
                               "MTS",
                               "progress",
                               "pryr",
                               "compositions",
                               "ccgarch",
                               "mvnTest",
                               "DEoptim",
                               "fMultivar",
                               "statmod",
                               "MVN",
                               "energy",
                               "sn",
                               "vars")) %dopar% {
                                 tryCatch(func(cnt),error = function(e) return(NA))
                               }


close(pb)
stopCluster(cl)


n.NA = sum(is.na(result[,1])) # NA number
index = which(is.na(result[,1])) # NA row index
if (n.NA > 0){
  temp = result[- index,] # remove NA rows
} else {
  temp = result
}

# CV1 = qnorm(1 - 0.01 / 2)^2
# CV2 = qnorm(1 - 0.05 / 2)^2
# CV3 = qnorm(1 - 0.1 / 2)^2
# cbind(sum(temp[,1]>CV1) / (nrep - n.NA),
#       sum(temp[,2]>CV1) / (nrep - n.NA),
#       sum(temp[,1]>CV2) / (nrep - n.NA),
#       sum(temp[,2]>CV2) / (nrep - n.NA),
#       sum(temp[,1]>CV3) / (nrep - n.NA),
#       sum(temp[,2]>CV3) / (nrep - n.NA))

# CV_s = quantile(temp[,3], probs = c(0.99, 0.95, 0.90))
# CV_p = quantile(temp[,4], probs = c(0.99, 0.95, 0.90))
# c(sum((temp[,1] - CV_s[1]) > 0) / (nrep - n.NA),
#   sum((temp[,1] - CV_s[2]) > 0) / (nrep - n.NA),
#   sum((temp[,1] - CV_s[3]) > 0) / (nrep - n.NA))
# c(sum((temp[,2] - CV_p[1]) > 0) / (nrep - n.NA),
#   sum((temp[,2] - CV_p[2]) > 0) / (nrep - n.NA),
#   sum((temp[,2] - CV_p[3]) > 0) / (nrep - n.NA))


CV_p = quantile(temp[,2], probs = c(0.99, 0.95, 0.90))
c(sum((temp[,1] - CV_p[1]) > 0) / (nrep - n.NA),
  sum((temp[,1] - CV_p[2]) > 0) / (nrep - n.NA),
  sum((temp[,1] - CV_p[3]) > 0) / (nrep - n.NA))

# cat("n =",n, "lambda =",lambda)
# cbind(apply(temp[,1:2]<0.01, 2, sum) / (nrep - n.NA),
#       apply(temp[,1:2]<0.05, 2, sum) / (nrep - n.NA),
#       apply(temp[,1:2]<0.10, 2, sum) / (nrep - n.NA))
