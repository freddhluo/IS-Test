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
  # y = array(rep(0,d*n),dim = c(d,n))
  y = array(rep(0,d*(n+ncut)),dim = c(d,n+ncut))
  eps_t = rep(0.5, d)
  sigma_ii = rep(0.3, d)
  C_t = R # Constant Correlation Matrix
  # Iteration
  for (t in 1:(n+ncut)){
    sigma_ii = a + B %*% eps_t^2 + G %*% sigma_ii
    D_t = diag(c(sqrt(sigma_ii)))
    sigma_t = D_t %*% C_t %*% D_t
    eps_t = msqrt(sigma_t)$mtxsqrt %*% ita[,t]
    # if (t > ncut){y[,t-ncut] = eps_t
    y[,t] = eps_t}
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

detach("package:vars", unload=TRUE)
Spec_GARCH(5.1)
library(vars)

# tolerance
tol = .Machine$double.eps^0.25

# VAR order
VAR.p = 3
# A = array(c(0.3,-0.2,0.65,-0.4,
#             -0.4,-0.6,0.4,0.4,
#             0.5,0.1,0.1,0.5), c(d, d, VAR.p))
A1 = matrix(c(0.2,0.1,-0.2,0, 0,
              0,-0.3,0.1,-0.1,0,
              0,0.05,0.15,0,0,
              -0.05,0,0.1,-0.2,0,
              0.05,-0.1,-0.1,0,0.3),d,d,byrow = T)
A2 = matrix(c(0.25,0.05,0.1,0, 0,
              -0.2,0.1,0.1,0,0,
              0.1,0.1,-0.2,0,0,
              0,0,0,-0.1,0.1,
              0,0,0,0.2,0.3),d,d,byrow = T)
A3 = matrix(c(-0.3,0.05,0.1,0, 0,
              -0.2,0.2,0.1,0,0,
              0.05,-0.1,0.2,0,0,
              0,0,0,-0.15,-0.1,
              0,0,0,0.05,0.2),d,d,byrow = T)
A = array(0, c(d,d,VAR.p))
A[,,1]=A1
A[,,2]=A2
A[,,3]=A3

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
CP_ST = list(mean = rep(0, d), var.cov = diag(d), gamma1 = gamma_hat, gamma2 = 70.55935)
DP_ST = cp2dp(CP_ST, "ST")
# DP_ST$nu

VARest <-
  function (y, p = 1, type = c("const", "trend", "both", "none"),
            season = ULL, exogen = NULL, lag.max = NULL,
            lag.restrict = 0L,
            ic = c("AIC", "HQ", "SC", "FPE")){
    y <- as.matrix(y)
    if (is.null(colnames(y))) {
      colnames(y) <- paste("y", 1:ncol(y), sep = "")
    }
    colnames(y) <- make.names(colnames(y))
    y.orig <- y
    type <- match.arg(type)
    obs <- dim(y)[1]
    K <- dim(y)[2]
    sample <- obs - p
    ylags <- embed(y, dimension = p + 1)[, -(1:K)]
    temp1 <- NULL
    for (i in 1:p) {
      temp <- paste(colnames(y), ".l", i, sep = "")
      temp1 <- c(temp1, temp)
    }
    colnames(ylags) <- temp1
    yend <- y[-c(1:p), ]
    if (type == "const") {
      rhs <- cbind(ylags, rep(1, sample))
      colnames(rhs) <- c(colnames(ylags), "const")
    }
    datamat <- as.data.frame(rhs)
    colnames(datamat) <- colnames(rhs)
    equation <- list()
    restrictions = NULL
    for (i in 1:K) {
      y <- yend[, i]
      equation[[colnames(yend)[i]]] <- lm(y ~ -1 + ., data = datamat)
      if(any(c("const", "both") %in% type)){
        attr(equation[[colnames(yend)[i]]]$terms, "intercept") <- 1
      }
    }
    call <- match.call()
    result <- list(varresult = equation, datamat = data.frame(cbind(yend,
                                                                    rhs)), y = y.orig, type = type, p = p, K = K, obs = sample,
                   totobs = sample + p, restrictions = restrictions, call = call)
    class(result) <- "varest"
    return(result)
  }
# pb <- progress_bar$new(
#   format = "  Percent [:bar] :percent Time :elapsed",
#   total = nrep, clear = FALSE, width= 60)
lambda = 1
# for (count in (1:nrep)){
func = function(cnt){
  ################# Generate Data #################
  # set.seed(count + 666)
  # Generate Sample Data
  # ccc_s = eccc.sim(nobs = n, a = a, A = B, B = G, R = R,
  #                  d.f = Inf, cut = ncut, model = "diagonal")
  # Ys = ccc_s$eps
  # Ys = t(GARCH_d('N'))
  etas = GARCH_d('N')
  Ys = t(sim.VAR0(etas, A))
  # ccc_p = eccc.sim(nobs = n, a = a, A = B, B = G, R = R,
  #                  d.f = nu, cut = ncut, model = "diagonal")
  # Yp = ccc_p$eps
  # Yp = t(GARCH_d('SN'))
  # library(MTS)
  etap = GARCH_d('N+SN')
  Yp = t(sim.VAR0(etap,A))
  ################# Estimation #################
  fit1s = VAR(Ys, p = 3, type = "const")
  fit2s = restrict(x = fit1s, method = "ser", thresh = 1.5)
  Yt_s = residuals(fit2s)
  order_s = fit2s$p[[1]]
  coef_s = Acoef(fit2s)
  
  fit1p = VAR(Yp, p = 3, type = "const")
  fit2p = restrict(x = fit1p, method = "ser", thresh = 1.5)
  Yt_p = residuals(fit2p)
  order_p = fit2p$p[[1]]
  coef_p = Acoef(fit2p)
  
  est_s = tryCatch(eccc.estimation(a = a_init, A = B_init, B = G_init,
                                   R = R_init, dvar = Yt_s, model = "extended"),
                   error = function(e) {return(NA)},
                   warning = function(w) NA)
  if (is.na(est_s[1])){return(NA)}
  
  est_p = tryCatch(eccc.estimation(a = a_init, A = B_init, B = G_init,
                                   R = R_init, dvar = Yt_p, model = "extended"),
                   error = function(e) {return(NA)},
                   warning = function(w) {return(NA)})
  if (is.na(est_p[1])) {return(NA)}
  
  Ys.res = est_s$std.resid
  Yp.res = est_p$std.resid
  
  ################# Estimation self #################
  # k = 3
  # p = d
  # q = k * p + 1
  # T0 = 1000
  # n0 = T0 - k
  # X.reg = NULL
  # Y.reg = NULL
  # for (t in (k+1):T0){
  #   xt = c(1, Y[t-1,], Y[t-2,], Y[t-3,])
  #   yt = Y[t,]
  #   X.reg = cbind(X.reg, xt)
  #   Y.reg = cbind(Y.reg, yt)
  # }
  # X.reg = t(X.reg)
  # Y.reg = t(Y.reg)
  # A_hat = t((solve(t(X.reg) %*% X.reg) %*% t(X.reg)) %*% Y.reg)
  # A0_hat = A_hat[,1]
  # A1_hat = A_hat[,2:(2+p-1)]
  # A2_hat = A_hat[,(2+p):(2+p*2-1)]
  # A3_hat = A_hat[,(2+p*2):(2+p*3-1)]
  
  ################# Estimation self w/o A0 #################
  # k = 3
  # p = d
  # q = k * p
  # T0 = 1000
  # n0 = T0 - k
  # X.reg = NULL
  # Y.reg = NULL
  # for (t in (k+1):T0){
  #   xt = c(Y[t-1,], Y[t-2,], Y[t-3,])
  #   yt = Y[t,]
  #   X.reg = cbind(X.reg, xt)
  #   Y.reg = cbind(Y.reg, yt)
  # }
  # X.reg = t(X.reg)
  # Y.reg = t(Y.reg)
  # A_hat = t((solve(t(X.reg) %*% X.reg) %*% t(X.reg)) %*% Y.reg)
  # A1_hat = A_hat[,1:(1+p-1)]
  # A2_hat = A_hat[,(1+p):(1+p*2-1)]
  # A3_hat = A_hat[,(1+p*2):(1+p*3-1)]
  ########################## M2 #########################
  as = est_s$para.mat$a
  Bs = est_s$para.mat$A
  Gs = est_s$para.mat$B
  Rs = est_s$para.mat$R
  hs = est_s$h
  
  ap = est_p$para.mat$a
  Bp = est_p$para.mat$A
  Gp = est_p$para.mat$B
  Rp = est_p$para.mat$R
  hp = est_p$h
  
  Rs.invsqrt = tryCatch(msqrt(Rs)$invsqrt,
                        warning = function(w) matrix(NA, d, d),
                        error = function(e) matrix(NA, d, d))
  if (is.na(Rs.invsqrt[1,1])) return(NA)
  Rp.invsqrt = tryCatch(msqrt(Rp)$invsqrt,
                        warning = function(w) matrix(NA, d, d),
                        error = function(e) matrix(NA, d, d))
  if (is.na(Rp.invsqrt[1,1])) return(NA)
  
  Xs = Rs.invsqrt %*% t(Ys.res)
  Xp = Rp.invsqrt %*% t(Yp.res)
  
  #################### IS Test ###################
  # Xs = Xs - rowMeans(Xs)
  # rowMeans(Xs)
  # Xp = Xp - rowMeans(Xp)
  # rowMeans(Xp)
  
  norm = function(x){
    return(sqrt(sum(x^2)))
  }
  sum1s = 0
  sum2s = 0
  for (i in 1:(n - order_s)){
    sum2s = sum2s + norm(Xs[,i])
    for (j in 1:(n - order_s)){
      sum1s = sum1s + norm(Xs[,i] + Xs[,j]) - norm(Xs[,i] - Xs[,j])
    }
  }
  nIS_s = 1 / 2 * sum1s / sum2s
  
  sum1p = 0
  sum2p = 0
  for (i in 1:(n - order_p)){
    sum2p = sum2p + norm(Xp[,i])
    for (j in 1:(n - order_p)){
      sum1p = sum1p + norm(Xp[,i] + Xp[,j]) - norm(Xp[,i] - Xp[,j])
    }
  }
  nIS_p = 1 / 2 * sum1p / sum2p
  
  # bootssample_s = NULL
  # bootssample_p = NULL
  nB = 1
  n_var = dim(Xp)[2]
  for (b in 1:nB){
    wt = (rbinom(n_var,size = 1, prob = 0.5) - 0.5) * 2
    wt = rbind(wt, wt, wt, wt, wt)
    Xs_b = wt * Xs
    Xp_b = wt * Xp
    
    itas_b = GARCH_d1.(Xs_b, as, Bs, Gs, Rs)
    Ys_b = t(sim.VAR.par1(itas_b, coef_s, order_s))
    itap_b = GARCH_d1.(Xp_b, ap, Bp, Gp, Rp)
    Yp_b = t(sim.VAR.par1(itap_b, coef_p, order_p))
    ####################################################
    est_var = function(Y, Y_b){
      k = 3
      p = d
      q = k * p
      T0 = dim(Y_b)[1]
      T1 = dim(Y)[1]
      Y = Y[(T1 - T0 + 1):T1,]
      n0 = T0 - k
      X.reg = NULL
      Y.reg = NULL
      for (t in (k+1):T0){
        xt = c(Y_b[t-1,], Y_b[t-2,], Y_b[t-3,])
        yt = Y[t,]
        X.reg = cbind(X.reg, xt)
        Y.reg = cbind(Y.reg, yt)
      }
      X.reg = t(X.reg)
      Y.reg = t(Y.reg)
      A_hat = t((solve(t(X.reg) %*% X.reg) %*% t(X.reg)) %*% Y.reg)
      A1_hat = A_hat[,1:(1+p-1)]
      A2_hat = A_hat[,(1+p):(1+p*2-1)]
      A3_hat = A_hat[,(1+p*2):(1+p*3-1)]
      res = Y.reg - X.reg %*% t(A_hat)
      lreturn = list(A1_hat, A2_hat, A3_hat, res)
      return(lreturn)
    }
    varest_b_s = est_var(Ys, Ys_b)
    varest_b_p = est_var(Yp, Yp_b)
    Yt_s_b = varest_b_s[[4]]
    Yt_p_b = varest_b_p[[4]]
    
    lY = dim(Yt_s_b)[1]
    lh = dim(hs)[1]
    hs = hs[(lh - lY + 1):lh, ]
    hp = hp[(lh - lY + 1):lh, ]
    
    logl_func_s = function(par){
      h = hs[7:997,]
      Yt = Yt_s[7:997,]
      Yt_b = Yt_s_b
      a. = par[1:d]
      B. = matrix(par[(d+1):(d*6)],d,d)
      G. = matrix(par[(d*6+1):(d*11)],d,d)
      R. = matrix(0,d,d)
      par1 = par[(d*11):(d*11 + 15)] # for d = 5
      cnt = 1
      for (j in 1:d){
        for (i in 1:j){
          R.[i,j] = par1[cnt]
          cnt = cnt + 1
          R.[j,i] = R.[i,j]
        }
      }
      logl = 0
      ht = matrix(0,nrow = lY,ncol = d)
      ht[1,] = h[1,]
      for (t in 2:lY){
        ht[t,] = a. + B. %*% (Yt[t-1,])^2 + G. %*% h[t-1,]
        Dt = diag(sqrt(ht[t,]))
        Ht = Dt %*% R. %*% Dt
        logl = logl + t(Yt_b[t,]) %*% solve(Ht) %*% Yt_b[t,] +
          log(det(Ht))
      }
      logl = logl / lY
      return(logl)
    }
    Rslist = c(Rs[upper.tri(Rs,diag = T)])
    theta_s = c(as,Bs,Gs,Rslist)
    ui = diag(length(theta_s))
    optim_b_s = constrOptim(theta = theta_s,
                          f = logl_func_s,
                          grad = NULL,
                          ui = ui,
                          ci = c(rep(0,length(theta_s))))
    par_s = optim_b_s$par
    est_garch_s = function(par){
      h = hs[7:997,]
      Yt = Yt_s[7:997,]
      Yt_b = Yt_s_b
      a. = par[1:d]
      B. = matrix(par[(d+1):(d*6)],d,d)
      G. = matrix(par[(d*6+1):(d*11)],d,d)
      R. = matrix(0,d,d)
      par1 = par[(d*11):(d*11 + 15)] # for d = 5
      cnt = 1
      for (j in 1:d){
        for (i in 1:j){
          R.[i,j] = par1[cnt]
          cnt = cnt + 1
          R.[j,i] = R.[i,j]
        }
      }
      ht = matrix(0,nrow = lY,ncol = d)
      ht[1,] = h[1,]
      eta = matrix(0, nrow = lY, ncol = d)
      Dt1 = diag(sqrt(ht[1,]))
      Ht1 = Dt1 %*% R. %*% Dt1
      eta[1,] = msqrt(Ht1)$invsqrt %*% Yt_b[1,]
      for (t in 2:lY){
        ht[t,] = a. + B. %*% (Yt[t-1,])^2 + G. %*% h[t-1,]
        Dt = diag(sqrt(ht[t,]))
        Ht = Dt %*% R. %*% Dt
        eta[t,] = msqrt(Ht)$invsqrt %*% Yt_b[t,]
      }
      return(eta)
    }
    Ys_b.res = tryCatch(est_garch_s(par_s),
             warning = function(w) matrix(NA, lY, d),
             error = function(e) matrix(NA, lY, d))
    if (is.na(Ys_b.res[1,1])) return(NA)
    # a.s = par_s[1:d]
    # B.s = matrix(par_s[(d+1):(d*6)],d,d)
    # G.s = matrix(par_s[(d*6+1):(d*11)],d,d)
    Rs_b = matrix(0,d,d)
    par1_s = par_s[(d*11):(d*11 + 15)] # for d = 5
    cnt = 1
    for (j in 1:d){
      for (i in 1:j){
        Rs_b[i,j] = par1_s[cnt]
        cnt = cnt + 1
        Rs_b[j,i] = Rs_b[i,j]
      }
    }
    
    
    logl_func_p = function(par){
      h = hp[7:997,]
      Yt = Yt_p[7:997,]
      Yt_b = Yt_p_b
      a. = par[1:d]
      B. = matrix(par[(d+1):(d*6)],d,d)
      G. = matrix(par[(d*6+1):(d*11)],d,d)
      R. = matrix(0,d,d)
      par1 = par[(d*11):(d*11 + 15)] # for d = 5
      cnt = 1
      for (j in 1:d){
        for (i in 1:j){
          R.[i,j] = par1[cnt]
          cnt = cnt + 1
          R.[j,i] = R.[i,j]
        }
      }
      logl = 0
      ht = matrix(0,nrow = lY,ncol = d)
      ht[1,] = h[1,]
      for (t in 2:lY){
        ht[t,] = a. + B. %*% (Yt[t-1,])^2 + G. %*% h[t-1,]
        Dt = diag(sqrt(ht[t,]))
        Ht = Dt %*% R. %*% Dt
        logl = logl + t(Yt_b[t,]) %*% solve(Ht) %*% Yt_b[t,] +
          log(det(Ht))
      }
      logl = logl / lY
      return(logl)
    }
    Rplist = c(Rp[upper.tri(Rp,diag = T)])
    theta_p = c(ap,Bp,Gp,Rplist)
    ui = diag(length(theta_p))
    optim_b_p = constrOptim(theta = theta_p,
                            f = logl_func_p,
                            grad = NULL,
                            ui = ui,
                            ci = c(rep(0,length(theta_p))))
    par_p = optim_b_p$par
    est_garch_p = function(par){
      h = hp[7:997,]
      Yt = Yt_p[7:997,]
      Yt_b = Yt_p_b
      a. = par[1:d]
      B. = matrix(par[(d+1):(d*6)],d,d)
      G. = matrix(par[(d*6+1):(d*11)],d,d)
      R. = matrix(0,d,d)
      par1 = par[(d*11):(d*11 + 15)] # for d = 5
      cnt = 1
      for (j in 1:d){
        for (i in 1:j){
          R.[i,j] = par1[cnt]
          cnt = cnt + 1
          R.[j,i] = R.[i,j]
        }
      }
      ht = matrix(0,nrow = lY,ncol = d)
      ht[1,] = h[1,]
      eta = matrix(0, nrow = lY, ncol = d)
      Dt1 = diag(sqrt(ht[1,]))
      Ht1 = Dt1 %*% R. %*% Dt1
      eta[1,] = msqrt(Ht1)$invsqrt %*% Yt_b[1,]
      for (t in 2:lY){
        ht[t,] = a. + B. %*% (Yt[t-1,])^2 + G. %*% h[t-1,]
        Dt = diag(sqrt(ht[t,]))
        Ht = Dt %*% R. %*% Dt
        eta[t,] = msqrt(Ht)$invsqrt %*% Yt_b[t,]
      }
      return(eta)
    }
    Yp_b.res = tryCatch(est_garch_p(par_p),
                        warning = function(w) matrix(NA, lY, d),
                        error = function(e) matrix(NA, lY, d))
    if (is.na(Yp_b.res[1,1])) return(NA)
    Rp_b = matrix(0,d,d)
    par1_p = par_p[(d*11):(d*11 + 15)] # for d = 5
    cnt = 1
    for (j in 1:d){
      for (i in 1:j){
        Rp_b[i,j] = par1_p[cnt]
        cnt = cnt + 1
        Rp_b[j,i] = Rp_b[i,j]
      }
    }
    
    ####################################################
    # fit1s_b = VAR(Ys_b, p = 3, type = "const")
    # fit2s_b = restrict(x = fit1s_b, method = "ser", thresh = 1.5)
    # Yt_s_b = residuals(fit2s_b)
    # order_s_b = fit2s_b$p[[1]]
    # coef_s_b = Acoef(fit2s_b)
    
    # fit1p_b = VAR(Yp_b, p = 3, type = "const")
    # fit2p_b = restrict(x = fit1p_b, method = "ser", thresh = 1.5)
    # Yt_p_b = residuals(fit2p_b)
    # order_p_b = fit2p_b$p[[1]]
    # coef_p_b = Acoef(fit2p_b)
    
    # est_s_b = tryCatch(eccc.estimation(a = a_init, A = B_init, B = G_init,
    #                                    R = R_init, dvar = Yt_s_b, model = "extended"),
    #                    error = function(e) {return(NA)},
    #                    warning = function(w) NA)
    # if (is.na(est_s_b[1])){return(NA)}
    # 
    # est_p_b = tryCatch(eccc.estimation(a = a_init, A = B_init, B = G_init,
    #                                    R = R_init, dvar = Yt_p_b, model = "extended"),
    #                    error = function(e) {return(NA)},
    #                    warning = function(w) {return(NA)})
    # if (is.na(est_p_b[1])) {return(NA)}
    
    # Ys_b.res = est_s_b$std.resid
    # Yp_b.res = est_p_b$std.resid
    
    ########################## M2 #########################
    # Rs_b = est_s_b$para.mat$R
    # Rp_b = est_p_b$para.mat$R
    
    Rs_b.invsqrt = tryCatch(msqrt(Rs_b)$invsqrt,
                            warning = function(w) matrix(NA, d, d),
                            error = function(e) matrix(NA, d, d))
    if (is.na(Rs_b.invsqrt[1,1])) return(NA)
    Rp_b.invsqrt = tryCatch(msqrt(Rp_b)$invsqrt,
                            warning = function(w) matrix(NA, d, d),
                            error = function(e) matrix(NA, d, d))
    if (is.na(Rp_b.invsqrt[1,1])) return(NA)
    
    X_bs = Rs_b.invsqrt %*% t(Ys_b.res)
    X_bp = Rp_b.invsqrt %*% t(Yp_b.res)
    n0.b = dim(X_bp)[2]
    
    sum1s_b = 0
    sum2s_b = 0
    for (i in 1:n0.b){
      sum2s_b = sum2s_b + norm(X_bs[,i])
      for (j in 1:n0.b){
        sum1s_b = sum1s_b + norm(X_bs[,i] + X_bs[,j]) - norm(X_bs[,i] - X_bs[,j])
      }
    }
    nIS_s_b = 1 / 2 * sum1s_b / sum2s_b
    
    sum1p_b = 0
    sum2p_b = 0
    for (i in 1:n0.b){
      sum2p_b = sum2p_b + norm(X_bp[,i])
      for (j in 1:n0.b){
        sum1p_b = sum1p_b + norm(X_bp[,i] + X_bp[,j]) - norm(X_bp[,i] - X_bp[,j])
      }
    }
    nIS_p_b = 1 / 2 * sum1p_b / sum2p_b
    
    # bootssample_s = c(bootssample_s, nIS_s_b)
    # bootssample_p = c(bootssample_p, nIS_p_b)
  }
  # pval_s = sum((bootssample_s - nIS_s) > 0) / length(bootssample_s)
  # pval_p = sum((bootssample_p - nIS_p) > 0) / length(bootssample_p)
  # CV = qnorm(1 - 0.05 / 2)^2
  ###################################################
  return(c(nIS_s, nIS_p, 
          nIS_s_b, nIS_p_b))
  # pb$tick()
  # Sys.sleep(1 / 100)
}

# gamma_hat = c(0.15, 0.6)
# CP = list(mean = rep(0, d), var.cov = diag(d), gamma1 = gamma_hat)
# DP = cp2dp(CP, "SN")

# result = NULL
# for (cnt in 1:1000){
#   temp = func(cnt)
#   result = rbind(result, temp)
#   print(c(cnt, temp))
# }
# CV = qnorm(1 - 0.05 / 2)^2
# sum(result[,1] > CV)
# sum(result[,2] > CV)

# n.NA = sum(is.na(result[,1])) # NA number
# index = which(is.na(result[,1])) # NA row index
# if (n.NA > 0){
#   temp = result[- index,] # remove NA rows
# } else {
#   temp = result
# }

# CV_p = quantile(temp[,2], probs = c(0.99, 0.95, 0.90))
# c(sum((temp[,1] - CV_p[1]) > 0) / (nrep - n.NA),
#   sum((temp[,1] - CV_p[2]) > 0) / (nrep - n.NA),
#   sum((temp[,1] - CV_p[3]) > 0) / (nrep - n.NA))
# gamma_hat

#################### Size Evaluation ###################
# ---------- Use foreach and doSNOW package ---------- #
n = 1000
# lambda = 1
nrep = 10000
alpha = 15
xi = -sqrt(2*alpha^2/(pi*(1+alpha^2)-2*alpha^2))
omega = 1/sqrt(1-2/pi*alpha^2/(1+alpha^2))
lambda = 0.5

cl <- makeCluster(80)
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



# KSD Block Test Result
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

CV_s = quantile(temp[,3], probs = c(0.99, 0.95, 0.90))
CV_p = quantile(temp[,4], probs = c(0.99, 0.95, 0.90))
c(sum((temp[,1] - CV_s[1]) > 0) / (nrep - n.NA),
  sum((temp[,1] - CV_s[2]) > 0) / (nrep - n.NA),
  sum((temp[,1] - CV_s[3]) > 0) / (nrep - n.NA))
c(sum((temp[,2] - CV_p[1]) > 0) / (nrep - n.NA),
  sum((temp[,2] - CV_p[2]) > 0) / (nrep - n.NA),
  sum((temp[,2] - CV_p[3]) > 0) / (nrep - n.NA))


# CV_p = quantile(temp[,2], probs = c(0.99, 0.95, 0.90))
# c(sum((temp[,1] - CV_p[1]) > 0) / (nrep - n.NA),
#   sum((temp[,1] - CV_p[2]) > 0) / (nrep - n.NA),
#   sum((temp[,1] - CV_p[3]) > 0) / (nrep - n.NA))
# lambda