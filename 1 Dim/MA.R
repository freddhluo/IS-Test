n = 50
ncut = 100
rho = 0.5
# Generate error eta_t
sim.error = function(dist){
  if (dist == 1){
    eta = rnorm(n + ncut)
  } else if (dist == 2){
    eta = rt(n + ncut, df = 5)
  } else if (dist == 3){
    z = runif(n + ncut)
    I_z1 = (z<0.5)*1
    I_z2 = (z>=0.5)*1
    temp1 = rnorm(n + ncut, -1, 1)
    temp2 = rnorm(n + ncut, 1, 1)
    eta = temp1 * I_z1 + temp2 * I_z2
  } else if (dist == 4){
    eta = rchisq(n + ncut, 2)
  } else if (dist == 5){
    z = runif(n + ncut)
    eta = -z^(-0.001) + (1-z)^(-0.13)
  } else if (dist == 6){
    z = runif(n + ncut)
    eta = -z^(-0.0001) + (1-z)^(-0.17)
  }
  mu = mean(eta)
  sd = sd(eta)
  eta = (eta - mu) / sd
  return(eta)
}
# eta = sim.error(1)

sim.MA = function(eta, rho){
  Y = rep(0, n + ncut)
  Y[1] = eta[1]
  for (t in 2:(n + ncut)){
    Y[t] = rho * eta[t-1] + eta[t]
  }
  return(Y[(ncut+1):(ncut + n)])
}

IS = function(X){
  sum1s = 0
  sum2s = 0
  for (i in 1:n){
    sum2s = sum2s + abs(X[i])
    for (j in 1:n){
      sum1s = sum1s + abs(X[i] + X[j]) - abs(X[i] - X[j])
    }
  }
  nIS = 1 / 2 / n * sum1s / sum2s
  return(nIS)
}

test = function(err.id){
  # simulate MA(1) data with different error dist.
  eta = sim.error(err.id)
  Y = sim.MA(eta, rho)
  
  # fit MA(1)
  fit = arima(x = Y, order = c(0,0,1), include.mean = FALSE)
  X = as.numeric(fit$residuals)
  
  ###################### IS test ######################
  nIS = IS(X)
  
  nB = 1000
  bootssample = NULL
  for (b in 1:nB){
    wt = (rbinom(n,size = 1, prob = 0.5) - 0.5) * 2
    X_b = wt * X
    nIS_b = IS(X_b)
    
    bootssample = c(bootssample, nIS_b)
  }
  pval = sum((bootssample - nIS) > 0) / length(bootssample)
  
  ###################### CS test ######################
  T0 = n
  e_hat = X
  
  # e_hat: length T error
  W = function(x, e_hat){
    temp = (sum(e_hat <= x) - sum(-e_hat <= x)) / sqrt(T0)
    return(temp)
  }
  
  # Gaussian kernel density estimation
  sigma = sd(e_hat)
  h = 1.06 * sigma * T0^(-1/5)
  
  f = function(x, e_hat){
    n = length(e_hat)
    # temp = 0
    # for (i in 1:n){
    #   temp = temp + 1 / n / h * dnorm((x - e_hat[i]) / h)
    # }
    list = lapply(e_hat,function(y){1 / n / h * dnorm((x - y) / h)})
    temp = sum(as.numeric(list))
    # temp[temp < 1e-4] = 1e-4
    return(temp)
  }
  g = function(x, e_hat){
    # h0 = sqrt(2.2e-16) * x
    h0 = 0.01
    # temp = (-f(x + 2 * h0, e_hat) + 8 * f(x + h0, e_hat) 
    #   - 8 * f(x - h0, e_hat) + f(x - 2* h0, e_hat)) / 12 / h0/ f(x, e_hat)
    temp = (f(x + h0, e_hat) - f(x - h0, e_hat)) / (2 * h0)
    return(temp)
  }
  A1 = function(y, e_hat){
    sum = 0
    for (t in 1:T0){
      sum = sum + g(e_hat[t], e_hat) * (e_hat[t] <= y) -
        g(-e_hat[t], e_hat) * (-e_hat[t] <= y)
      # print(c(t, sum))
    }
    return(sum / sqrt(T0))
  }
  A2 = function(y, e_hat){
    sum = 0
    for (t in 1:T0){
      sum = sum + g(e_hat[t], e_hat) * (e_hat[t] >= y) -
        g(-e_hat[t], e_hat) * (-e_hat[t] >= y)
    }
    return(sum / sqrt(T0))
  }
  f_int1 = function(z){
    return(g(z, e_hat)^2 * f(z, e_hat))
  }
  integrate_sum = function(f, lower, upper){
    a = lower
    b = upper
    n = 100
    dx = (b - a) / n
    # sum = 0
    # for (i in 1:n){
    #   x = a + i * dx
    #   sum = sum + f(x) * dx
    # }
    l_temp = seq(a + dx, b, by = dx)
    sum_temp = lapply(l_temp, function(y){f(y) * dx})
    out = list(value = sum(as.numeric(sum_temp)))
    # out = list(value = sum)
    return(out)
  }
  B1 = function(y, e_hat){
    l = length(y)
    list = NULL
    for (i in 1:l){
      temp = integrate_sum(f = f_int1, lower = -5, upper = y[i])$value
      list = c(list, 1 / temp)
    }
    # temp = integrate_sum(f = f_int1, lower = -10, upper = y)$value
    # return(1 / temp)
    return(list)
  }
  B2 = function(y, e_hat){
    l = length(y)
    list = NULL
    for (i in 1:l){
      temp = integrate_sum(f = f_int1, lower = y[i], upper = 5)$value
      list = c(list, 1 / temp)
    }
    return(list)
    # temp = integrate_sum(f = f_int1, lower = y, upper = 10)$value
    # return(1 / temp)
  }
  h_neg = function(y){
    return(g(y, e_hat) * f(y, e_hat) *
             B1(y, e_hat) * A1(y, e_hat))
  }
  h_pos = function(y){
    return(g(y, e_hat) * f(y, e_hat) *
             B2(y, e_hat) * A2(y, e_hat))
  }
  C1 = function(x, e_hat){
    # return(integrate(f = h_neg, lower = x, upper = 0, rel.tol = 1e-3)$value)
    return(integrate_sum(f = h_neg, lower = x, upper = 0)$value)
  }
  C2 = function(x, e_hat){
    # return(-integrate(f = h_pos, lower = 0, upper = x, rel.tol = 1e-3)$value)
    return(-integrate_sum(f = h_pos, lower = 0, upper = x)$value)
  }
  ST = function(x, e_hat){
    if (x<=0){
      temp = W(x, e_hat) - W(0, e_hat) + C1(x, e_hat)
    }
    else{
      temp = W(x, e_hat) - W(0, e_hat) + C2(x, e_hat)
    }
    return(temp)
  }
  
  e_hat_2 = c(e_hat, -e_hat)
  l_e = length(e_hat_2)
  #----- method 1 -----#
  CS = 0
  for (i in 1:l_e){
    temp = abs(ST(e_hat_2[i], e_hat))
    if (temp > CS){CS = temp}
    # print(i)
  }
  
  ######################
  return(c(pval, CS))
}

func = function(cnt){
  p1 = test(1)
  p2 = test(2)
  p3 = test(3)
  p4 = test(4)
  p5 = test(5)
  p6 = test(6)
  return(c(p1, p2, p3, p4, p5, p6))
}

# ---------- Use foreach and doSNOW package ---------- #
library(foreach)
library(doSNOW)
nrep = 100
cl <- makeCluster(16)
registerDoSNOW(cl)
pb = txtProgressBar(max = nrep, style = 3)
progress <- function(n) setTxtProgressBar(pb, n)
opts = list(progress = progress)
result = foreach(cnt = 1:nrep,
                 .combine = 'rbind',
                 .options.snow = opts) %dopar% {
                   tryCatch(func(cnt),error = function(e) return(NA))
                 }


close(pb)
stopCluster(cl)

eval = function(num){
  temp = c(sum((result[,num] - 0.05) < 0) / nrep)
  return(temp)
}
eval2 = function(num){
  temp = c(sum((result[,num] - 2.21) > 0) / nrep)
}
c(eval(1), eval(3), eval(5), eval(7), eval(9), eval(11))
c(eval2(2), eval2(4), eval2(6), eval2(8), eval2(10), eval2(12))


