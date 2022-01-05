#Produces m nearest neighbors of the ith point in location s
myknn <- function(i,s,m){
  if(m>=(i-1)) im<-1:(i-1)
  else
  {
    dist=cdist(s[c(1,i),],s[c(1,1:(i-1)),])[-1,-1]
    im<-sort(order(dist)[1:m])
  }
  return(im)
}

ellK <- function (K, S, n=1)
{
  value <- (n/2) * (as.numeric(determinant(K,logarithm = TRUE)$mod) - sum(rowSums(K * S)))
  return(value)
}

matern <- function (u, phi, kappa) 
{
  if (is.vector(u)) 
    names(u) <- NULL
  if (is.matrix(u)) 
    dimnames(u) <- list(NULL, NULL)
  uphi <- u/phi
  uphi <- ifelse(u > 0, (((2^(-(kappa - 1)))/ifelse(0, Inf, 
                                                    gamma(kappa))) * (uphi^kappa) * besselK(x = uphi, nu = kappa)), 
                 1)
  uphi[u > 600 * phi] <- 0
  return(uphi)
}

nngp_likelihood<-function(S,w,mi,q,nc){
  
  #joint covariances of each location with their m-nearest neighbors
  if(q==1){ind <- lapply(2:n, function(x){rbind(c(x,imvec[[x-1]]))})
  } else{
    ind <- lapply(2:n, function(x){(cbind(seq(x,(q-1)*n+x,length=q),sapply(imvec[[x-1]],function(i){seq(i,(q-1)*n+i,length=q)})))})
  }
  
  Cilist=lapply(2:n,function(i) S[as.numeric(ind[[i-1]]),as.numeric(ind[[i-1]])])
  
  #joint precision matrices of m-nearest neighbors for each location
  F1 = solve(S[as.numeric(ind[[1]]),as.numeric(ind[[1]])][c(1:q),c(1:q)])
  ind1 = seq(1,((q-1)*n+1),length=q)
  lik1 =  0.5*as.numeric(log(det(F1)) - 0.5* t(w[ind1]) %*% F1 %*% w[ind1])
  lik2 = unlist(lapply(2:n, function(i) {Cim <- S[as.numeric(ind[[i-1]]),as.numeric(ind[[i-1]])]
  wim <- t(chol2inv(chol(Cim[-c(1:q),-c(1:q)]))%*%Cim[-c(1:q),c(1:q)])
  fim <- solve(Cim[c(1:q),c(1:q)]- Cim[c(1:q),-c(1:q)]%*% t(wim))
  0.5*log(det(fim)) - 0.5 * 
    t(w[c(ind[[i-1]][,1])] - 
        wim %*% as.numeric(w[c(ind[[i-1]][,-1])])) %*% (fim) %*% (w[c(ind[[i-1]][,1])] - wim %*% as.numeric(w[c(ind[[i-1]][,-1])]))}))
  
  return(sum(lik2) + lik1)
}

fill.offdiagonal.one <- function(theta,m){
  clq.match <- which(unlist(lapply(clqs,function(x){all(!is.na(match(as.numeric(clqs_2[[m]]),as.numeric(x))))}))>0)
  sep.match <- which(unlist(lapply(seps,function(x){all(!is.na(match(as.numeric(clqs_2[[m]]),as.numeric(x))))}))>0)
  clq.ind <- lapply(clqs[clq.match],function(x){match(as.numeric(clqs_2[[m]]),as.numeric(x))})
  sep.ind <- lapply(seps[sep.match],function(x){match(as.numeric(clqs_2[[m]]),as.numeric(x))})
  
  v <- sort(clqs_2[[m]])
  sig <- sqrt(sigmahat.mat[v[1],v[1]] * sigmahat.mat[v[2],v[2]]) *( (phihat.mat[v[1],v[1]]^nuhat.mat[v[1],v[1]]) * (phihat.mat[v[2],v[2]]^nuhat.mat[v[2],v[2]])) * ((1/ phihat.mat[v[1],v[2]]) ^(2*nuhat.mat[v[1],v[2]])) * theta[m] 
  sigmahat1.mat <- sigmahat.mat
  sigmahat1.mat[v[1],v[2]] <- sigmahat1.mat[v[2],v[1]] <- sig
  Stemp <-sig *matern(D,phi= 1/phihat.mat[v[1],v[2]], kappa= nuhat.mat[v[1],v[2]])
  
  Stemp.clq <- Slist.clq
  Stemp.sep <- Slist.sep
  Rtemp.clq <- Rlist.clq
  Rtemp.sep <- Rlist.sep
  
  for(i in 1:length(clq.match)){
    v <- clq.ind[[i]]
    idx=c(((v[1]-1)*n+1):(v[1]*n))
    jdx=c(((v[2]-1)*n+1):(v[2]*n))
    Stemp.clq[[clq.match[i]]][idx,jdx] <- Stemp
    Stemp.clq[[clq.match[i]]][jdx,idx] <- Stemp
    Rtemp.clq[[clq.match[i]]][v[1],v[2]] <- Rtemp.clq[[clq.match[i]]][v[2],v[1]] <- theta[m]
  }
  
  if(length(sep.match)>0){
    for(i in 1:length(sep.match)){
      v <- sep.ind[[i]]
      idx=c(((v[1]-1)*n+1):(v[1]*n))
      jdx=c(((v[2]-1)*n+1):(v[2]*n))
      Stemp.sep[[sep.match[i]]][idx,jdx] <- Stemp
      Stemp.sep[[sep.match[i]]][jdx,idx] <- Stemp
      Rtemp.sep[[sep.match[i]]][v[1],v[2]] <- Rtemp.sep[[sep.match[i]]][v[2],v[1]] <- theta[m]
    }
  }
  return(list(Slc=Stemp.clq,Sls=Stemp.sep,Rlc=Rtemp.clq,Rls=Rtemp.sep,sigmahat=sigmahat1.mat))
}

comp.lik.oneedge <- function(t,S.clq,S.sep,R.clq,R.sep){
  
 
  clq.match <- clqmatchedge[[t]]
  sep.match <- sepmatchedge[[t]]
  y=unlist(wl)
  n=length(y)/p
  m = 1
  
  k.store <- list()
  k.sep.store <- list()
  
  max.clq.length <- max(sapply(clqs[clq.match],length))
  
  lclq <- lsep <- NULL
  
  if(max.clq.length > 2){
    pdind.clq <- unlist(lapply(clq.match,function(x){
      slanczos(R.clq[[x]],k=1,kl=1)$val[2]}))
    pdind.sep <- NULL
    if(length(sep.match)>0){
      pdind.sep <- unlist(lapply(sep.match,function(x){
       slanczos(R.sep[[x]],k=1,kl=1)$val[2]}))}
    
    pdind <- c(pdind.clq,pdind.sep)
  } else { 
    pdind <- 1}
  
  if(all(pdind>0)){
    lclq <- unlist(lapply(clq.match,function(l){ 
      varsub <- clqs[[l]]
      sub <- unlist(lapply(varsub,function(x){c(((x-1)*n+1):(x*n))}))
      value <- nngp_likelihood(S=S.clq[[l]],w=w[sub],q=length(clqs[[l]]),mi=mi,nc=4)
      value}))
    
    if(length(sep.match)>0){
      lsep <- unlist(lapply(sep.match,function(l){
        varsub <- seps[[l]]
        sub <- unlist(lapply(varsub,function(x){c(((x-1)*n+1):(x*n))}))
        value <- nngp_likelihood(S=S.sep[[l]],w=w[sub],q=length(seps[[l]]),mi=mi,nc=4)
        value}))
    } else {
      lsep =0
    } 
    val <- sum(lclq) - sum(lsep)
  } else {
    val <- -10^26
  }
  return(list(lik=-val,lclq=lclq,lsep=lsep))
}

decomp_ips_par <- function(S,p,e=1e-3,clqs=clqs, seps=seps){
  k.store <- list()
  k.sep.store <- list()
  n <- ncol(S)/p
  S <- (S + t(S))/2
  
  kclq <- foreach(l=1:length(clqs),.combine='+',.export=c("clqs","seps"),.packages = "FastGP") %do%{
    varsub <- clqs[[l]]
    sub <- unlist(lapply(varsub,function(x){c(((x-1)*n+1):(x*n))}))
    kdummy <- matrix(0,ncol=n*p,nrow=n*p)
    kdummy[sub,sub]=rcppeigen_invert_matrix(S[sub,sub])
    kdummy
  }
  
  ksep <- foreach(l=2:length(seps),.combine='+',.export=c("clqs","seps"),.packages = "FastGP") %do%
  {
    varsub <- seps[[l]]
    sub <- unlist(lapply(varsub,function(x){c(((x-1)*n+1):(x*n))}))
    kdummy <- matrix(0,ncol=n*p,nrow=n*p)
    kdummy[sub,sub] <- rcppeigen_invert_matrix(S[sub,sub])
    kdummy
  }
  K <- kclq - ksep 
  return((K+t(K))/2)
}
