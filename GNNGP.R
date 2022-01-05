rm(list=ls())

detachAllPackages <- function() {
  
  basic.packages <- c("package:stats","package:graphics","package:grDevices","package:utils","package:datasets","package:methods","package:base")
  
  package.list <- search()[ifelse(unlist(gregexpr("package:",search()))==1,TRUE,FALSE)]
  
  package.list <- setdiff(package.list,basic.packages)
  
  if (length(package.list)>0)  for (package in package.list) detach(package, character.only=TRUE)
  
}

detachAllPackages()
library(gRim)
library(RBGL)
library(mvtnorm)
library(fields)
#library(matrixcalc)
#library(geoR)
library(gRbase)
library(RandomFields)
library(BRISC)
#library(qpgraph)
library(R.utils)
library(optimx)
library(doParallel)
library(foreach)
library(igraph)
library(purrr)
library(MCMCpack)
library(FastGP)
library(Matrix)
library(tictoc)
library(invgamma)
library(MASS)
library(Rcpp)
library(RcppArmadillo)
library(tictoc)
library(RSpectra)
library(mgcv)
library(gRbase)
library(igraph)
library(tidyverse)
library(partitions)
library(matrixcalc)
library(rdist)
library(cluster) 
library(Matrix)
library(ggplot2)

# Functions to update graph 
source("graph_operations.R")
source("mcmc_functions.R")

# X.train: (n_train * q) matrix for single covariate (training)
# X.test: (n_test * q) matrix for single covariate (test)
# Y.train: (n_train*q) matrix for outcome (training)
# Y.test: (n_train*q) matrix for outcome (test)
# test.sample: List of length q containing missing/test location number for each variable. 
# N: number of MCMC draws
# coords: (n*2) matrix of coordinates
# m: number of nearest neighbors for locations

run_gnngp = function(X.train, X.test, Y.train, Y.test, cooords, m=5, N=5000){
  # Creating initial variables
  p = dim(Y.train)[2]
  n = dim(Y.train)[1] + dim(Y.test)[1]
  test.prop = dim(Y.test)[1]/n
  
  # Estimating marginal materns with BRISC
  M <- list()
  for(i in 1:ncol(w.data)){
    M[[i]] <- BRISC_estimation(coords[-test.sample[[i]],], x=as.matrix(na.omit(X.train[,i])), y=na.omit(Y.train[,i]), n.neighbors = 15, cov.model="exponential")
  }
  
  # location graph
  loc_in <-coords
  imvec <- sapply(2:n,myknn,loc_in,m)
  edge.im <- do.call("rbind",lapply(2:n,function(x){t(sapply(imvec[[x-1]],function(y){c(x,y)}))}) )
  edge.im <- cbind(edge.im[,2],edge.im[,1])
  G_L <- graph_from_edgelist(edge.im)
  G_Lm <- moralize(G_L)
  A_L <- as.matrix(as_adjacency_matrix(G_Lm))
  g_L <- as(A_L[as.numeric(max_cardinality(G_Lm)$alpha),as.numeric(max_cardinality(G_Lm)$alpha)],"graphNEL")
  coloring_L <- as.numeric(sequential.vertex.coloring(g_L)$color[max_cardinality(G_Lm)$alpham])
  U_s <- lapply(1:n,function(x){as.numeric(which(!is.na(unlist(lapply(imvec,function(y){match(x,y)})))))+1})
  rev.imvec <- lapply(1:n,function(x){as.numeric(na.omit(unlist(lapply(imvec,function(y){match(x,y)}))))})
  mi<-c(1:max((m-1),1),rep(m,n-max((m-1),1)-1))
  
  # test. sample.locations
  test.sample.location <- lapply(1:n,function(x){which(unlist(lapply(test.sample,function(t){any(x==t)})))})
  train.sample <- lapply(1:p, function(t){ c(1:n)[!c(1:n) %in% test.sample[[t]]]})
  o.list <- lapply(1:n, function(t){if(length(test.sample.location[[t]])){
    o_t <- as.numeric(!c(1:p) %in% test.sample.location[[t]])
  } else {
    o_t = rep(1,p)}})
  
  # Using estimates to initialize Gibbs sampler
  # Fixing smoothness parameter and not estimating it
  nuhat.mat = matrix(0.5, ncol=p, nrow= p)
  phihat.diag=  unlist(lapply(M,function(x){x$Theta[3]}))
  phihat.mat = diag(phihat.diag)
  phihat.mat0=phihat.mat
  
  for(i in 1:(p-1)){
    for (j in (i+1): p){
      phihat.mat[i,j]= sqrt((phihat.mat[i,i]^2 + phihat.mat[j,j]^2)/2)
      phihat.mat[j,i] = phihat.mat[i,j]
    }
  }
  
  # Initial cross-covariance estimate
  sigmahat.diag=unlist(lapply(M,function(x){x$Theta[1]}))
  sigmahat.mat=diag(sigmahat.diag)
  sigmahat.mat0 =sigmahat.mat
  
  rho <- 0.5
  R_V= (1-rho)*diag(p) + rho*cor(Y.train)
  R <- R_V
  
  for(i in 1:(p-1)){
    for (j in (i+1): p){
      sigmahat.mat[i,j]=  sqrt(sigmahat.mat[i,i] * sigmahat.mat[j,j]) *( (phihat.mat[i,i]^nuhat.mat[i,i]) * (phihat.mat[j,j]^nuhat.mat[j,j])) * ((1/ phihat.mat[i,j]) ^(2*nuhat.mat[i,j])) * R_V[i,j] 
      sigmahat.mat[j,i] = sigmahat.mat[i,j]
    }
  }
  
  # Initial variable graph (just join an edge between variable 1 and 2)
  g <- make_ring(p) %>% delete_edges(edges=1:p)
  g <- add_edges(g,c(1,2))
  jt <- jTree(as(g,"graphNEL"))
  jt.graph <- as.undirected(graph.adjlist(jt$childList,mode="out"))
  jt.edge <- as_edgelist(jt.graph)
  jt$cliques <- lapply(jt$cliques, function(k){sort(as.numeric(k))})
  jt$separators <- lapply(jt$separators, function(k){sort(as.numeric(k))})
  
  # Add remove algo, update adjacency, store adjacency as a sparse matrix
  jT <- list(links=cbind(1:(p-2),2:(p-1)), clqs=jt$cliques, seps = jt$separators)
  clqs <- jT$clqs
  seps <- jT$seps
  clqs_2 <- list()
  psic <- combn(p,2)
  psi.clqs_2 <- split(psic,rep(1:ncol(psic), each = nrow(psic)))
  psi <- cor(Y.train)[lower.tri(cor(Y.train))]
  psi_prior <- psi
  clq.no.singleton <- which(sapply(clqs, length)>1)
  if(length(clq.no.singleton)){
    b <- lapply(clqs[clq.no.singleton],function(x){x<-sort(x);c <- combn(x,2);c})
    b <- reduce(b,cbind) %>% unique(MARGIN=2)
    clqs_2 <- split(b,rep(1:ncol(b), each = nrow(b)))
  }
  g_v <- g
  A_V <- diag(p)
  g_V <- as(A_V[as.numeric(max_cardinality(g_v)$alpha),as.numeric(max_cardinality(g_v)$alpha)],"graphNEL")
  coloring <- as.numeric(sequential.vertex.coloring(g_V)$color[max_cardinality(g_v)$alpham])
  
  # chromatic sample coloring for edges
  ne <- length(clqs_2)
  A_E <- matrix(0,nrow=ne, ncol=ne)
  if(ne >1){
    for(i in 1:(ne-1)){
      for(j in (i+1):ne){
        e <- sort(union(clqs_2[[i]], clqs_2[[j]]))
        A_E[i,j] <- any(sapply(clqs, function(x){setequal(x,e)}))
        A_E[j,i] <- A_E[i,j]
      }
    }
    g_e <- graph_from_adjacency_matrix(A_E,mode="undirected")
    g_E <- as(A_E[as.numeric(max_cardinality(g_e)$alpha),as.numeric(max_cardinality(g_e)$alpha)],"graphNEL")
    coloring_e <- as.numeric(sequential.vertex.coloring(g_E)$color[max_cardinality(g_e)$alpham])
  } else{
    coloring_e <- 0  
  }
  
  # Store which edges belong to which cliques and seaprators
  clqmatchedge <- sepmatchedge <- list()
  if(length(clqs_2)){
    for(t in 1:length(clqs_2)){
      clqmatchedge[[t]] <- which(unlist(lapply(clqs,function(x){all(!is.na(match(as.numeric(clqs_2[[t]]),as.numeric(x))))}))>0)
      sepmatchedge[[t]] <- which(unlist(lapply(seps,function(x){all(!is.na(match(as.numeric(clqs_2[[t]]),as.numeric(x))))}))>0)
    }
  }
  
  # Store which variable belongs to which cliques
  clqmatchvar <- sepmatchvar <- list()
  for(t in 1:p){
    clqmatchvar[[t]] <- which(unlist(lapply(clqs,function(x){all(!is.na(match(as.numeric(t),as.numeric(x))))}))>0)
    sepmatchvar[[t]] <- which(unlist(lapply(seps,function(x){all(!is.na(match(as.numeric(t),as.numeric(x))))}))>0)
  }
  
  # Storing location * variable indices for cliques and separators 
  sam.clq <- lapply(c(1:length(clqs)), function(k){
    q=length(clqs[[k]])
    sam=unlist(lapply(clqs[[k]],function(x){c(((x-1)*n+1):(x*n))}))
    return(sam)})
  
  sam.sep <- lapply(c(2:length(seps)), function(k){
    q=length(seps[[k]])
    sam=unlist(lapply(seps[[k]],function(x){c(((x-1)*n+1):(x*n))}))
    return(sam)})
  
  sam.sep <- append(100, sam.sep)
  
  # Storing neighboring conditioning indices for cliques and separators
  ind.clq <- lapply(c(1:length(clqs)), function(k){
    q=length(clqs[[k]])
    if(q==1){ind <- lapply(2:n, function(x){rbind(c(x,imvec[[x-1]]))})
    } else{
      ind <- lapply(2:n, function(x){(cbind(seq(x,(q-1)*n+x,length=q),sapply(imvec[[x-1]],function(i){seq(i,(q-1)*n+i,length=q)})))})
    }
    return(ind)
  })
  
  ind.sep <- lapply(c(2:length(seps)), function(k){
    if(length(seps[[k]]>0)){
      q=length(seps[[k]])
      if(q==1){ind <- lapply(2:n, function(x){rbind(c(x,imvec[[x-1]]))})
      } else{
        ind <- lapply(2:n, function(x){(cbind(seq(x,(q-1)*n+x,length=q),sapply(imvec[[x-1]],function(i){seq(i,(q-1)*n+i,length=q)})))})
      }
      return(ind)
    }})
  
  ind.sep <- append(100,ind.sep)
  
  
  # Storing clique and separator specific covariance matrices
  Slist.clq <- Slist.sep <- list()
  Rlist.clq <- Rlist.sep <- list()
  
  for(k in 1:length(clqs)){
    comp <- sort(clqs[[k]])
    pc <- length(clqs[[k]])
    sigmahat.sub <- as.matrix(sigmahat.mat[comp,comp])
    phihat.sub <- as.matrix(phihat.mat[comp,comp])
    nu.sub <- as.matrix(nu.mat[comp,comp])
    Stemp <- matrix(nrow=n*pc,ncol=n*pc)
    for (i in 1:pc){
      for(j in i:pc){
        idx=c(((i-1)*n+1):(i*n))
        jdx=c(((j-1)*n+1):(j*n))
        Stemp[idx,jdx] = sigmahat.sub[i,j]*matern(D,phi= 1/phihat.sub[i,j], kappa= nu.sub[i,j])
        Stemp[jdx,idx] = Stemp[idx,jdx]
      }
    }
    Slist.clq[[k]] <- Stemp
    Rlist.clq[[k]] <- R[comp,comp]
    rm(Stemp)
  }
  
  for(k in 2:length(seps)){
    if(length(seps[[k]])>0){
      comp <- sort(seps[[k]])
      pc <- length(seps[[k]])
      sigmahat.sub <- as.matrix(sigmahat.mat[comp,comp])
      phihat.sub <- as.matrix(phihat.mat[comp,comp])
      nu.sub <- as.matrix(nu.mat[comp,comp])
      Stemp <- matrix(nrow=n*pc,ncol=n*pc)
      for (i in 1:pc){
        for(j in i:pc){
          idx=c(((i-1)*n+1):(i*n))
          jdx=c(((j-1)*n+1):(j*n))
          Stemp[idx,jdx] = sigmahat.sub[i,j]*matern(D,phi= 1/phihat.sub[i,j], kappa= nu.sub[i,j])
          Stemp[jdx,idx] = Stemp[idx,jdx]
        }
      }
      Slist.sep[[k]] <- Stemp
      Rlist.sep[[k]] <- R[comp,comp]
      rm(Stemp)
    }
  }
  
  # Creating universal palette for cross-correlation parameters
  theta <- numeric(length(clqs_2))
  for(t in 1:length(clqs_2)){
    t1 <- which(sapply(psi.clqs_2, function(x){setequal(x,clqs_2[[t]])}))
    theta[t] <- psi[t1]
  }
  beta= unlist(lapply(M,function(x){x$Beta}))
  tausq= unlist(lapply(M,function(x){x$Theta[2]}))

  # Initialiazing latent process for Gibbs sampling 
  Yl <- list()
  Xl <- list()
  wl <- list()
  for(i in 1:p){
    Yl[[i]] = Y.train[,i]
    Xl[[i]] = X.train[,i]
    wl[[i]] = numeric(n)
    cmatch <- clqmatchvar[[i]][1]
    imatch <- which(clqs[[cmatch[1]]]==i)
    im <- c(((imatch-1)*n+1):(imatch*n))
    wtemp <- as.numeric(rmvnorm(1,sigma=Slist.clq[[cmatch[1]]][im,im]))
    wl[[i]][-test.sample[[i]]] = wtemp[-test.sample[[i]]]
    wl[[i]][test.sample[[i]]] = wtemp[test.sample[[i]]]
  }
  
  w = unlist(wl)
  
  #  Initial likelihood for cliques and separators
  lik.clq.temp <- mclapply(1:length(clqs),mc.cores=ncore, function(c){
    varsub <- clqs[[c]]
    sub <- unlist(lapply(varsub,function(x){c(((x-1)*n+1):(x*n))}))
    S_Y <- w[sub] %*% t(w[sub])
    
    return(list(S_Y,nngp_likelihood(S=Slist.clq[[c]],w=w[sub], mi=mi, nc=ncore, q=length(clqs[[c]]))))})
  
  if(length(seps)>0){
    lik.sep.temp <- mclapply(2:length(seps),mc.cores=ncore,function(c){
      if(length(seps[[c]]>0)){
        varsub <- seps[[c]]
        sub <- unlist(lapply(varsub,function(x){c(((x-1)*n+1):(x*n))}))
        S_Y <- w[sub] %*% t(w[sub])
        return(list(S_Y,nngp_likelihood(S=Slist.sep[[c]],w=w[sub], mi=mi, nc=ncore, q=length(seps[[c]]))))}})
    
  }
  
  
  lik.clq <- lapply(lik.clq.temp, "[[", 2)
  Sy.clq.list <- lapply(lik.clq.temp, "[[", 1)
  
  lik.sep <- lapply(lik.sep.temp, "[[", 2)
  Sy.sep.list <- lapply(lik.sep.temp, "[[", 1)
  
  llik.w <- sum(unlist(lik.clq)) - sum(unlist(lik.sep))
  
  lik.sep <- append(100,lik.sep)
  Sy.sep.list <- append(100,Sy.sep.list)
  
  rm(lik.clq.temp)
  rm(lik.sep.temp)
  
  # Storing mean for latent spatial process
  mu.list <- lapply(1:n,function(x){unlist(lapply(1:p,function(t){if(t %in% test.sample.location[[x]]){
    0} else {
      k <- which(train.sample[[t]]==x)
      Yl[[t]][k] - Xl[[t]][k] * beta [t]
    }}))})
  
  w = unlist(wl)
  countertau <- countersig <- counterphi <- matrix(nrow=p,ncol=N)
  mcmc.store <- list(betahat=matrix(nrow=N,ncol=p),tausq=tausq0,tausqhat=matrix(nrow=N,ncol=p),rhat=list(),phihat=matrix(nrow=N,ncol=p),sigmahat=matrix(nrow=N,ncol=p),lik=matrix(nrow=N,ncol=2),
                     w=array(dim=c(N,p,n)),psihat=matrix(nrow=N,ncol=(p*(p-1)/2)),
                     ytest=Y.test,ytestpred=array(dim=c(N,p,n*(test.prop))), A.list=list(), rnodes=list(), pd.ind=list(), clq.length=list(), add.counter=list(), add.counter.accept=list(), loglik = matrix(nrow=N,ncol=3))
  mu=rep(0,n*p)
  
  counter <- matrix(0,nrow=length(clqs_2),ncol=N)
  countersig <- counterphi <- matrix(nrow=p,ncol=N)
  mu=rep(0,n*p)
  llik.psi <- 0
  llik.g <- 0
  lik.clq <- list()
  lik.sep <- list()
  Ytest <- lapply(1:p, function(x){rep(NA,n)})
  
  for(j in 1:N){
    tic("totaltime")
    
    # Storing NNGP conditional matrices for each cliques and separators
    
    tic("w_store")
    wimlist.clq=mclapply(1:length(clqs), mc.cores=ncore, function(k){
      q=length(clqs[[k]])
      S = Slist.clq[[k]]
      sam=sam.clq[[k]]
      ind <- ind.clq[[k]]  
      wim <- lapply(2:n, function(i,Cilist,Pilist) {Ci=S[as.numeric(ind[[i-1]]),as.numeric(ind[[i-1]])]
      Pi= chol2inv(chol(Ci[-c(1:q),-c(1:q)]))
      wi = t(Pi%*%Ci[-c(1:q),c(1:q)])
      fi = solve(Ci[c(1:q),c(1:q)]- Ci[c(1:q),-c(1:q)]%*% t(wi))
      return(list(wi,fi,Ci))})
      return(wim)})
    
    wimlist.sep=mclapply(2:length(seps), mc.cores=ncore, function(k){
      if(length(seps[[k]]>0)){
        q=length(seps[[k]])
        S = Slist.sep[[k]]
        sam=sam.sep[[k]]
        ind = ind.sep[[k]]
        wim <- lapply(2:n, function(i,Cilist,Pilist) {Ci=S[as.numeric(ind[[i-1]]),as.numeric(ind[[i-1]])]
        Pi= chol2inv(chol(Ci[-c(1:q),-c(1:q)]))
        wi = t(Pi%*%Ci[-c(1:q),c(1:q)])
        fi = solve(Ci[c(1:q),c(1:q)]- Ci[c(1:q),-c(1:q)]%*% t(wi))
        return(list(wi,fi,Ci))})
        return(wim)}})
    
    wimlist.sep <- append(100,wimlist.sep)
    toc()
    
    # Simulate latent spatial process
    for(k in c(1:length(unique(coloring_L)))){
      tic("one")
      m = which(coloring_L==(k-1))
      w.store <- mclapply(m,mc.cores=ncore, function(t){  
        s <- t
        mu_t = mu.list[[t]]
        o_t = o.list[[t]]
        cond.dist.clq <- lapply(c(1:length(clqs)), function(k,type="Clique"){
          if(type=="Clique"){
            q=length(clqs[[k]])
            S = Slist.clq[[k]]
            sam=sam.clq[[k]]
            ind <- ind.clq[[k]]
          } else {
            q=length(seps[[k]])
            S = Slist.sep[[k]]
            sam=sam.sep[[k]]
            ind = ind.sep[[k]]
          }
          
          w1 = w[sam]
          wimlist=wimlist.clq[[k]]
          
          cond_s <- lapply(1:length(U_s[[s]]), function(x){
            if(s==n){
              res1 <- rep(0,q)
              res2 <- matrix(0,ncol=q,nrow=q)
              return(list(res1,res2))
            } else {t <- U_s[[s]][x]
            l <- rev.imvec[[s]][x] 
            n_t <- imvec[[t-1]][-l]  
            if(length(n_t)==0){
              a_t=w1[as.numeric(ind[[t-1]][,1])]} else{
                a_t = w1[as.numeric(ind[[t-1]][,1])] - wimlist[[t-1]][[1]][,-c(((l-1)*q+1):(l*q))] %*% w1[as.numeric(ind[[t-1]][,-c(1,(l+1))])]
              }
            res1 <- t(wimlist[[t-1]][[1]][,c(((l-1)*q+1):(l*q))]) %*% wimlist[[t-1]][[2]] %*% a_t
            res2 <- t(wimlist[[t-1]][[1]][,c(((l-1)*q+1):(l*q))]) %*% wimlist[[t-1]][[2]] %*% wimlist[[t-1]][[1]][,c(((l-1)*q+1):(l*q))]
            return(list(res1,res2))
            }
          })
          
          if(s==1){
            cond.prec = (Reduce('+', lapply(cond_s,function(x){x[[2]]})) + solve(wimlist[[1]][[3]][c(1:q),c(1:q)]))
            cond.mu.s = Reduce('+', lapply(cond_s,function(x){x[[1]]}))
          } else {
            cond.prec = (Reduce('+', lapply(cond_s,function(x){x[[2]]})) + wimlist[[s-1]][[2]])
            cond.mu.s = (Reduce('+', lapply(cond_s,function(x){x[[1]]})) + wimlist[[s-1]][[2]] %*% wimlist[[s-1]][[1]] %*% w1[as.numeric(ind[[s-1]][,-1])])
          }
          
          S.d.1 <- matrix(0,ncol=p,nrow=p)
          S.d.1[c(clqs[[k]]),c(clqs[[k]])] <- cond.prec
          mu.d.1 <- numeric(length=p)
          mu.d.1[clqs[[k]]] <- as.numeric(cond.mu.s)
          return(list(S.d.1,mu.d.1))
        })
        
        cond.dist.sep <- lapply(c(2:length(seps)), function(k,type="Sep"){
          if(length(seps[[k]]>0)){
            if(type=="Clique"){
              q=length(clqs[[k]])
              S = Slist.clq[[k]]
              sam=sam.clq[[k]]
              ind <- ind.clq[[k]]
            } else {
              q=length(seps[[k]])
              S = Slist.sep[[k]]
              sam=sam.sep[[k]]
              ind = ind.sep[[k]]
            }
            
            w1 = w[sam]
            wimlist=wimlist.sep[[k]]
            
            cond_s <- lapply(1:length(U_s[[s]]), function(x){
              if(s==n){
                res1 <- rep(0,q)
                res2 <- matrix(0,ncol=q,nrow=q)
                return(list(res1,res2))
              } else {t <- U_s[[s]][x]
              l <- rev.imvec[[s]][x] 
              n_t <- imvec[[t-1]][-l]  
              if(length(n_t)==0){
                a_t=w1[as.numeric(ind[[t-1]][,1])]} else{
                  a_t = w1[as.numeric(ind[[t-1]][,1])] - wimlist[[t-1]][[1]][,-c(((l-1)*q+1):(l*q))] %*% w1[as.numeric(ind[[t-1]][,-c(1,(l+1))])]
                }
              res1 <- t(wimlist[[t-1]][[1]][,c(((l-1)*q+1):(l*q))]) %*% wimlist[[t-1]][[2]] %*% a_t
              res2 <- t(wimlist[[t-1]][[1]][,c(((l-1)*q+1):(l*q))]) %*% wimlist[[t-1]][[2]] %*% wimlist[[t-1]][[1]][,c(((l-1)*q+1):(l*q))]
              return(list(res1,res2))
              }
            })
            
            
            if(s==1){
              cond.prec = (Reduce('+', lapply(cond_s,function(x){x[[2]]})) + solve(wimlist[[1]][[3]][c(1:q),c(1:q)]))
              cond.mu.s = Reduce('+', lapply(cond_s,function(x){x[[1]]}))
            } else {
              cond.prec = (Reduce('+', lapply(cond_s,function(x){x[[2]]})) + wimlist[[s-1]][[2]])
              cond.mu.s = (Reduce('+', lapply(cond_s,function(x){x[[1]]})) + wimlist[[s-1]][[2]] %*% wimlist[[s-1]][[1]] %*% w1[as.numeric(ind[[s-1]][,-1])])
            }
            
            S.d.1 <- matrix(0,ncol=p,nrow=p)
            S.d.1[c(seps[[k]]),c(seps[[k]])] <- cond.prec
            mu.d.1 <- numeric(length=p)
            mu.d.1[seps[[k]]] <- as.numeric(cond.mu.s)
            return(list(S.d.1,mu.d.1))
          }})
        
        cond.prec.s <- ((1/tausq)*diag(o_t) + Reduce('+', lapply(cond.dist.clq,function(x){x[[1]]}))- Reduce('+',lapply(cond.dist.sep,function(x){
          if(is.null(x[[1]])){matrix(0,p,p)
          }else{x[[1]]}})))
        cond.sig.s <- solve(cond.prec.s)
        cond.mu.s <- cond.sig.s %*% ( (1/tausq)*mu_t + Reduce('+', lapply(cond.dist.clq,function(x){x[[2]]}))- Reduce('+',lapply(cond.dist.sep,function(x){
          if(is.null(x[[2]])){rep(0,p)
          }else{x[[2]]}})))
        as.numeric(mvrnormArma(1,mu=cond.mu.s,sigma=cond.sig.s))
      })
      print(c(k,m))
      if(length(m)==1){
        wlN <- lapply(1:p, function(x) {v <- wl[[x]]; v[m] <- as.numeric(w.store[[1]])[x]; return(v)})
        wl <- wlN
        if(length(test.sample.location[[m]])>0){
          for(z in test.sample.location[[m]]){Ytest[[z]][m[1]] <- X.test[which(test.sample[[z]]==m[1]),z] * beta[z] + as.numeric(w.store[[1]])[z]+ rnorm(1,sd=tausq[z])}
        }
      } else {
        for(i in 1:length(m)){
          wlN <- lapply(1:p, function(x) {v <- wl[[x]]; v[m[i]] <- as.numeric(w.store[[i]])[x]; v})
          wl <- wlN
          for(z in test.sample.location[[m[i]]]){Ytest[[z]][m[i]] <- X.test[which(test.sample[[z]]==m[i]),z] * beta[z] + as.numeric(w.store[[i]])[z]+ rnorm(1,tausq[z])}
        }
      }
      w <- unlist(wl)
      toc()
    }
    
    # Likelihood update
    tic("lik_update")
    lik.clq.temp <- mclapply(1:length(clqs),mc.cores=ncore,function(c){
      varsub <- clqs[[c]]
      sub <- unlist(lapply(varsub,function(x){c(((x-1)*n+1):(x*n))}))
      S_Y <- w[sub] %*% t(w[sub])
      
      return(list(S_Y,nngp_likelihood(S=Slist.clq[[c]],w=w[sub], mi=mi, nc=ncore, q=length(clqs[[c]]))))})
    
    lik.sep.temp <- mclapply(2:length(seps),mc.cores=ncore, function(c){
      if(length(seps[[c]]>0)){
        varsub <- seps[[c]]
        sub <- unlist(lapply(varsub,function(x){c(((x-1)*n+1):(x*n))}))
        S_Y <- w[sub] %*% t(w[sub])
        return(list(S_Y,nngp_likelihood(S=Slist.sep[[c]],w=w[sub], mi=mi, nc=ncore, q=length(seps[[c]]))))}})
    
    lik.clq <- lapply(lik.clq.temp, "[[", 2)
    Sy.clq.list <- lapply(lik.clq.temp, "[[", 1)
    
    lik.sep <- lapply(lik.sep.temp, "[[", 2)
    Sy.sep.list <- lapply(lik.sep.temp, "[[", 1)
    
    llik.w <- sum(unlist(lik.clq)) - sum(unlist(lik.sep))
    
    lik.sep <- append(100,lik.sep)
    Sy.sep.list <- append(100,Sy.sep.list)
    
    rm(lik.clq.temp)
    rm(lik.sep.temp)
    toc()
    
    tic("corr_update")
    
    # simulate cross-correlation parameters
    g=function(x){log((1+x)/(1-x))}
    gprime=function(x){
      2/(1-x^2)
    }
    ginv = function(x){
      (exp(x)-1)/(exp(x)+1)
    }
    
    if(length(clqs_2)){
      for(k in c(1:length(unique(coloring_e)))){
        m = which(coloring_e==(k-1))
        rup <- mclapply(m,mc.cores = ncore, function(t)
        {lclq <- lsep <- 0
        clqt <- clqmatchedge[[t]] ### checking cliques corresponding to specific correlation
        sept <- sepmatchedge[[t]]
        lclq <- sum(sapply(clqt,function(x){lik.clq[[x]]})) ### summing up clique likelihoods
        if(length(sept)>0){
          lsep <- sum(sapply(sept,function(x){lik.sep[[x]]}))
        }
        lik.v <- -(lclq-lsep)
        r=0
        theta_t = theta[t]
        ita_t=g(theta_t)
        ita_t1 = rnorm(1,ita_t,0.4)
        theta_t1=ginv(ita_t1)
        thetanew <- theta
        thetanew[t] <- theta_t1
        Su=fill.offdiagonal.one(thetanew,t)
        Slnew=list(clq=Su$Slc,sep=Su$Sls)
        Rlnew=list(clq=Su$Rlc,sep=Su$Rls)
        #tic()
        lik.up <- tryCatch(comp.lik.oneedge(t=t,S.clq=Slnew$clq,S.sep=Slnew$sep,R.clq=Rlnew$clq,R.sep=Rlnew$sep),error=function(e){NA})
        #toc()
        lik.v <- c(lik.v,lik.up$lik)
        
        #lik0 <- comp.lik.one(theta = theta,t=t,S=S)
        #theta1 <- theta
        #theta1[t] <- theta_t1
        #lik1 <- comp.lik.one(theta = theta1,t=t,S=S)
        logdiff1 <- (-lik.v[2]+lik.v[1])
        logdiff2 <- log(abs(gprime(theta_t)/gprime(theta_t1))) + dnorm(ita_t1, log = TRUE) - dnorm(ita_t, log=TRUE)
        logdiff <- logdiff1 + logdiff2
        r=min(c(1,exp(logdiff)))
        u=runif(1)
        Slnew <- list(clq=lapply(clqt,function(x){Slnew$clq[[x]]}),sep=lapply(sept,function(x){Slnew$sep[[x]]}))
        Rlnew <- list(clq=lapply(clqt,function(x){Rlnew$clq[[x]]}),sep=lapply(sept,function(x){Rlnew$sep[[x]]}))
        #print(r)
        if(u > r){
          list(NULL)
        } else {
          list(thetanew[t],Slnew,Rlnew,lik.up,lik.v)
        }
        })
        
        for(t in 1:length(m)){
          if(!is.null(rup[[t]][[1]])){
            clqt <- clqmatchedge[[m[t]]]
            sept <- sepmatchedge[[m[t]]]
            theta[m[t]] <- rup[[t]][[1]]
            t1 <- which(sapply(psi.clqs_2, function(x){setequal(x,clqs_2[[m[t]]])}))
            psi[t1] <- rup[[t]][[1]]
            sigmahat.mat <- fill.offdiagonal.one(theta,m[t])$sigma
            for(c in 1:length(clqt)){
              Slist.clq[[clqt[c]]] <- rup[[t]][[2]]$clq[[c]]
              Rlist.clq[[clqt[c]]]<- rup[[t]][[3]]$clq[[c]]
              lik.clq[[clqt[c]]] <- rup[[t]][[4]]$lclq[c]
            }
            if(length(sept)>0){
              for(c in 1:length(sept)){
                Slist.sep[[sept[c]]] <- rup[[t]][[2]]$sep[[c]]
                Rlist.sep[[sept[c]]] <- rup[[t]][[3]]$sep[[c]]
                lik.sep[[sept[c]]] <- rup[[t]][[4]]$lsep[c]
              }
            }
            #counter[m[t],j] <- 1
          }
        }
      }
    }
    
  
    # Creating global palette psi for rJMCMC
    uk <- which(!sapply(psi.clqs_2, function(x){any(sapply(clqs_2,function(y){setequal(x,y)}))}))
    psi[uk] <- sapply(rnorm(length(uk), mean=g(psi_prior[uk])), ginv)
    llik.psi <- sum(sapply(psi, function(x){dnorm(g(x),log = TRUE) - log(abs(gprime(x)))}))
    
    toc()
    
    # update graph
    if(j==1){
      Atemp <- get.adjacency(g_v)
      diag(Atemp) <- 1
    } else {
      Atemp <- mcmc.store$A.list[[j-1]]
    }
    
    mcmc.store$add.counter[[j]] <- numeric()
    mcmc.store$add.counter.accept[[j]] <- numeric()
    
    tic("graph move")
    
    for(graph.k in 1){
      
      add <- sample(c(0,1),prob=c(0.5,0.5),size=1)
      mcmc.store$add.counter[[j]][graph.k] <- as.numeric(add==1)
      
      if(add==1){
        Jprime <- add.edge(jT)
        qJJprime <- Jprime$prob
        if(Jprime$prob==0){J <- jT
        Atemp <- tryCatch(Atemp, error=function(e) NULL)
        } else{ qJprimeJ = add.reverse.prob(Jprime)
        u1= runif(1)
        qratio = qJJprime/qJprimeJ
        if(u1 >= qratio){J <- jT
        Atemp <- tryCatch(Atemp, error=function(e) NULL)
        } else{ 
          J <- jT
          muJ = countjtrees(J)
          muJprime= countjtrees(Jprime$J)
          
          clq.add.lik <- sep.add.lik <- clq.del.lik <- sep.del.lik <- list()
          
          if(!list.check(Jprime$clq.add)){
            clq.add.lik <- lapply(1:length(Jprime$clq.add),function(c){
              varsub <- Jprime$clq.add[[c]]
              if(length(varsub)){sub <- unlist(lapply(varsub,function(x){c(((x-1)*n+1):(x*n))}))
              S_Y <- w[sub] %*% t(w[sub])
              comp <- sort(Jprime$clq.add[[c]])
              pc <- length(Jprime$clq.add[[c]])
              sigmahat.sub <- as.matrix(sigmahat.mat[comp,comp])
              phihat.sub <- as.matrix(phihat.mat[comp,comp])
              nu.sub <- as.matrix(nu.mat[comp,comp])
              Stemp <- matrix(nrow=n*pc,ncol=n*pc)
              Rtemp <- matrix(0,nrow=pc,ncol=pc)
              diag(Rtemp) <- 1
              for (i in 1:pc){
                for(j in i:pc){
                  idx=c(((i-1)*n+1):(i*n))
                  jdx=c(((j-1)*n+1):(j*n))
                  cnew = sort(c(comp[i],comp[j]))
                  if(i != j){m1 <- which(sapply(psi.clqs_2,function(x){setequal(x,cnew)}))
                  pnew <- psi[m1]
                  } else{
                    pnew <- 1
                  }
                  sig <- sqrt(sigmahat.sub[i,i] * sigmahat.sub[j,j]) *( (phihat.sub[i,i]^nu.sub[i,i]) * (phihat.sub[j,j]^nu.sub[j,j])) * ((1/ phihat.sub[i,j]) ^(2*nu.sub[i,j])) * pnew
                  #sigmahat1.sub <- sigmahat.sub
                  #sigmahat1.mat[v[1],v[2]] <- sigmahat1.mat[v[2],v[1]] <- sig
                  #Stemp <-sig *matern(D,phi= 1/phihat.mat[v[1],v[2]], kappa= nuhat.mat[v[1],v[2]])
                  Stemp[idx,jdx] = sig*matern(D,phi= 1/phihat.sub[i,j], kappa= nu.sub[i,j])
                  Stemp[jdx,idx] = Stemp[idx,jdx]
                  #Rtemp[i,j] = sigmahat.sub[i,j]/ (sqrt(sigmahat.sub[i,i] * sigmahat.sub[j,j]) *( (phihat.sub[i,i]^nu.sub[i,i]) * (phihat.sub[j,j]^nu.sub[j,j])) * ((1/ phihat.sub[i,j]) ^(2*nu.sub[i,j])))
                  Rtemp[i,j] = pnew
                  Rtemp[j,i] = Rtemp[i,j]
                }
              }
              if(!is.positive.semi.definite(Rtemp)){
                lik <- -10^6
              } else {
                lik <- ellK(K=rcppeigen_invert_matrix(Stemp),S=S_Y,n=1)
              }
              return(list(Stemp, Rtemp, lik, S_Y))
              }else{
                return(list(NULL,NULL,0, NULL))
              }})
          } 
          if(!list.check(Jprime$clq.del)){
            clq.del.lik <- lapply(1:length(Jprime$clq.del),function(c){
              varsub <- Jprime$clq.del[[c]]
              if(length(varsub)){
                ind <- which(sapply(clqs, function(x){all(varsub %in% x)}))
                return(lik.clq[[ind[1]]])
              }else{
                return(0)
              }})
          }
          if(!list.check(Jprime$sep.add)){
            sep.add.lik <- lapply(1:length(Jprime$sep.add),function(c){
              varsub <- Jprime$sep.add[[c]]
              if(length(varsub)){sub <- unlist(lapply(varsub,function(x){c(((x-1)*n+1):(x*n))}))
              S_Y <- w[sub] %*% t(w[sub])
              comp <- sort(Jprime$sep.add[[c]])
              pc <- length(Jprime$sep.add[[c]])
              sigmahat.sub <- as.matrix(sigmahat.mat[comp,comp])
              phihat.sub <- as.matrix(phihat.mat[comp,comp])
              nu.sub <- as.matrix(nu.mat[comp,comp])
              Stemp <- matrix(nrow=n*pc,ncol=n*pc)
              Rtemp <- matrix(nrow=pc,ncol=pc)
              diag(Rtemp) <- 1
              for (i in 1:pc){
                for(j in i:pc){
                  idx=c(((i-1)*n+1):(i*n))
                  jdx=c(((j-1)*n+1):(j*n))
                  cnew = sort(c(comp[i],comp[j]))
                  if(i != j){m1 <- which(sapply(psi.clqs_2,function(x){setequal(x,cnew)}))
                  pnew <- psi[m1]
                  } else{
                    pnew <- 1
                  }
                  sig <- sqrt(sigmahat.sub[i,i] * sigmahat.sub[j,j]) *( (phihat.sub[i,i]^nu.sub[i,i]) * (phihat.sub[j,j]^nu.sub[j,j])) * ((1/ phihat.sub[i,j]) ^(2*nu.sub[i,j])) * pnew
                  #sigmahat1.sub <- sigmahat.sub
                  #sigmahat1.mat[v[1],v[2]] <- sigmahat1.mat[v[2],v[1]] <- sig
                  #Stemp <-sig *matern(D,phi= 1/phihat.mat[v[1],v[2]], kappa= nuhat.mat[v[1],v[2]])
                  Stemp[idx,jdx] = sig*matern(D,phi= 1/phihat.sub[i,j], kappa= nu.sub[i,j])
                  Stemp[jdx,idx] = Stemp[idx,jdx]
                  #Rtemp[i,j] = sigmahat.sub[i,j]/ (sqrt(sigmahat.sub[i,i] * sigmahat.sub[j,j]) *( (phihat.sub[i,i]^nu.sub[i,i]) * (phihat.sub[j,j]^nu.sub[j,j])) * ((1/ phihat.sub[i,j]) ^(2*nu.sub[i,j])))
                  Rtemp[i,j] = pnew
                  Rtemp[j,i] = Rtemp[i,j]
                }
              }
              if(!is.positive.semi.definite(Rtemp)){
                lik <- -10^6
              } else {
                lik <- ellK(K=rcppeigen_invert_matrix(Stemp),S=S_Y,n=1)
              }
              return(list(Stemp, Rtemp, lik, S_Y))
              }else{
                return(list(NULL,NULL,0, NULL))
              }})
          }
          if(!list.check(Jprime$sep.del)){
            sep.del.lik <- lapply(1:length(Jprime$sep.del),function(c){
              varsub <- Jprime$sep.del[[c]]
              if(length(varsub)){
                ind <- which(sapply(seps, function(x){all(varsub %in% x)}))
                return(lik.sep[[ind[1]]])
              }else{
                return(0)
              }})
          }
          pi.ratio1 = list.sum(clq.add.lik,3) + list.sum(sep.del.lik,1) - list.sum(clq.del.lik,1) - list.sum(sep.add.lik,3) 
          pi.ratio2 = - log(muJprime) + log(muJ)
          pi.ratio = pi.ratio1 + pi.ratio2
          pi.ratio= exp(pi.ratio)    
          u2 = runif(1)
          if(u2 > min(1,pi.ratio)){
            J <- jT
            Atemp <- tryCatch(Atemp, error=function(e) NULL)
          } else{
            J <- Jprime$J
            llik.w = llik.w + pi.ratio1
            llik.g = llik.g + pi.ratio2
            clqs.new <- Jprime$J$clqs
            seps.new <- Jprime$J$seps
            Slist.clq.new <- Slist.sep.new <- Rlist.clq.new <- Rlist.sep.new <- lik.clq.new <- lik.sep.new <-  Sy.clq.list.new <- Sy.sep.list.new <- list()
            if(length(Jprime$sep.del)){
              for(k in 1:length(Jprime$sep.del)){
                if(length(Jprime$sep.del[[k]])){
                  Atemp[Jprime$sep.del[[k]], Jprime$sep.del[[k]]] <- 0
                }
              }
            }
            
            if(length(Jprime$clq.del)){
              for(k in 1:length(Jprime$clq.del)){
                if(length(Jprime$clq.del[[k]])){
                  Atemp[Jprime$clq.del[[k]], Jprime$clq.del[[k]]] <- 0
                }
              }
            }  
            for(k in 1:length(clqs.new)){
              match.id <- which(sapply(clqs, function(x){setequal(clqs.new[[k]],x)}))[1]
              if(!is.na(match.id)){
                Slist.clq.new[[k]] <- Slist.clq[[match.id]]
                Rlist.clq.new[[k]] <- Rlist.clq[[match.id]]
                lik.clq.new[[k]] <- lik.clq[[match.id]]
                Sy.clq.list.new[[k]] <- Sy.clq.list[[match.id]]
              } else {
                match.id <- which(sapply(Jprime$clq.add, function(x){setequal(clqs.new[[k]],x)}))[1]
                Slist.clq.new[[k]] <- clq.add.lik[[match.id]][[1]]
                Rlist.clq.new[[k]] <- clq.add.lik[[match.id]][[2]]
                lik.clq.new[[k]] <- clq.add.lik[[match.id]][[3]]
                Sy.clq.list.new[[k]] <- clq.add.lik[[match.id]][[4]]
                Atemp[clqs.new[[k]], clqs.new[[k]]] <- 1
              }
            }
            for(k in 2:length(seps.new)){
              match.id <- which(sapply(seps, function(x){setequal(seps.new[[k]],x)}))[1]
              if(!length(seps.new[[k]])){
                Slist.sep.new[[k]] <- NULL
                Rlist.sep.new[[k]] <- NULL
                lik.sep.new[[k]] <- NULL
                Sy.sep.list.new[[k]] <- NULL
              } else if(!is.na(match.id)){
                Slist.sep.new[[k]] <- Slist.sep[[match.id]]
                Rlist.sep.new[[k]] <- Rlist.sep[[match.id]]
                lik.sep.new[[k]] <- lik.sep[[match.id]]
                Sy.sep.list.new[[k]] <- Sy.sep.list[[match.id]]
              } else {
                match.id <- which(sapply(Jprime$sep.add, function(x){setequal(seps.new[[k]],x)}))[1]
                Slist.sep.new[[k]] <- sep.add.lik[[match.id]][[1]]
                Rlist.sep.new[[k]] <- sep.add.lik[[match.id]][[2]]
                lik.sep.new[[k]] <- sep.add.lik[[match.id]][[3]]
                Sy.sep.list.new[[k]] <- sep.add.lik[[match.id]][[4]]
                Atemp[seps.new[[k]], seps.new[[k]]] <- 1
              }
            }
            
            diag(Atemp) <- 1
            
            clqs <- clqs.new
            seps <- seps.new
            J0 <- jT
            jT <- J
            clq.no.singleton <- which(sapply(clqs, length)>1)
            if(length(clq.no.singleton)){
              b <- lapply(clqs[clq.no.singleton],function(x){x<-sort(x);c <- combn(x,2);c})
              b <- reduce(b,cbind) %>% unique(MARGIN=2)
              clqs_2 <- split(b,rep(1:ncol(b), each = nrow(b)))
            } else{
              clqs_2 <- list()
              theta <- numeric(0)
            }
            g_v <- graph_from_adjacency_matrix(Atemp,mode="undirected")
            g_V <- as(Atemp[as.numeric(max_cardinality(g_v)$alpha),as.numeric(max_cardinality(g_v)$alpha)],"graphNEL")
            coloring <- as.numeric(sequential.vertex.coloring(g_V)$color[max_cardinality(g_v)$alpham])
            
            # chromatic sample coloring for edges
            ne <- length(clqs_2)
            A_E <- matrix(0,nrow=ne, ncol=ne)
            if(ne >1){
              for(ii in 1:(ne-1)){
                for(jj in (ii+1):ne){
                  e <- sort(union(clqs_2[[ii]], clqs_2[[jj]]))
                  A_E[ii,jj] <- any(sapply(clqs, function(x){setequal(x,e)}))
                  A_E[jj,ii] <- A_E[ii,jj]
                }
              }
              g_e <- graph_from_adjacency_matrix(A_E,mode="undirected")
              g_E <- as(A_E[as.numeric(max_cardinality(g_e)$alpha),as.numeric(max_cardinality(g_e)$alpha)],"graphNEL")
              coloring_e <- as.numeric(sequential.vertex.coloring(g_E)$color[max_cardinality(g_e)$alpham])
            } else{
              coloring_e <- 0  
            }
            
            if(length(clqs_2)){
              for(t in 1:length(clqs_2)){
                clqmatchedge[[t]] <- which(unlist(lapply(clqs,function(x){all(!is.na(match(as.numeric(clqs_2[[t]]),as.numeric(x))))}))>0)
                sepmatchedge[[t]] <- which(unlist(lapply(seps,function(x){all(!is.na(match(as.numeric(clqs_2[[t]]),as.numeric(x))))}))>0)
                i1 <- which(clqs[[clqmatchedge[[t]][1]]] == clqs_2[[t]][1])
                j1 <- which(clqs[[clqmatchedge[[t]][1]]] == clqs_2[[t]][2])
                theta[t] <- Rlist.clq.new[[clqmatchedge[[t]][1]]][i1,j1]
              }
            }
            
            clqmatchvar <- sepmatchvar <- list()
            for(t in 1:p){
              clqmatchvar[[t]] <- which(unlist(lapply(clqs,function(x){all(!is.na(match(as.numeric(t),as.numeric(x))))}))>0)
              sepmatchvar[[t]] <- which(unlist(lapply(seps,function(x){all(!is.na(match(as.numeric(t),as.numeric(x))))}))>0)
            }
            
            # recalculate indices based on new clique and separators 
            sam.clq <- lapply(c(1:length(clqs)), function(k){
              q=length(clqs[[k]])
              sam=unlist(lapply(clqs[[k]],function(x){c(((x-1)*n+1):(x*n))}))
              return(sam)})
            
            sam.sep <- lapply(c(2:length(seps)), function(k){
              q=length(seps[[k]])
              sam=unlist(lapply(seps[[k]],function(x){c(((x-1)*n+1):(x*n))}))
              return(sam)})
            
            sam.sep <- append(100, sam.sep)
            
            ind.clq <- lapply(c(1:length(clqs)), function(k){
              q=length(clqs[[k]])
              if(q==1){ind <- lapply(2:n, function(x){rbind(c(x,imvec[[x-1]]))})
              } else{
                ind <- lapply(2:n, function(x){(cbind(seq(x,(q-1)*n+x,length=q),sapply(imvec[[x-1]],function(i){seq(i,(q-1)*n+i,length=q)})))})
              }
              return(ind)
            })
            
            ind.sep <- lapply(c(2:length(seps)), function(k){
              q=length(seps[[k]])
              if(q==1){ind <- lapply(2:n, function(x){rbind(c(x,imvec[[x-1]]))})
              } else{
                ind <- lapply(2:n, function(x){(cbind(seq(x,(q-1)*n+x,length=q),sapply(imvec[[x-1]],function(i){seq(i,(q-1)*n+i,length=q)})))})
              }
              return(ind)
            })
            
            ind.sep <- append(100,ind.sep)
            
            Slist.clq <- Slist.clq.new
            Slist.sep <- Slist.sep.new
            Rlist.clq <- Rlist.clq.new
            Rlist.sep <- Rlist.sep.new
            lik.clq <- lik.clq.new
            lik.sep <- lik.sep.new
            Sy.sep.list <- Sy.sep.list.new
            Sy.clq.list <- Sy.clq.list.new
            mcmc.store$add.counter.accept[[j]][graph.k] <- 1
          }
        }
        }
      } else {
        Jprime <- remove.edge(jT)
        qJJprime <- Jprime$prob
        if(Jprime$prob==0){J <- jT
        Atemp <- tryCatch(Atemp, error=function(e) NULL)
        } else{ qJprimeJ = remove.reverse.prob(Jprime)
        u1= runif(1)
        qratio = qJJprime/qJprimeJ
        if(u1 >= qratio){J <- jT
        Atemp <- tryCatch(Atemp, error=function(e) NULL)
        } else{ 
          J <- jT
          muJ = countjtrees(J)
          muJprime= countjtrees(Jprime$J)
          
          clq.add.lik <- sep.add.lik <- clq.del.lik <- sep.del.lik <- list()
          
          if(!list.check(Jprime$clq.add)){
            clq.add.lik <- lapply(1:length(Jprime$clq.add),function(c){
              varsub <- Jprime$clq.add[[c]]
              if(length(varsub)){sub <- unlist(lapply(varsub,function(x){c(((x-1)*n+1):(x*n))}))
              S_Y <- w[sub] %*% t(w[sub])
              comp <- sort(Jprime$clq.add[[c]])
              pc <- length(Jprime$clq.add[[c]])
              sigmahat.sub <- as.matrix(sigmahat.mat[comp,comp])
              phihat.sub <- as.matrix(phihat.mat[comp,comp])
              nu.sub <- as.matrix(nu.mat[comp,comp])
              Stemp <- matrix(nrow=n*pc,ncol=n*pc)
              Rtemp <- matrix(0,nrow=pc,ncol=pc)
              diag(Rtemp) <- 1
              for (i in 1:pc){
                for(j in i:pc){
                  idx=c(((i-1)*n+1):(i*n))
                  jdx=c(((j-1)*n+1):(j*n))
                  cnew = sort(c(comp[i],comp[j]))
                  if(i != j){m1 <- which(sapply(psi.clqs_2,function(x){setequal(x,cnew)}))
                  pnew <- psi[m1]
                  } else{
                    pnew <- 1
                  }
                  sig <- sqrt(sigmahat.sub[i,i] * sigmahat.sub[j,j]) *( (phihat.sub[i,i]^nu.sub[i,i]) * (phihat.sub[j,j]^nu.sub[j,j])) * ((1/ phihat.sub[i,j]) ^(2*nu.sub[i,j])) * pnew
                  Stemp[idx,jdx] = sig*matern(D,phi= 1/phihat.sub[i,j], kappa= nu.sub[i,j])
                  Stemp[jdx,idx] = Stemp[idx,jdx]
                  Rtemp[i,j] = pnew
                  Rtemp[j,i] = Rtemp[i,j]
                }
              }
              if(!is.positive.semi.definite(Rtemp)){
                lik <- -10^6
              } else {
                lik <- ellK(K=rcppeigen_invert_matrix(Stemp),S=S_Y,n=1)
              }
              return(list(Stemp, Rtemp, lik, S_Y))
              }else{
                return(list(NULL,NULL,0, NULL))
              }})
          } 
          if(!list.check(Jprime$clq.del)){
            clq.del.lik <- lapply(1:length(Jprime$clq.del),function(c){
              varsub <- Jprime$clq.del[[c]]
              if(length(varsub)){
                ind <- which(sapply(clqs, function(x){all(varsub %in% x)}))
                return(lik.clq[[ind[1]]])
              }else{
                return(0)
              }})
          }
          if(!list.check(Jprime$sep.add)){
            sep.add.lik <- lapply(1:length(Jprime$sep.add),function(c){
              varsub <- Jprime$sep.add[[c]]
              if(length(varsub)){sub <- unlist(lapply(varsub,function(x){c(((x-1)*n+1):(x*n))}))
              S_Y <- w[sub] %*% t(w[sub])
              comp <- sort(Jprime$sep.add[[c]])
              pc <- length(Jprime$sep.add[[c]])
              sigmahat.sub <- as.matrix(sigmahat.mat[comp,comp])
              phihat.sub <- as.matrix(phihat.mat[comp,comp])
              nu.sub <- as.matrix(nu.mat[comp,comp])
              Stemp <- matrix(nrow=n*pc,ncol=n*pc)
              Rtemp <- matrix(nrow=pc,ncol=pc)
              diag(Rtemp) <- 1
              for (i in 1:pc){
                for(j in i:pc){
                  idx=c(((i-1)*n+1):(i*n))
                  jdx=c(((j-1)*n+1):(j*n))
                  cnew = sort(c(comp[i],comp[j]))
                  if(i != j){m1 <- which(sapply(psi.clqs_2,function(x){setequal(x,cnew)}))
                  pnew <- psi[m1]
                  } else{
                    pnew <- 1
                  }
                  sig <- sqrt(sigmahat.sub[i,i] * sigmahat.sub[j,j]) *( (phihat.sub[i,i]^nu.sub[i,i]) * (phihat.sub[j,j]^nu.sub[j,j])) * ((1/ phihat.sub[i,j]) ^(2*nu.sub[i,j])) * pnew
                  Stemp[idx,jdx] = sig*matern(D,phi= 1/phihat.sub[i,j], kappa= nu.sub[i,j])
                  Stemp[jdx,idx] = Stemp[idx,jdx]
                  Rtemp[i,j] = pnew
                  Rtemp[j,i] = Rtemp[i,j]
                }
              }
              if(!is.positive.semi.definite(Rtemp)){
                lik <- 10^6
              } else {
                lik <- ellK(K=rcppeigen_invert_matrix(Stemp),S=S_Y,n=1)
              }
              return(list(Stemp, Rtemp, lik, S_Y))
              }else{
                return(list(NULL,NULL,0, NULL))
              }})
          }
          if(!list.check(Jprime$sep.del)){
            sep.del.lik <- lapply(1:length(Jprime$sep.del),function(c){
              varsub <- Jprime$sep.del[[c]]
              if(length(varsub)){
                ind <- which(sapply(seps, function(x){all(varsub %in% x)}))
                return(lik.sep[[ind[1]]])
              }else{
                return(0)
              }})
          }
          pi.ratio1 = list.sum(clq.add.lik,3) + list.sum(sep.del.lik,1) - list.sum(clq.del.lik,1) - list.sum(sep.add.lik,3) 
          pi.ratio2 = - log(muJprime) + log(muJ)
          pi.ratio = pi.ratio1 + pi.ratio2
          pi.ratio= exp(pi.ratio)    
          u2 = runif(1)
          if(u2 > min(1,pi.ratio)){
            J <- jT
            Atemp <- tryCatch(Atemp, error=function(e) NULL)
          } else{
            J <- Jprime$J
            llik.w = llik.w + pi.ratio1
            llik.g = llik.g + pi.ratio2
            clqs.new <- Jprime$J$clqs
            seps.new <- Jprime$J$seps
            Slist.clq.new <- Slist.sep.new <- Rlist.clq.new <- Rlist.sep.new <- lik.clq.new <- lik.sep.new <-  Sy.clq.list.new <- Sy.sep.list.new <- list()
            if(length(Jprime$sep.del)){
              for(k in 1:length(Jprime$sep.del)){
                if(length(Jprime$sep.del[[k]])){
                  Atemp[Jprime$sep.del[[k]], Jprime$sep.del[[k]]] <- 0
                }
              }
            }
            
            if(length(Jprime$clq.del)){
              for(k in 1:length(Jprime$clq.del)){
                if(length(Jprime$clq.del[[k]])){
                  Atemp[Jprime$clq.del[[k]], Jprime$clq.del[[k]]] <- 0
                }
              }
            }  
            for(k in 1:length(clqs.new)){
              match.id <- which(sapply(clqs, function(x){setequal(clqs.new[[k]],x)}))[1]
              if(!is.na(match.id)){
                Slist.clq.new[[k]] <- Slist.clq[[match.id]]
                Rlist.clq.new[[k]] <- Rlist.clq[[match.id]]
                lik.clq.new[[k]] <- lik.clq[[match.id]]
                Sy.clq.list.new[[k]] <- Sy.clq.list[[match.id]]
              } else {
                match.id <- which(sapply(Jprime$clq.add, function(x){setequal(clqs.new[[k]],x)}))[1]
                Slist.clq.new[[k]] <- clq.add.lik[[match.id]][[1]]
                Rlist.clq.new[[k]] <- clq.add.lik[[match.id]][[2]]
                lik.clq.new[[k]] <- clq.add.lik[[match.id]][[3]]
                Sy.clq.list.new[[k]] <- clq.add.lik[[match.id]][[4]]
                Atemp[clqs.new[[k]], clqs.new[[k]]] <- 1
              }
            }
            for(k in 2:length(seps.new)){
              match.id <- which(sapply(seps, function(x){setequal(seps.new[[k]],x)}))[1]
              if(!length(seps.new[[k]])){
                Slist.sep.new[[k]] <- NULL
                Rlist.sep.new[[k]] <- NULL
                lik.sep.new[[k]] <- NULL
                Sy.sep.list.new[[k]] <- NULL
              } else if(!is.na(match.id)){
                Slist.sep.new[[k]] <- Slist.sep[[match.id]]
                Rlist.sep.new[[k]] <- Rlist.sep[[match.id]]
                lik.sep.new[[k]] <- lik.sep[[match.id]]
                Sy.sep.list.new[[k]] <- Sy.sep.list[[match.id]]
              } else {
                match.id <- which(sapply(Jprime$sep.add, function(x){setequal(seps.new[[k]],x)}))[1]
                Slist.sep.new[[k]] <- sep.add.lik[[match.id]][[1]]
                Rlist.sep.new[[k]] <- sep.add.lik[[match.id]][[2]]
                lik.sep.new[[k]] <- sep.add.lik[[match.id]][[3]]
                Sy.sep.list.new[[k]] <- sep.add.lik[[match.id]][[4]]
                Atemp[seps.new[[k]], seps.new[[k]]] <- 1
              }
            }
            
            diag(Atemp) <- 1
            
            clqs <- clqs.new
            seps <- seps.new
            J0 <- jT
            jT <- J
            clq.no.singleton <- which(sapply(clqs, length)>1)
            if(length(clq.no.singleton)){
              b <- lapply(clqs[clq.no.singleton],function(x){x<-sort(x);c <- combn(x,2);c})
              b <- reduce(b,cbind) %>% unique(MARGIN=2)
              clqs_2 <- split(b,rep(1:ncol(b), each = nrow(b)))
            } else{
              clqs_2 <- list()
              theta <- numeric(0)
            }
            g_v <- graph_from_adjacency_matrix(Atemp,mode="undirected")
            g_V <- as(Atemp[as.numeric(max_cardinality(g_v)$alpha),as.numeric(max_cardinality(g_v)$alpha)],"graphNEL")
            coloring <- as.numeric(sequential.vertex.coloring(g_V)$color[max_cardinality(g_v)$alpham])
            
            # chromatic sample coloring for edges
            ne <- length(clqs_2)
            A_E <- matrix(0,nrow=ne, ncol=ne)
            if(ne >1){
              for(ii in 1:(ne-1)){
                for(jj in (ii+1):ne){
                  e <- sort(union(clqs_2[[ii]], clqs_2[[jj]]))
                  A_E[ii,jj] <- any(sapply(clqs, function(x){setequal(x,e)}))
                  A_E[jj,ii] <- A_E[ii,jj]
                }
              }
              g_e <- graph_from_adjacency_matrix(A_E,mode="undirected")
              g_E <- as(A_E[as.numeric(max_cardinality(g_e)$alpha),as.numeric(max_cardinality(g_e)$alpha)],"graphNEL")
              coloring_e <- as.numeric(sequential.vertex.coloring(g_E)$color[max_cardinality(g_e)$alpham])
            } else{
              coloring_e <- 0  
            }
            
            
            if(length(clqs_2)){
              theta <- numeric(length(clqs_2))
              for(t in 1:length(clqs_2)){
                clqmatchedge[[t]] <- which(unlist(lapply(clqs,function(x){all(!is.na(match(as.numeric(clqs_2[[t]]),as.numeric(x))))}))>0)
                sepmatchedge[[t]] <- which(unlist(lapply(seps,function(x){all(!is.na(match(as.numeric(clqs_2[[t]]),as.numeric(x))))}))>0)
                i1 <- which(clqs[[clqmatchedge[[t]][1]]] == clqs_2[[t]][1])
                j1 <- which(clqs[[clqmatchedge[[t]][1]]] == clqs_2[[t]][2])
                theta[t] <- Rlist.clq.new[[clqmatchedge[[t]][1]]][i1,j1]
              }
            }
            
            clqmatchvar <- sepmatchvar <- list()
            for(t in 1:p){
              clqmatchvar[[t]] <- which(unlist(lapply(clqs,function(x){all(!is.na(match(as.numeric(t),as.numeric(x))))}))>0)
              sepmatchvar[[t]] <- which(unlist(lapply(seps,function(x){all(!is.na(match(as.numeric(t),as.numeric(x))))}))>0)
            }
            
            # recalculate indices based on new clique and separators 
            sam.clq <- lapply(c(1:length(clqs)), function(k){
              q=length(clqs[[k]])
              sam=unlist(lapply(clqs[[k]],function(x){c(((x-1)*n+1):(x*n))}))
              return(sam)})
            
            sam.sep <- lapply(c(2:length(seps)), function(k){
              q=length(seps[[k]])
              sam=unlist(lapply(seps[[k]],function(x){c(((x-1)*n+1):(x*n))}))
              return(sam)})
            
            sam.sep <- append(100, sam.sep)
            
            ind.clq <- lapply(c(1:length(clqs)), function(k){
              q=length(clqs[[k]])
              if(q==1){ind <- lapply(2:n, function(x){rbind(c(x,imvec[[x-1]]))})
              } else{
                ind <- lapply(2:n, function(x){(cbind(seq(x,(q-1)*n+x,length=q),sapply(imvec[[x-1]],function(i){seq(i,(q-1)*n+i,length=q)})))})
              }
              return(ind)
            })
            
            ind.sep <- lapply(c(2:length(seps)), function(k){
              q=length(seps[[k]])
              if(q==1){ind <- lapply(2:n, function(x){rbind(c(x,imvec[[x-1]]))})
              } else{
                ind <- lapply(2:n, function(x){(cbind(seq(x,(q-1)*n+x,length=q),sapply(imvec[[x-1]],function(i){seq(i,(q-1)*n+i,length=q)})))})
              }
              return(ind)
            })
            
            ind.sep <- append(100,ind.sep)
            
            
            Slist.clq <- Slist.clq.new
            Slist.sep <- Slist.sep.new
            Rlist.clq <- Rlist.clq.new
            Rlist.sep <- Rlist.sep.new
            lik.clq <- lik.clq.new
            lik.sep <- lik.sep.new
            Sy.sep.list <- Sy.sep.list.new
            Sy.clq.list <- Sy.clq.list.new
            mcmc.store$add.counter.accept[[j]][graph.k] <- 0
          }
        }
        }
      }
    }
    
    toc()
    
    # Randomizing junction tree
    if(j %% 100==0){
      J <- randomize.jt(jT)
      clqs.new <- J$clqs
      seps.new <- J$seps
      Slist.sep.new <- Rlist.sep.new <-  lik.sep.new <- Sy.sep.list.new <- list()
      
      for(k in 2:length(seps.new)){
        match.id <- which(sapply(seps, function(x){setequal(seps.new[[k]],x)}))[1]
        if(!length(seps.new[[k]])){
          Slist.sep.new[[k]] <- NULL
          Rlist.sep.new[[k]] <- NULL
          lik.sep.new[[k]] <- NULL
          Sy.sep.list.new[[k]] <- NULL
        } else if(!is.na(match.id)){
          Slist.sep.new[[k]] <- Slist.sep[[match.id]]
          Rlist.sep.new[[k]] <- Rlist.sep[[match.id]]
          lik.sep.new[[k]] <- lik.sep[[match.id]]
          Sy.sep.list.new[[k]] <- Sy.sep.list[[match.id]]
        } else {
          match.id <- which(sapply(Jprime$sep.add, function(x){setequal(seps.new[[k]],x)}))[1]
          Slist.sep.new[[k]] <- sep.add.lik[[match.id]][[1]]
          Rlist.sep.new[[k]] <- sep.add.lik[[match.id]][[2]]
          lik.sep.new[[k]] <- sep.add.lik[[match.id]][[3]]
          Sy.sep.list.new[[k]] <- sep.add.lik[[match.id]][[4]]
          Atemp[seps.new[[k]], seps.new[[k]]] <- 1
        }
      }
      
      diag(Atemp) <- 1
      
      clqs <- clqs.new
      seps <- seps.new
      J0 <- jT
      jT <- J
      
      if(length(clqs_2)){
        for(t in 1:length(clqs_2)){
          sepmatchedge[[t]] <- which(unlist(lapply(seps,function(x){all(!is.na(match(as.numeric(clqs_2[[t]]),as.numeric(x))))}))>0)
        }
      }
      
      sepmatchvar <- list()
      for(t in 1:p){
        sepmatchvar[[t]] <- which(unlist(lapply(seps,function(x){all(!is.na(match(as.numeric(t),as.numeric(x))))}))>0)
      }
      Slist.sep <- Slist.sep.new
      Rlist.sep <- Rlist.sep.new
      lik.sep <- lik.sep.new
      Sy.sep.list <- Sy.sep.list.new
      
      # recalculate indices based on new clique and separators
      sam.clq <- lapply(c(1:length(clqs)), function(k){
        q=length(clqs[[k]])
        sam=unlist(lapply(clqs[[k]],function(x){c(((x-1)*n+1):(x*n))}))
        return(sam)})
      
      sam.sep <- lapply(c(2:length(seps)), function(k){
        q=length(seps[[k]])
        sam=unlist(lapply(seps[[k]],function(x){c(((x-1)*n+1):(x*n))}))
        return(sam)})
      
      sam.sep <- append(100, sam.sep)
      
      ind.clq <- lapply(c(1:length(clqs)), function(k){
        q=length(clqs[[k]])
        if(q==1){ind <- lapply(2:n, function(x){rbind(c(x,imvec[[x-1]]))})
        } else{
          ind <- lapply(2:n, function(x){(cbind(seq(x,(q-1)*n+x,length=q),sapply(imvec[[x-1]],function(i){seq(i,(q-1)*n+i,length=q)})))})
        }
        return(ind)
      })
      
      ind.sep <- lapply(c(2:length(seps)), function(k){
        q=length(seps[[k]])
        if(q==1){ind <- lapply(2:n, function(x){rbind(c(x,imvec[[x-1]]))})
        } else{
          ind <- lapply(2:n, function(x){(cbind(seq(x,(q-1)*n+x,length=q),sapply(imvec[[x-1]],function(i){seq(i,(q-1)*n+i,length=q)})))})
        }
        return(ind)
      })
      
      ind.sep <- append(100,ind.sep)
      
    }
    
    mcmc.store$betahat[j,]=beta
    mcmc.store$rhat[[j]]=theta
    mcmc.store$rnodes[[j]] = clqs_2
    mcmc.store$tausqhat[j,]=tausq
    mcmc.store$phihat[j,]= diag(phihat.mat)
    mcmc.store$sigmahat[j,]=diag(sigmahat.mat)
    diag(Atemp) <- 1
    mcmc.store$A.list[[j]] = Atemp
    mcmc.store$psihat[j,] <- psi
    mcmc.store$loglik[j,] <- c(llik.w,llik.psi, llik.g)
    rm(Atemp)
    for(k in 1:p){
      #mcmc.store$w[j,k,]=wl[[k]]
      mcmc.store$ytestpred[j,k,]=as.numeric(na.omit(Ytest[[k]]))
    }
    #mcmc.store$pd.ind[[j]] <- sapply(Rlist.clq,function(z){if(is.matrix(z)){is.positive.semi.definite(z)}})
    mcmc.store$clq.length[[j]] <- sapply(clqs,length)
    print(j)
    print(llik.w + llik.psi + llik.g)
    toc()
  }
  
  return(mcmc.store)
}

