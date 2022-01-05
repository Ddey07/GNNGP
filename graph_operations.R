make_graph_join=function(A1,A2){
  m1=nrow(A1)
  m2=nrow(A2)
  n1=ncol(A1)
  n2=ncol(A2)
  A=matrix(ncol=n1+n2,nrow=m1+m2)
  A[1:n1,1:n1]=A1
  A[1:n1,((n1+1):(n1+n2))] <- A[((n1+1):(n1+n2)),(1:n1)] <- 1
  A[((n1+1):(n1+n2)), ((n1+1):(n1+n2))] <- A2
  diag(A) <- 0
  return(A)
}

insertRow <- function(existingDF, newrow, r) {
  existingDF[seq(r+1,nrow(existingDF)+1),] <- existingDF[seq(r,nrow(existingDF)),]
  existingDF[r,] <- newrow
  existingDF
}

# graph functions #
countjtrees <- function(x){
  #creating graph
  x$links <- rbind(x$links)
  jt.edge <- x$links
  if(ncol(jt.edge)==1){jt.edge <- t(jt.edge)}
  jt.graph <- graph_from_edgelist(jt.edge,directed=F)
  if(nrow(jt.edge)==0){
    if(length(x$clqs)==1){jt.graph=make_ring(length(x$clqs))
  } else{
    jt.graph=make_ring(length(x$clqs)) %>% delete_edges(edges=1:length(x$clqs))
  }}
  
  # Counting number of junction trees
  # Finding nu(s) for null separators
  Fs.null <- as.numeric(clusters(jt.graph)$csize)
  nu.null <- prod(Fs.null) * length(x$clqs) ^(length(Fs.null)-2)
  
  
  if(nrow(jt.edge)){
    # calcualting links
    jt.links <- apply(jt.edge,1,function(z){z <- as.numeric(z); y <- intersect(x$clqs[[z[1]]],x$clqs[[z[2]]]); paste(y,collapse=", ")})
    # creating separator vector
    sep.vec <- unlist(lapply(x$seps[-1],function(x){paste(x,collapse=", ")}))
    # finding nu(s) for other separators
    sep.nu <- function(k){
      sep <- unique(sep.vec)[k]
      sep.c <- unlist(str_split(sep,", "))
      ms <- sum(sep.vec==sep)
      if(sep.c[1]==""){ts.ind <- 1:length(x$clqs)
      } else{ts.ind <- which(sapply(x$clqs, function(x){sum(x %in% sep.c)== length(sep.c)}))
      }
      ts <- length(ts.ind)
      sep.sub <- induced_subgraph(delete_edges(jt.graph, edges= which(jt.links == sep)), vids= ts.ind)
      Fs <- as.numeric(clusters(sep.sub)$csize)
      nu.s <- prod(Fs) * ts ^ (ms-1)
      return(nu.s)}
    
    
    n.jtree <- prod(unlist(lapply(1:length(unique(sep.vec)),sep.nu)))
  } else {
    n.jtree <- nu.null
  }
  return(n.jtree)
}



# next step is to write function for junction tree jump steps (also terminate at a certain clique size)
# jt as a list of links, links, cliques and separators
add.edge <- function(J, move="single",max.clique=3, lag.clique=5){
  clq.del <- clq.add <- sep.del <- sep.add <- list()
  typea.clq <- numeric(0)
  type <- NULL
  J$links <- rbind(J$links)
  if(length(J$seps)==1){
    Jnew <- J
    q <- 0
    x <- NULL
    y <- NULL
    mx <- 0
    my <- 0
  } else{
    
    # pick a link at random
    l <- sample(1:nrow(J$links),1)
    lset <- J$links[l,]
    s <- J$seps[[l+1]]
    cx <- J$clqs[[min(lset)]]
    cy <- J$clqs[[max(lset)]]
    mx <- length(cx)
    my <- length(cy)
    
    if(move=="single"){
      cx_s <-  setdiff(cx,s)
      cy_s = setdiff(cy,s)
      x <- ifelse(length(cx_s)==1,cx_s, sample(cx_s,size=1))
      y <- ifelse(length(cy_s)==1,cy_s, sample(cy_s,size=1))
      q <- 1/((length(J$seps)-1)* (mx-length(s)) * (my-length(s)))
    } else {
      cx_s = setdiff(cx,s)
      cy_s = setdiff(cy,s)
      nx = sample(1: length(cx_s),size=1)
      ny = sample(1: length(cy_s),size=1)
      x <- ifelse(length(cx_s)==1,cx_s, sample(cx_s,size=nx))
      y <- ifelse(length(cy_s)==1,cy_s, sample(cy_s,size=ny))
      q <- 1/((length(J$seps)-1)* (mx-length(s)) * (my-length(s)) *  choose(mx-length(s), nx) * choose(my-length(s), ny))
    }
    Jnew <- J
    
    # type a
    if(setequal(union(x,s), cx) & setequal(union(y,s), cy)){
      # updating links list
      links.new <- J$links[-l,]
      links.new[which(links.new==max(lset))]= min(lset)
      links.new[which(links.new > max(lset))]= links.new[which(links.new > max(lset))] - 1
      Jnew$links <- rbind(links.new)
      rm(links.new)
      # Updating clique list
      Jnew$clqs <- J$clqs
      clq.del <- J$clqs[lset]
      Jnew$clqs <- J$clqs[-max(lset)]
      clq.add <- list(sort(union(J$clqs[min(lset)][[1]],J$clqs[max(lset)][[1]])))
      Jnew$clqs[min(lset)] <- clq.add
      # updating separators
      Jnew$seps <- J$seps
      sep.del <- J$seps[(l+1)]
      Jnew$seps <- Jnew$seps[-(l+1)]
      # separator change id
      sep.change <- which(apply(Jnew$links, 1, function(z){any(z %in% min(lset))}))
      for(k in sep.change){
        k1 <- Jnew$links[k,]
        Jnew$seps[[k+1]] <- sort(intersect(Jnew$clqs[[k1[1]]],Jnew$clqs[[k1[2]]]))
      }
      sep.add <- Jnew$seps[sep.change+1]
      type= "a"
      typea.clq = min(lset)
    } else if (length(setdiff(cx, union(x,s))) & setequal(union(y,s), cy)){
      Jnew$links <- J$links
      Jnew$clqs <- J$clqs
      clq.del <- J$clqs[max(lset)]
      clq.add <- list(sort(union(cy,x)))
      Jnew$clqs[[max(lset)]] <- unlist(clq.add)
      Jnew$seps <- J$seps
      sep.del <- list(J$seps[[l+1]])
      sep.add <- list(sort(union(s,x)))
      Jnew$seps[[l+1]] <- unlist(sep.add)
      type= "b"
    } else if (length(setdiff(cy, union(y,s))) & setequal(union(x,s), cx)){
      Jnew$links <- J$links
      Jnew$clqs <- J$clqs
      clq.del <- J$clqs[min(lset)]
      clq.add <- list(sort(union(cx,y)))
      Jnew$clqs[[min(lset)]] <- unlist(clq.add)
      Jnew$seps <- J$seps
      sep.del <- J$seps[[l+1]]
      sep.add <- list(sort(union(s,y)))
      Jnew$seps[[l+1]] <- unlist(sep.add)
      type= "c"
    } else {
      # updating clqs list
      links.new <- rbind(J$links, c(min(lset), length(J$clqs)+1))
      links.new[l,]= sort(c((length(J$clqs)+1),max(lset)))
      # Updating links list
      Jnew$links <- links.new
      rm(links.new)
      clq.add <- list(sort(union(union(x,y),s)))
      Jnew$clqs <- append(J$clqs,clq.add)
      # updating separators
      sep.add <- list(sort(union(x,s)))
      Jnew$seps <- append(J$seps, sep.add)
      sep.del <- Jnew$seps[[(l+1)]]
      Jnew$seps[[(l+1)]] <- sort(union(y,s))
      sep.add <- append(sep.add, list( sort(union(y,s))))
      type= "d"
    }
  }
  # add a condition to restrict maximum cliques and not allow cliques at more than lag.clique
  if(any(sapply(Jnew$clqs,length)>max.clique) | any(sapply(Jnew$clqs,function(x){max(x)-min(x)})>lag.clique)){
    Jnew <- J
    q <- 0
    x <- NULL
    y <- NULL
    clq.del <- clq.add <- sep.del <- sep.add <- list()
  }
  
  if(!is.list(clq.add)){
    clq.add <- list(clq.add)
  }
  if(!is.list(clq.del)){
    clq.del <- list(clq.del)
  }
  if(!is.list(sep.add)){
    sep.add <- list(sep.add)
  }
  if(!is.list(sep.del)){
    sep.del <- list(sep.del)
  }
  
  return(list(J=Jnew, x=x, y=y, s=s, type=type, mx=mx, my=my, l=l, prob=q, move=move, typea.clq=typea.clq, sep.add=sep.add, sep.del=sep.del, clq.add=clq.add, clq.del=clq.del))  
}

# remove edge 
remove.edge <- function(J, move="single",max.clique=3, lag.clique=5){
  J$links <- rbind(J$links)
  Jgraph <- graph_from_edgelist(J$links, directed = F)
  l <- sample(1:length(J$clqs),1)
  #lset <- J$links[l,]
  c <- J$clqs[[l]]
  clq.del <- clq.add <- sep.del <- sep.add <- list()
  type <- NULL
  mx <- my <- 0
  
  if(length(c)==1){
    Jnew <- J
    x <- NULL
    y <- NULL
    q <- 0
    cx <- 0
    cy <- 0
  } else {
    
    m <- length(c)
    M <- sample(2:m,size=1)
    N <- sample(1:(M-1),size=1)
    if(move=="single"){
      sam <- sample(c,size=2)
      x <- sam[1]
      y <- sam[2]
      s <- setdiff(c,union(x,y))
      q <- 1/(length(J$clqs)) * 2/(m*(m-1))
    } else {
      part1 <- as.numeric(setparts(c(N, M-N, m-M)))
      xys.order <- perms(3)[,sample(1:6,size=1)]
      x <- c[which(xys.order==1)]
      y <- c[which(xys.order==2)]
      s <- c[which(xys.order==3)]
      q <- 1/(length(J$clqs)) * 2/ ((m-1)*(M-1)) * (factorial(N)* factorial(M-N)* factorial(m-M))/(factorial(m))
    }
    Jnew <- J
    # Finding N, N_x, N_y 
    nbr <- tryCatch(as.numeric(neighbors(Jgraph,v=l)), error=function(e) NULL)
    nbr.intersect.x <- sapply(nbr, function(k){any(J$clqs[[k]] %in% x)})
    nbr.intersect.y <- sapply(nbr, function(k){any(J$clqs[[k]] %in% y)})
    nbr.intersect <- rbind(nbr.intersect.x,nbr.intersect.y)
    
    if(any(tryCatch(colSums(nbr.intersect),error=function(e){0})==2)){
      Jnew <- J
      x <- NULL
      y <- NULL
      q <- 0
      cx <- 0
      cy <- 0
    } else { 
      scrN <- tryCatch(nbr[(colSums(nbr.intersect)==0)], error=function(e){NULL})
      scrNx <- nbr[(nbr.intersect.x)==1 & (nbr.intersect.y)==0]
      scrNy <- nbr[(nbr.intersect.y)==1 & (nbr.intersect.x)==0]
      cx <- tryCatch({t <- scrNx[which(sapply(scrNx, function(z){all(union(x,s) %in% J$clqs[[z]])}))]; ifelse(length(t)==1,t, sample(t,size=1))}, error=function(e){NULL})
      cy <- tryCatch({t <- scrNy[which(sapply(scrNy, function(z){all(union(y,s) %in% J$clqs[[z]])}))]; ifelse(length(t)==1,t, sample(t,size=1))}, error=function(e){NULL})
      # type a
      if(is.null(cx) & is.null(cy)){
        # add and delete clique
        clq.del <- J$clqs[[l]]
        Jnew$clqs <- J$clqs[-l]
        clq.add <- list(sort(union(x,s)), sort(union(y,s)))
        Jnew$clqs <- append(append(Jnew$clqs, list(sort(union(x,s)))), list(sort(union(y,s))))
        # add and delete links
        links.c <- which(apply(J$links, 1, function(z){l %in% z}))
        Jnew$links <- J$links[-links.c,]
        Jnew$links[which(Jnew$links > l)] <- Jnew$links[which(Jnew$links > l)] - 1
        # connecting Nx to XUS and Ny to YUS
        link.x <- length(Jnew$clqs)-1
        link.y <- length(Jnew$clqs)
        Jnew$links <- rbind(Jnew$links,sort(c(link.x,link.y)))
        if(length(scrNx)) {scrNx[which(scrNx >l)] <- scrNx[which(scrNx >l)] -1 ; links.new.x <- t(sapply(scrNx, function(z){sort(c(z,link.x))})); Jnew$links <- rbind(Jnew$links,links.new.x)}
        if(length(scrNy)) {scrNy[which(scrNy >l)] <- scrNy[which(scrNy >l)] -1 ; links.new.y <- t(sapply(scrNy, function(z){sort(c(z,link.y))})); Jnew$links <- rbind(Jnew$links,links.new.y)}
        if(length(scrN)){scrN[which(scrN >l)] <- scrN[which(scrN >l)] -1 ; links.new.xy <- t(sapply(scrN, function(z){sort(c(z,sample(c(link.x,link.y),size=1)))})) ; Jnew$links <- rbind(Jnew$links,links.new.xy); q <- q * 2^(-length(scrN))}
        #Jnew$links <- rbind(Jnew$links,c(link.x,link.y), links.new.x, links.new.y)
        # add and delete separators
        sep.del <- J$seps[(links.c+1)]
        Jnew$seps <- J$seps[-(links.c+1)]
        nsep <- length(Jnew$seps)
        if(nsep==0){nsep <- nsep +1}
        for(k in (nsep+1): (nrow(Jnew$links)+1))
        {
          Jnew$seps[[k]] <- sort(intersect(Jnew$clqs[[Jnew$links[k-1,1]]],Jnew$clqs[[Jnew$links[k-1,2]]]))
          #sep.add <- append(sep.add, Jnew$seps[[k]])
          #print(sep.add)
        }
        sep.add <- Jnew$seps[(nsep+1): (nrow(Jnew$links)+1)]
        type= "a"
        mx=length(x) + length(s)
        my= length(x) + length(s)
        # type b
      } else if(is.null(cy) & !is.null(cx)){
        if(!setequal(scrNx, cx)){
          Jnew <- J
          x <- NULL
          y <- NULL
          q <- 0
        } else{
          # add and delete clique
          clq.del <- J$clqs[[l]]
          Jnew$clqs <- J$clqs
          clq.add <- list(sort(union(y,s)))
          Jnew$clqs[[l]] <- unlist(clq.add)
          # add and delete links
          Jnew$links <- J$links 
          link.edit <- which(apply(J$links,1,function(z){setequal(z,c(cx,l))}))
          # add and delete separators
          sep.del <- J$seps[[link.edit+1]]
          sep.del <- ifelse(is.list(sep.del),sep.del, list(sep.del))
          Jnew$seps <- J$seps
          sep.add <- list(sort(s))
          Jnew$seps[[link.edit+1]] <- sep.add[[1]]
          my <- length(union(y,s))
          mx <- length(Jnew$clqs[[cx]])
        }
        type= "b"
        # type c
      } else if(!is.null(cy) & is.null(cx)){
        if(!setequal(scrNy, cy)){
          Jnew <- J
          x <- NULL
          y <- NULL
          q <- 0
        } else{
          # add and delete clique
          clq.del <- J$clqs[[l]]
          Jnew$clqs <- J$clqs
          clq.add <- list(sort(union(x,s)))
          Jnew$clqs[[l]] <- unlist(clq.add)
          # add and delete links
          Jnew$links <- J$links 
          link.edit <- which(apply(J$links,1,function(z){setequal(z,c(cy,l))}))
          # add and delete separators
          sep.del <- J$seps[[link.edit+1]]
          sep.del <- ifelse(is.list(sep.del),sep.del, list(sep.del))
          Jnew$seps <- J$seps
          sep.add <- list(sort(s))
          Jnew$seps[[link.edit+1]] <- sep.add[[1]]
          mx <- length(union(x,s))
          my <- length(Jnew$clqs[[cy]])
        } 
        type= "c"
        #type d
      }  else if(!is.null(cy) & !is.null(cx)){
        if(length(scrN) !=0 | length(scrNx) > 1 | length(scrNy) > 1 ){
          Jnew <- J
          x <- NULL
          y <- NULL
          q <- 0
        } else{
          # add and delete clique
          clq.del <- J$clqs[[l]]
          Jnew$clqs <- J$clqs[-l]
          # add and delete links
          link.edit <- which(apply(J$links,1,function(z){setequal(z,c(cy,l)) | setequal(z,c(cx,l))}))
          Jnew$links <- J$links[-link.edit,]
          Jnew$links <- rbind(Jnew$links, sort(c(cx,cy)))
          Jnew$links[which(Jnew$links > l)] <- Jnew$links[which(Jnew$links > l)] - 1
          # add and delete separators
          sep.del <- J$seps[link.edit+1]
          Jnew$seps <- J$seps[-(link.edit+1)]
          sep.add <- list(sort(s))
          Jnew$seps <- append(Jnew$seps, sep.add)
          my <- length(J$clqs[[cy]])
          mx <- length(J$clqs[[cx]])
        }
        type= "d"
      }  
    }
  }
  # add a condition to restrict maximum cliques and not allow cliques at more than lag.clique
  if(any(sapply(Jnew$clqs,length)>max.clique) | any(sapply(Jnew$clqs,function(x){max(x)-min(x)})>lag.clique)){
    Jnew <- J
    q <- 0
    x <- NULL
    y <- NULL
    clq.del <- clq.add <- sep.del <- sep.add <- list()
  }
  if(!is.list(clq.add)){
    clq.add <- list(clq.add)
  }
  if(!is.list(clq.del)){
    clq.del <- list(clq.del)
  }
  if(!is.list(sep.add)){
    sep.add <- list(sep.add)
  }
  if(!is.list(sep.del)){
    sep.del <- list(sep.del)
  }
  
  return(list(J=Jnew, x=x, y=y, l=l, s=s, mx = mx, my = my, type= type, move=move, prob=q, sep.add=sep.add, sep.del=sep.del, clq.add=clq.add, clq.del=clq.del) )
}



# is.connected(graph_from_edgelist(J$links,directed = F))
# all(sapply(2:length(J$seps),function(z){setequal(J$seps[[z]], intersect(J$clqs[[J$links[z-1,1]]], J$clqs[[J$links[z-1,2]]]))}))


#randomizing junction tree
randomize.jt <- function(J){
  #creating graph
  #jt.edge <- J$links[sapply(J$seps, function(y){(length(y)>0)})[-1],]
  J$links <- rbind(J$links)
  jt.edge <- J$links
  jt.graph <- graph_from_edgelist(jt.edge,directed=F)
  
  Jnew <- J
  Jnew$links <- c(0,0)
  Jnew$seps <- list()
  Jnew$seps[[1]] <- NULL
  link.count <- 1
  sep.count <- 2
  
  if(nrow(jt.edge)==0){
    Jnew <- J
  } else{
  jt.links <- apply(jt.edge,1,function(z){z <- as.numeric(z); y <- intersect(J$clqs[[z[1]]],J$clqs[[z[2]]]); paste(y,collapse=", ")})
  # creating separator vector
  sep.vec <- unlist(lapply(J$seps,function(x){paste(x,collapse=", ")}))[-1]
  # finding nu(s) for other separators
  for(k in 1:length(unique(sep.vec))){
    sep <- unique(sep.vec)[k]
    sep.c <- unlist(str_split(sep,", "))
    ms <- sum(sep.vec==sep)
    if(sep == ""){
      ts.ind <- 1:length(J$clqs)
      ts <- length(ts.ind)
    } else {
      ts.ind <- which(sapply(J$clqs, function(x){sum(x %in% sep.c)== length(sep.c)}))
      ts <- length(ts.ind)
    }
    Fs <- induced_subgraph(delete_edges(jt.graph, edges= which(jt.links == sep)), vids= ts.ind)
    Fs.comp <- clusters(Fs)$membership
    q <- length(clusters(Fs)$csize)
    p <- sum(clusters(Fs)$csize)
    vertex.Fs <- as.numeric(V(Fs))
    label.Fs <- matrix(nrow=length(vertex.Fs),ncol=2)
    count <- numeric(length(Fs.comp))
    for(k1 in vertex.Fs){
      i <- Fs.comp[k1]
      count[i] <- count[i]+1
      label.Fs[k1,1] <- i
      label.Fs[k1,2] <- count[i]
    }
    # choose q-2 vertices at random
    v <- sample(vertex.Fs, size=q-2, replace = TRUE)
    w <- sapply(1:q, function(z){sub.z <- which(label.Fs[,1]==z); if(length(sub.z)==1){sub.z} else {sample(sub.z, size=1)}})
    while(length(v)){
      w_v <- which(!(label.Fs[w,1] %in% label.Fs[v,1]))
      x.ind <- w_v[which.max(label.Fs[w,1][w_v])]
      x <- w[x.ind]
      y <- v[1]
      Jnew$links <- rbind(Jnew$links,c(ts.ind[x],ts.ind[y]))
      Jnew$seps[[sep.count]] <- intersect(J$clqs[[ts.ind[x]]],J$clqs[[ts.ind[y]]])
      link.count <- link.count + 1
      sep.count <- sep.count + 1
      v <- v[-1]
      w <- w[-x.ind]
    }
    Jnew$links <- rbind(Jnew$links,c(ts.ind[w[1]],ts.ind[w[2]]))
    Jnew$seps[[sep.count]] <- intersect(J$clqs[[ts.ind[w[1]]]],J$clqs[[ts.ind[w[2]]]])
    link.count <- link.count+1
    sep.count <- sep.count + 1
  }
  Jnew$links <- Jnew$links[-1,]
  Jnew$links <- rbind(Jnew$links)
  }
  return(Jnew)
}

# reverse probabilities
add.reverse.prob <- function(Jlist){
  J <- Jlist
  nx = length(J$x)
  ny = length(J$y)
  s = length(J$s)
  cj = length(J$J$clqs)
  m = nx + ny + s
  N = nx
  x = J$x
  y = J$y
  move= J$move
  
  if(J$type=="a"){
    l= J$typea.clq
    nbr <- unlist(apply(J$J$links,1, function(z){if(any(z %in% l)){z[z != l]}}))
    scrN <- tryCatch(sum(sapply(J$J$clqs[nbr], function(z){!any(z %in% c(x,y))})), error = function(e) 0)
    if(move=="single"){
      q <- 1/cj * 2/(m*(m-1)) * 2^(-scrN)
    } else {
      q <- 1/(cj) * 2/ ((m-1)*(M-1)) * (factorial(N)* factorial(M-N)* factorial(m-M))/(factorial(m)) 
    }} else {
      if(move=="single"){
        q <- 1/cj * 2/(m*(m-1)) 
      } else {
        q <- 1/(cj) * 2/ ((m-1)*(M-1)) * (factorial(N)* factorial(M-N)* factorial(m-M))/(factorial(m))
      }} 
  return(q)
}

remove.reverse.prob <- function(Jlist){
  J <- Jlist
  nx = length(J$x)
  ny = length(J$y)
  s = length(J$s)
  mx = J$mx
  my = J$my
  cj = length(J$J$clqs)
  m = nx + ny + s
  N = nx
  x = J$x
  y = J$y
  move= J$move
  type= J$type
  
  if(type=="a"){
    #mx = nx + s
    #my = ny + s
    q <- 1/((length(J$J$seps)-1)* (mx-s) * (my-s))
  } else if(type== "b"){
    #mx = mx
    #my=ny + s
    if(move=="single"){
      q <- 1/((length(J$J$seps)-1)* (mx-s) * (my-s))
    } else {
      q <- 1/((length(J$J$seps)-1)* (mx-s) * (my-s) *  choose(mx-s, nx) * choose(my-s, ny))
    }} else if(type== "c"){
      #mx = nx + s
      #my= my
      if(move=="single"){
        q <- 1/((length(J$J$seps)-1)* (mx-s) * (my-s))
      } else {
        q <- 1/((length(J$J$seps)-1)* (mx-s) * (my-s) *  choose(mx-s, nx) * choose(my-s, ny))
      }} else {
        if(move=="single"){
          q <- 1/((length(J$J$seps)-1)* (mx-s) * (my-s))
        } else {
          q <- 1/((length(J$J$seps)-1)* (mx-s) * (my-s) *  choose(mx-s, nx) * choose(my-s, ny))
        }
      }
  
  return(q)
}

list.check <- function (L){
  all(lapply(L, length)==0) | (length(L) == 0)
}

list.sum <- function(L,id){
  if(length(L)==0){
    0
  } else{
    sum(unlist(lapply(L,function(x){x[[id]]})))
  }
}

match.list <- function(L1,L2){
  L1 <- lapply(L1,sort)
  L2 <- lapply(L2,sort)
  match(L1,L2)
}
