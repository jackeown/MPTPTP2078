%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 702 expanded)
%              Number of leaves         :   10 ( 222 expanded)
%              Depth                    :   18
%              Number of atoms          :  325 (4659 expanded)
%              Number of equality atoms :   37 ( 221 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f132,plain,(
    $false ),
    inference(global_subsumption,[],[f33,f131])).

fof(f131,plain,(
    ~ r1_partfun1(sK4,sK5) ),
    inference(resolution,[],[f129,f101])).

fof(f101,plain,(
    ~ sP0(sK4,k1_xboole_0,sK5,k1_xboole_0) ),
    inference(backward_demodulation,[],[f64,f90])).

fof(f90,plain,(
    k1_xboole_0 = sK3 ),
    inference(global_subsumption,[],[f33,f87])).

fof(f87,plain,
    ( ~ r1_partfun1(sK4,sK5)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f85,f64])).

fof(f85,plain,(
    ! [X0] :
      ( sP0(X0,sK3,sK5,sK3)
      | ~ r1_partfun1(X0,sK5)
      | k1_xboole_0 = sK3 ) ),
    inference(resolution,[],[f84,f82])).

fof(f82,plain,
    ( v1_partfun1(sK5,sK3)
    | k1_xboole_0 = sK3 ),
    inference(global_subsumption,[],[f31,f81])).

fof(f81,plain,
    ( k1_xboole_0 = sK3
    | ~ v1_funct_2(sK5,sK3,sK3)
    | v1_partfun1(sK5,sK3) ),
    inference(resolution,[],[f75,f32])).

fof(f32,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r2_hidden(sK5,k5_partfun1(sK3,sK3,sK4))
    & r1_partfun1(sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    & v1_funct_2(sK5,sK3,sK3)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f6,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,k5_partfun1(X0,X0,X1))
            & r1_partfun1(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(X2,k5_partfun1(sK3,sK3,sK4))
          & r1_partfun1(sK4,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
          & v1_funct_2(X2,sK3,sK3)
          & v1_funct_1(X2) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

% (24113)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f16,plain,
    ( ? [X2] :
        ( ~ r2_hidden(X2,k5_partfun1(sK3,sK3,sK4))
        & r1_partfun1(sK4,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
        & v1_funct_2(X2,sK3,sK3)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(sK5,k5_partfun1(sK3,sK3,sK4))
      & r1_partfun1(sK4,sK5)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
      & v1_funct_2(sK5,sK3,sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,k5_partfun1(X0,X0,X1))
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,k5_partfun1(X0,X0,X1))
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
             => r2_hidden(X2,k5_partfun1(X0,X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
           => r2_hidden(X2,k5_partfun1(X0,X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_funct_2)).

fof(f75,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | k1_xboole_0 = X2
      | ~ v1_funct_2(sK5,X3,X2)
      | v1_partfun1(sK5,X3) ) ),
    inference(resolution,[],[f53,f30])).

fof(f30,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f31,plain,(
    v1_funct_2(sK5,sK3,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_partfun1(sK5,sK3)
      | ~ r1_partfun1(X0,sK5)
      | sP0(X0,sK3,sK5,sK3) ) ),
    inference(resolution,[],[f78,f32])).

fof(f78,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_partfun1(sK5,X4)
      | ~ r1_partfun1(X3,sK5)
      | sP0(X3,X4,sK5,X5) ) ),
    inference(resolution,[],[f52,f30])).

fof(f52,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ r1_partfun1(X0,X4)
      | ~ v1_partfun1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | sP0(X0,X1,X4,X3) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | ~ r1_partfun1(X0,X4)
      | ~ v1_partfun1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r1_partfun1(X0,X4)
            | ~ v1_partfun1(X4,X1)
            | X2 != X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            | ~ v1_funct_1(X4) ) )
      & ( ( r1_partfun1(X0,sK7(X0,X1,X2,X3))
          & v1_partfun1(sK7(X0,X1,X2,X3),X1)
          & sK7(X0,X1,X2,X3) = X2
          & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          & v1_funct_1(sK7(X0,X1,X2,X3)) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f25,f26])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_partfun1(X0,X5)
          & v1_partfun1(X5,X1)
          & X2 = X5
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          & v1_funct_1(X5) )
     => ( r1_partfun1(X0,sK7(X0,X1,X2,X3))
        & v1_partfun1(sK7(X0,X1,X2,X3),X1)
        & sK7(X0,X1,X2,X3) = X2
        & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & v1_funct_1(sK7(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r1_partfun1(X0,X4)
            | ~ v1_partfun1(X4,X1)
            | X2 != X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            | ~ v1_funct_1(X4) ) )
      & ( ? [X5] :
            ( r1_partfun1(X0,X5)
            & v1_partfun1(X5,X1)
            & X2 = X5
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            & v1_funct_1(X5) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X4,X1] :
      ( ( sP0(X2,X0,X4,X1)
        | ! [X5] :
            ( ~ r1_partfun1(X2,X5)
            | ~ v1_partfun1(X5,X0)
            | X4 != X5
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_1(X5) ) )
      & ( ? [X5] :
            ( r1_partfun1(X2,X5)
            & v1_partfun1(X5,X0)
            & X4 = X5
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X5) )
        | ~ sP0(X2,X0,X4,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X2,X0,X4,X1] :
      ( sP0(X2,X0,X4,X1)
    <=> ? [X5] :
          ( r1_partfun1(X2,X5)
          & v1_partfun1(X5,X0)
          & X4 = X5
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X5) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f64,plain,(
    ~ sP0(sK4,sK3,sK5,sK3) ),
    inference(resolution,[],[f62,f34])).

fof(f34,plain,(
    ~ r2_hidden(sK5,k5_partfun1(sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(X0,k5_partfun1(sK3,sK3,sK4))
      | ~ sP0(sK4,sK3,X0,sK3) ) ),
    inference(resolution,[],[f40,f60])).

fof(f60,plain,(
    sP1(sK3,sK3,sK4,k5_partfun1(sK3,sK3,sK4)) ),
    inference(resolution,[],[f51,f58])).

fof(f58,plain,(
    sP2(sK4,sK3,sK3) ),
    inference(resolution,[],[f55,f29])).

fof(f29,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(sK4,X0,X1) ) ),
    inference(resolution,[],[f49,f28])).

fof(f28,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( sP2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f10,f13,f12,f11])).

% (24117)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f12,plain,(
    ! [X1,X0,X2,X3] :
      ( sP1(X1,X0,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP0(X2,X0,X4,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP1(X1,X0,X2,X3) )
      | ~ sP2(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | sP1(X2,X1,X0,k5_partfun1(X1,X2,X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k5_partfun1(X1,X2,X0) != X3
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X2,X0) = X3
            | ~ sP1(X2,X1,X0,X3) )
          & ( sP1(X2,X1,X0,X3)
            | k5_partfun1(X1,X2,X0) != X3 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP1(X1,X0,X2,X3) )
          & ( sP1(X1,X0,X2,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP2(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ sP0(X2,X1,X5,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ sP0(X2,X1,sK6(X0,X1,X2,X3),X0)
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( sP0(X2,X1,sK6(X0,X1,X2,X3),X0)
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X2,X1,X5,X0) )
            & ( sP0(X2,X1,X5,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f22])).

fof(f22,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP0(X2,X1,X4,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP0(X2,X1,X4,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP0(X2,X1,sK6(X0,X1,X2,X3),X0)
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( sP0(X2,X1,sK6(X0,X1,X2,X3),X0)
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X2,X1,X4,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X2,X1,X4,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X2,X1,X5,X0) )
            & ( sP0(X2,X1,X5,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X1,X0,X2,X3] :
      ( ( sP1(X1,X0,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X2,X0,X4,X1)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X2,X0,X4,X1)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP0(X2,X0,X4,X1) )
            & ( sP0(X2,X0,X4,X1)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X1,X0,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f129,plain,(
    ! [X0] :
      ( sP0(X0,k1_xboole_0,sK5,k1_xboole_0)
      | ~ r1_partfun1(X0,sK5) ) ),
    inference(subsumption_resolution,[],[f115,f128])).

fof(f128,plain,(
    v1_partfun1(sK5,k1_xboole_0) ),
    inference(global_subsumption,[],[f92,f124])).

fof(f124,plain,
    ( ~ v1_funct_2(sK5,k1_xboole_0,k1_xboole_0)
    | v1_partfun1(sK5,k1_xboole_0) ),
    inference(resolution,[],[f93,f72])).

fof(f72,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(sK5,k1_xboole_0,X1)
      | v1_partfun1(sK5,k1_xboole_0) ) ),
    inference(resolution,[],[f54,f30])).

fof(f54,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | v1_partfun1(X2,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f50])).

fof(f50,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f93,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f32,f90])).

fof(f92,plain,(
    v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f31,f90])).

fof(f115,plain,(
    ! [X0] :
      ( sP0(X0,k1_xboole_0,sK5,k1_xboole_0)
      | ~ v1_partfun1(sK5,k1_xboole_0)
      | ~ r1_partfun1(X0,sK5) ) ),
    inference(forward_demodulation,[],[f107,f90])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v1_partfun1(sK5,k1_xboole_0)
      | ~ r1_partfun1(X0,sK5)
      | sP0(X0,sK3,sK5,sK3) ) ),
    inference(backward_demodulation,[],[f84,f90])).

fof(f33,plain,(
    r1_partfun1(sK4,sK5) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:19:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (24095)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.49  % (24108)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.49  % (24119)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.50  % (24094)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (24100)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (24099)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (24108)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (24105)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (24097)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (24121)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(global_subsumption,[],[f33,f131])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    ~r1_partfun1(sK4,sK5)),
% 0.22/0.51    inference(resolution,[],[f129,f101])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    ~sP0(sK4,k1_xboole_0,sK5,k1_xboole_0)),
% 0.22/0.51    inference(backward_demodulation,[],[f64,f90])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    k1_xboole_0 = sK3),
% 0.22/0.51    inference(global_subsumption,[],[f33,f87])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ~r1_partfun1(sK4,sK5) | k1_xboole_0 = sK3),
% 0.22/0.51    inference(resolution,[],[f85,f64])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ( ! [X0] : (sP0(X0,sK3,sK5,sK3) | ~r1_partfun1(X0,sK5) | k1_xboole_0 = sK3) )),
% 0.22/0.51    inference(resolution,[],[f84,f82])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    v1_partfun1(sK5,sK3) | k1_xboole_0 = sK3),
% 0.22/0.51    inference(global_subsumption,[],[f31,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    k1_xboole_0 = sK3 | ~v1_funct_2(sK5,sK3,sK3) | v1_partfun1(sK5,sK3)),
% 0.22/0.51    inference(resolution,[],[f75,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    (~r2_hidden(sK5,k5_partfun1(sK3,sK3,sK4)) & r1_partfun1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(sK5,sK3,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_1(sK4)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f6,f16,f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0,X1] : (? [X2] : (~r2_hidden(X2,k5_partfun1(X0,X0,X1)) & r1_partfun1(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => (? [X2] : (~r2_hidden(X2,k5_partfun1(sK3,sK3,sK4)) & r1_partfun1(sK4,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(X2,sK3,sK3) & v1_funct_1(X2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_1(sK4))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  % (24113)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X2] : (~r2_hidden(X2,k5_partfun1(sK3,sK3,sK4)) & r1_partfun1(sK4,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(X2,sK3,sK3) & v1_funct_1(X2)) => (~r2_hidden(sK5,k5_partfun1(sK3,sK3,sK4)) & r1_partfun1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(sK5,sK3,sK3) & v1_funct_1(sK5))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f6,plain,(
% 0.22/0.51    ? [X0,X1] : (? [X2] : (~r2_hidden(X2,k5_partfun1(X0,X0,X1)) & r1_partfun1(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 0.22/0.51    inference(flattening,[],[f5])).
% 0.22/0.51  fof(f5,plain,(
% 0.22/0.51    ? [X0,X1] : (? [X2] : ((~r2_hidden(X2,k5_partfun1(X0,X0,X1)) & r1_partfun1(X1,X2)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) => r2_hidden(X2,k5_partfun1(X0,X0,X1)))))),
% 0.22/0.51    inference(negated_conjecture,[],[f3])).
% 0.22/0.51  fof(f3,conjecture,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) => r2_hidden(X2,k5_partfun1(X0,X0,X1)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_funct_2)).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | k1_xboole_0 = X2 | ~v1_funct_2(sK5,X3,X2) | v1_partfun1(sK5,X3)) )),
% 0.22/0.51    inference(resolution,[],[f53,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    v1_funct_1(sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    v1_funct_2(sK5,sK3,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_partfun1(sK5,sK3) | ~r1_partfun1(X0,sK5) | sP0(X0,sK3,sK5,sK3)) )),
% 0.22/0.51    inference(resolution,[],[f78,f32])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X4,X5,X3] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_partfun1(sK5,X4) | ~r1_partfun1(X3,sK5) | sP0(X3,X4,sK5,X5)) )),
% 0.22/0.51    inference(resolution,[],[f52,f30])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X4,X0,X3,X1] : (~v1_funct_1(X4) | ~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | sP0(X0,X1,X4,X3)) )),
% 0.22/0.51    inference(equality_resolution,[],[f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | ~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4))) & ((r1_partfun1(X0,sK7(X0,X1,X2,X3)) & v1_partfun1(sK7(X0,X1,X2,X3),X1) & sK7(X0,X1,X2,X3) = X2 & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(sK7(X0,X1,X2,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f25,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X3,X2,X1,X0] : (? [X5] : (r1_partfun1(X0,X5) & v1_partfun1(X5,X1) & X2 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(X5)) => (r1_partfun1(X0,sK7(X0,X1,X2,X3)) & v1_partfun1(sK7(X0,X1,X2,X3),X1) & sK7(X0,X1,X2,X3) = X2 & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(sK7(X0,X1,X2,X3))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4))) & (? [X5] : (r1_partfun1(X0,X5) & v1_partfun1(X5,X1) & X2 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(X5)) | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.51    inference(rectify,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X2,X0,X4,X1] : ((sP0(X2,X0,X4,X1) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~sP0(X2,X0,X4,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X2,X0,X4,X1] : (sP0(X2,X0,X4,X1) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ~sP0(sK4,sK3,sK5,sK3)),
% 0.22/0.51    inference(resolution,[],[f62,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ~r2_hidden(sK5,k5_partfun1(sK3,sK3,sK4))),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(X0,k5_partfun1(sK3,sK3,sK4)) | ~sP0(sK4,sK3,X0,sK3)) )),
% 0.22/0.51    inference(resolution,[],[f40,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    sP1(sK3,sK3,sK4,k5_partfun1(sK3,sK3,sK4))),
% 0.22/0.51    inference(resolution,[],[f51,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    sP2(sK4,sK3,sK3)),
% 0.22/0.51    inference(resolution,[],[f55,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(sK4,X0,X1)) )),
% 0.22/0.51    inference(resolution,[],[f49,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    v1_funct_1(sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (sP2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(definition_folding,[],[f10,f13,f12,f11])).
% 0.22/0.51  % (24117)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X1,X0,X2,X3] : (sP1(X1,X0,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP0(X2,X0,X4,X1)))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X2,X0,X1] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP1(X1,X0,X2,X3)) | ~sP2(X2,X0,X1))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | sP1(X2,X1,X0,k5_partfun1(X1,X2,X0))) )),
% 0.22/0.51    inference(equality_resolution,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k5_partfun1(X1,X2,X0) != X3 | ~sP2(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X2,X0) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k5_partfun1(X1,X2,X0) != X3)) | ~sP2(X0,X1,X2))),
% 0.22/0.51    inference(rectify,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X2,X0,X1] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP1(X1,X0,X2,X3)) & (sP1(X1,X0,X2,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP2(X2,X0,X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f13])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3) | ~sP0(X2,X1,X5,X0) | r2_hidden(X5,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ((~sP0(X2,X1,sK6(X0,X1,X2,X3),X0) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sP0(X2,X1,sK6(X0,X1,X2,X3),X0) | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X2,X1,X5,X0)) & (sP0(X2,X1,X5,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X3,X2,X1,X0] : (? [X4] : ((~sP0(X2,X1,X4,X0) | ~r2_hidden(X4,X3)) & (sP0(X2,X1,X4,X0) | r2_hidden(X4,X3))) => ((~sP0(X2,X1,sK6(X0,X1,X2,X3),X0) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sP0(X2,X1,sK6(X0,X1,X2,X3),X0) | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X2,X1,X4,X0) | ~r2_hidden(X4,X3)) & (sP0(X2,X1,X4,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X2,X1,X5,X0)) & (sP0(X2,X1,X5,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.22/0.51    inference(rectify,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X1,X0,X2,X3] : ((sP1(X1,X0,X2,X3) | ? [X4] : ((~sP0(X2,X0,X4,X1) | ~r2_hidden(X4,X3)) & (sP0(X2,X0,X4,X1) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP0(X2,X0,X4,X1)) & (sP0(X2,X0,X4,X1) | ~r2_hidden(X4,X3))) | ~sP1(X1,X0,X2,X3)))),
% 0.22/0.51    inference(nnf_transformation,[],[f12])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    ( ! [X0] : (sP0(X0,k1_xboole_0,sK5,k1_xboole_0) | ~r1_partfun1(X0,sK5)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f115,f128])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    v1_partfun1(sK5,k1_xboole_0)),
% 0.22/0.51    inference(global_subsumption,[],[f92,f124])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    ~v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) | v1_partfun1(sK5,k1_xboole_0)),
% 0.22/0.51    inference(resolution,[],[f93,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(sK5,k1_xboole_0,X1) | v1_partfun1(sK5,k1_xboole_0)) )),
% 0.22/0.51    inference(resolution,[],[f54,f30])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | v1_partfun1(X2,k1_xboole_0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.51    inference(equality_resolution,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.51    inference(backward_demodulation,[],[f32,f90])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    v1_funct_2(sK5,k1_xboole_0,k1_xboole_0)),
% 0.22/0.51    inference(backward_demodulation,[],[f31,f90])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    ( ! [X0] : (sP0(X0,k1_xboole_0,sK5,k1_xboole_0) | ~v1_partfun1(sK5,k1_xboole_0) | ~r1_partfun1(X0,sK5)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f107,f90])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_partfun1(sK5,k1_xboole_0) | ~r1_partfun1(X0,sK5) | sP0(X0,sK3,sK5,sK3)) )),
% 0.22/0.51    inference(backward_demodulation,[],[f84,f90])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    r1_partfun1(sK4,sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (24108)------------------------------
% 0.22/0.51  % (24108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (24108)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (24108)Memory used [KB]: 6268
% 0.22/0.51  % (24108)Time elapsed: 0.089 s
% 0.22/0.51  % (24108)------------------------------
% 0.22/0.51  % (24108)------------------------------
% 0.22/0.51  % (24090)Success in time 0.151 s
%------------------------------------------------------------------------------
