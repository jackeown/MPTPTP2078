%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  144 (3328 expanded)
%              Number of leaves         :   22 (1002 expanded)
%              Depth                    :   31
%              Number of atoms          :  495 (20797 expanded)
%              Number of equality atoms :   90 (4640 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f549,plain,(
    $false ),
    inference(subsumption_resolution,[],[f449,f548])).

fof(f548,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,X0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f547,f433])).

fof(f433,plain,(
    ! [X0,X1] : sP2(k1_xboole_0,X0,X1) ),
    inference(subsumption_resolution,[],[f432,f142])).

fof(f142,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f139,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f139,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f138,f129])).

fof(f129,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f106,f127])).

fof(f127,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(resolution,[],[f124,f111])).

fof(f111,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f76,f106])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f124,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f119,f103])).

% (10859)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f103,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f95,f102])).

fof(f102,plain,(
    k1_xboole_0 = sK11 ),
    inference(resolution,[],[f65,f95])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f95,plain,(
    v1_xboole_0(sK11) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    v1_xboole_0(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f4,f53])).

fof(f53,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK11) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f119,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | X1 = X2
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f72,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f74,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f106,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f64,f98])).

fof(f98,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f94,f103])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f432,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1))
      | sP2(k1_xboole_0,X0,X1) ) ),
    inference(forward_demodulation,[],[f423,f419])).

fof(f419,plain,(
    k1_xboole_0 = sK5 ),
    inference(forward_demodulation,[],[f418,f98])).

fof(f418,plain,(
    sK5 = k2_zfmisc_1(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f417,f365])).

fof(f365,plain,(
    k1_xboole_0 = sK4 ),
    inference(resolution,[],[f360,f65])).

fof(f360,plain,(
    v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f359,f178])).

fof(f178,plain,(
    sP2(sK5,sK3,sK4) ),
    inference(resolution,[],[f175,f56])).

fof(f56,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5))
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 != sK4 )
    & r1_partfun1(sK5,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f15,f28,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(sK3,sK4,sK5))
          & ( k1_xboole_0 = sK3
            | k1_xboole_0 != sK4 )
          & r1_partfun1(sK5,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ~ r2_hidden(X3,k5_partfun1(sK3,sK4,sK5))
        & ( k1_xboole_0 = sK3
          | k1_xboole_0 != sK4 )
        & r1_partfun1(sK5,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
        & v1_funct_2(X3,sK3,sK4)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5))
      & ( k1_xboole_0 = sK3
        | k1_xboole_0 != sK4 )
      & r1_partfun1(sK5,sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(sK5,X0,X1) ) ),
    inference(resolution,[],[f93,f55])).

fof(f55,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( sP2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f21,f25,f24,f23])).

fof(f23,plain,(
    ! [X2,X0,X4,X1] :
      ( sP0(X2,X0,X4,X1)
    <=> ? [X5] :
          ( r1_partfun1(X2,X5)
          & v1_partfun1(X5,X0)
          & X4 = X5
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X5) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X1,X0,X2,X3] :
      ( sP1(X1,X0,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP0(X2,X0,X4,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP1(X1,X0,X2,X3) )
      | ~ sP2(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f359,plain,
    ( v1_xboole_0(sK4)
    | ~ sP2(sK5,sK3,sK4) ),
    inference(subsumption_resolution,[],[f358,f62])).

fof(f62,plain,(
    ~ r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f29])).

fof(f358,plain,
    ( r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5))
    | v1_xboole_0(sK4)
    | ~ sP2(sK5,sK3,sK4) ),
    inference(resolution,[],[f351,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0,k5_partfun1(X1,X2,X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k5_partfun1(X1,X2,X0) != X3
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X2,X0) = X3
            | ~ sP1(X2,X1,X0,X3) )
          & ( sP1(X2,X1,X0,X3)
            | k5_partfun1(X1,X2,X0) != X3 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP1(X1,X0,X2,X3) )
          & ( sP1(X1,X0,X2,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP2(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f351,plain,(
    ! [X0] :
      ( ~ sP1(sK4,sK3,sK5,X0)
      | r2_hidden(sK6,X0)
      | v1_xboole_0(sK4) ) ),
    inference(resolution,[],[f347,f84])).

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X2,X1,X5,X0)
      | r2_hidden(X5,X3)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ sP0(X2,X1,sK9(X0,X1,X2,X3),X0)
            | ~ r2_hidden(sK9(X0,X1,X2,X3),X3) )
          & ( sP0(X2,X1,sK9(X0,X1,X2,X3),X0)
            | r2_hidden(sK9(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X2,X1,X5,X0) )
            & ( sP0(X2,X1,X5,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f46,f47])).

fof(f47,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP0(X2,X1,X4,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP0(X2,X1,X4,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP0(X2,X1,sK9(X0,X1,X2,X3),X0)
          | ~ r2_hidden(sK9(X0,X1,X2,X3),X3) )
        & ( sP0(X2,X1,sK9(X0,X1,X2,X3),X0)
          | r2_hidden(sK9(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f347,plain,
    ( sP0(sK5,sK3,sK6,sK4)
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f346,f59])).

fof(f59,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f29])).

fof(f346,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | sP0(sK5,sK3,sK6,X0)
      | v1_xboole_0(sK4) ) ),
    inference(resolution,[],[f344,f335])).

fof(f335,plain,
    ( v1_partfun1(sK6,sK3)
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f334,f59])).

fof(f334,plain,
    ( v1_partfun1(sK6,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_xboole_0(sK4) ),
    inference(subsumption_resolution,[],[f333,f57])).

fof(f57,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f333,plain,
    ( v1_partfun1(sK6,sK3)
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f69,f58])).

fof(f58,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f344,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK6,X0)
      | sP0(sK5,X0,sK6,X1)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f342,f57])).

fof(f342,plain,(
    ! [X0,X1] :
      ( sP0(sK5,X0,sK6,X1)
      | ~ v1_partfun1(sK6,X0)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK6) ) ),
    inference(resolution,[],[f101,f60])).

fof(f60,plain,(
    r1_partfun1(sK5,sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f101,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r1_partfun1(X0,X4)
      | sP0(X0,X1,X4,X3)
      | ~ v1_partfun1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | ~ r1_partfun1(X0,X4)
      | ~ v1_partfun1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r1_partfun1(X0,X4)
            | ~ v1_partfun1(X4,X1)
            | X2 != X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
            | ~ v1_funct_1(X4) ) )
      & ( ( r1_partfun1(X0,sK10(X0,X1,X2,X3))
          & v1_partfun1(sK10(X0,X1,X2,X3),X1)
          & sK10(X0,X1,X2,X3) = X2
          & m1_subset_1(sK10(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          & v1_funct_1(sK10(X0,X1,X2,X3)) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f50,f51])).

fof(f51,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_partfun1(X0,X5)
          & v1_partfun1(X5,X1)
          & X2 = X5
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
          & v1_funct_1(X5) )
     => ( r1_partfun1(X0,sK10(X0,X1,X2,X3))
        & v1_partfun1(sK10(X0,X1,X2,X3),X1)
        & sK10(X0,X1,X2,X3) = X2
        & m1_subset_1(sK10(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & v1_funct_1(sK10(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f417,plain,(
    sK5 = k2_zfmisc_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f416,f142])).

fof(f416,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5)
    | sK5 = k2_zfmisc_1(sK3,sK4) ),
    inference(forward_demodulation,[],[f373,f98])).

fof(f373,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,k1_xboole_0),sK5)
    | sK5 = k2_zfmisc_1(sK3,sK4) ),
    inference(backward_demodulation,[],[f122,f365])).

fof(f122,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,sK4),sK5)
    | sK5 = k2_zfmisc_1(sK3,sK4) ),
    inference(resolution,[],[f72,f108])).

fof(f108,plain,(
    r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f76,f56])).

fof(f423,plain,(
    ! [X0,X1] :
      ( sP2(k1_xboole_0,X0,X1)
      | ~ r1_tarski(sK5,k2_zfmisc_1(X0,X1)) ) ),
    inference(backward_demodulation,[],[f179,f419])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK5,k2_zfmisc_1(X0,X1))
      | sP2(sK5,X0,X1) ) ),
    inference(resolution,[],[f175,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f547,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,X0,k1_xboole_0))
      | ~ sP2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f540,f100])).

fof(f540,plain,(
    ! [X2,X1] :
      ( ~ sP1(X2,k1_xboole_0,k1_xboole_0,X1)
      | r2_hidden(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f538,f84])).

fof(f538,plain,(
    ! [X0] : sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f537,f129])).

fof(f537,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f536,f99])).

fof(f99,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f536,plain,(
    ! [X0] :
      ( sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(resolution,[],[f452,f133])).

fof(f133,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f63,f127])).

fof(f63,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f452,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(k1_xboole_0,X0)
      | sP0(k1_xboole_0,X0,k1_xboole_0,X1)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(forward_demodulation,[],[f451,f437])).

fof(f437,plain,(
    k1_xboole_0 = sK6 ),
    inference(forward_demodulation,[],[f436,f98])).

fof(f436,plain,(
    sK6 = k2_zfmisc_1(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f435,f365])).

fof(f435,plain,(
    k2_zfmisc_1(sK3,sK4) = sK6 ),
    inference(subsumption_resolution,[],[f434,f142])).

fof(f434,plain,
    ( ~ r1_tarski(k1_xboole_0,sK6)
    | k2_zfmisc_1(sK3,sK4) = sK6 ),
    inference(forward_demodulation,[],[f374,f98])).

fof(f374,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,k1_xboole_0),sK6)
    | k2_zfmisc_1(sK3,sK4) = sK6 ),
    inference(backward_demodulation,[],[f123,f365])).

fof(f123,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,sK4),sK6)
    | k2_zfmisc_1(sK3,sK4) = sK6 ),
    inference(resolution,[],[f72,f109])).

fof(f109,plain,(
    r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f76,f59])).

fof(f451,plain,(
    ! [X0,X1] :
      ( sP0(k1_xboole_0,X0,k1_xboole_0,X1)
      | ~ v1_partfun1(k1_xboole_0,X0)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(forward_demodulation,[],[f448,f437])).

fof(f448,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(k1_xboole_0,X0)
      | sP0(k1_xboole_0,X0,sK6,X1)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(backward_demodulation,[],[f425,f437])).

fof(f425,plain,(
    ! [X0,X1] :
      ( sP0(k1_xboole_0,X0,sK6,X1)
      | ~ v1_partfun1(sK6,X0)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(backward_demodulation,[],[f344,f419])).

fof(f449,plain,(
    ~ r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f429,f437])).

fof(f429,plain,(
    ~ r2_hidden(sK6,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f413,f419])).

fof(f413,plain,(
    ~ r2_hidden(sK6,k5_partfun1(k1_xboole_0,k1_xboole_0,sK5)) ),
    inference(forward_demodulation,[],[f370,f366])).

fof(f366,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f61,f365])).

fof(f61,plain,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f29])).

fof(f370,plain,(
    ~ r2_hidden(sK6,k5_partfun1(sK3,k1_xboole_0,sK5)) ),
    inference(backward_demodulation,[],[f62,f365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:53:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (10850)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.50  % (10861)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (10851)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (10846)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (10850)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f549,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f449,f548])).
% 0.22/0.53  fof(f548,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,X0,k1_xboole_0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f547,f433])).
% 0.22/0.53  fof(f433,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP2(k1_xboole_0,X0,X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f432,f142])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(resolution,[],[f139,f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f37,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(resolution,[],[f138,f129])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.53    inference(backward_demodulation,[],[f106,f127])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.22/0.53    inference(resolution,[],[f124,f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)),
% 0.22/0.53    inference(resolution,[],[f76,f106])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(resolution,[],[f119,f103])).
% 0.22/0.53  % (10859)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    inference(backward_demodulation,[],[f95,f102])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    k1_xboole_0 = sK11),
% 0.22/0.53    inference(resolution,[],[f65,f95])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    v1_xboole_0(sK11)),
% 0.22/0.53    inference(cnf_transformation,[],[f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    v1_xboole_0(sK11)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f4,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK11)),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ? [X0] : v1_xboole_0(X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ( ! [X2,X1] : (~v1_xboole_0(X2) | X1 = X2 | ~r1_tarski(X1,X2)) )),
% 0.22/0.53    inference(resolution,[],[f72,f115])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.22/0.53    inference(resolution,[],[f74,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.53    inference(rectify,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.53    inference(superposition,[],[f64,f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.53    inference(flattening,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) )),
% 0.22/0.53    inference(resolution,[],[f94,f103])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.53  fof(f432,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) | sP2(k1_xboole_0,X0,X1)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f423,f419])).
% 0.22/0.53  fof(f419,plain,(
% 0.22/0.53    k1_xboole_0 = sK5),
% 0.22/0.53    inference(forward_demodulation,[],[f418,f98])).
% 0.22/0.53  fof(f418,plain,(
% 0.22/0.53    sK5 = k2_zfmisc_1(sK3,k1_xboole_0)),
% 0.22/0.53    inference(forward_demodulation,[],[f417,f365])).
% 0.22/0.53  fof(f365,plain,(
% 0.22/0.53    k1_xboole_0 = sK4),
% 0.22/0.53    inference(resolution,[],[f360,f65])).
% 0.22/0.53  fof(f360,plain,(
% 0.22/0.53    v1_xboole_0(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f359,f178])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    sP2(sK5,sK3,sK4)),
% 0.22/0.53    inference(resolution,[],[f175,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    (~r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f15,f28,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (~r2_hidden(X3,k5_partfun1(sK3,sK4,sK5)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ? [X3] : (~r2_hidden(X3,k5_partfun1(sK3,sK4,sK5)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) => (~r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_partfun1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (? [X3] : (((~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.53    inference(negated_conjecture,[],[f12])).
% 0.22/0.53  fof(f12,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(sK5,X0,X1)) )),
% 0.22/0.53    inference(resolution,[],[f93,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    v1_funct_1(sK5)),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (sP2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.53    inference(definition_folding,[],[f21,f25,f24,f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X2,X0,X4,X1] : (sP0(X2,X0,X4,X1) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X1,X0,X2,X3] : (sP1(X1,X0,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP0(X2,X0,X4,X1)))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X2,X0,X1] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP1(X1,X0,X2,X3)) | ~sP2(X2,X0,X1))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.53    inference(flattening,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).
% 0.22/0.53  fof(f359,plain,(
% 0.22/0.53    v1_xboole_0(sK4) | ~sP2(sK5,sK3,sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f358,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ~r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5))),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f358,plain,(
% 0.22/0.53    r2_hidden(sK6,k5_partfun1(sK3,sK4,sK5)) | v1_xboole_0(sK4) | ~sP2(sK5,sK3,sK4)),
% 0.22/0.53    inference(resolution,[],[f351,f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k5_partfun1(X1,X2,X0)) | ~sP2(X0,X1,X2)) )),
% 0.22/0.53    inference(equality_resolution,[],[f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k5_partfun1(X1,X2,X0) != X3 | ~sP2(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X2,X0) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k5_partfun1(X1,X2,X0) != X3)) | ~sP2(X0,X1,X2))),
% 0.22/0.53    inference(rectify,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X2,X0,X1] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP1(X1,X0,X2,X3)) & (sP1(X1,X0,X2,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP2(X2,X0,X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f25])).
% 0.22/0.53  fof(f351,plain,(
% 0.22/0.53    ( ! [X0] : (~sP1(sK4,sK3,sK5,X0) | r2_hidden(sK6,X0) | v1_xboole_0(sK4)) )),
% 0.22/0.53    inference(resolution,[],[f347,f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X2,X0,X5,X3,X1] : (~sP0(X2,X1,X5,X0) | r2_hidden(X5,X3) | ~sP1(X0,X1,X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ((~sP0(X2,X1,sK9(X0,X1,X2,X3),X0) | ~r2_hidden(sK9(X0,X1,X2,X3),X3)) & (sP0(X2,X1,sK9(X0,X1,X2,X3),X0) | r2_hidden(sK9(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X2,X1,X5,X0)) & (sP0(X2,X1,X5,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f46,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ! [X3,X2,X1,X0] : (? [X4] : ((~sP0(X2,X1,X4,X0) | ~r2_hidden(X4,X3)) & (sP0(X2,X1,X4,X0) | r2_hidden(X4,X3))) => ((~sP0(X2,X1,sK9(X0,X1,X2,X3),X0) | ~r2_hidden(sK9(X0,X1,X2,X3),X3)) & (sP0(X2,X1,sK9(X0,X1,X2,X3),X0) | r2_hidden(sK9(X0,X1,X2,X3),X3))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X2,X1,X4,X0) | ~r2_hidden(X4,X3)) & (sP0(X2,X1,X4,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X2,X1,X5,X0)) & (sP0(X2,X1,X5,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.22/0.53    inference(rectify,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ! [X1,X0,X2,X3] : ((sP1(X1,X0,X2,X3) | ? [X4] : ((~sP0(X2,X0,X4,X1) | ~r2_hidden(X4,X3)) & (sP0(X2,X0,X4,X1) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP0(X2,X0,X4,X1)) & (sP0(X2,X0,X4,X1) | ~r2_hidden(X4,X3))) | ~sP1(X1,X0,X2,X3)))),
% 0.22/0.53    inference(nnf_transformation,[],[f24])).
% 0.22/0.53  fof(f347,plain,(
% 0.22/0.53    sP0(sK5,sK3,sK6,sK4) | v1_xboole_0(sK4)),
% 0.22/0.53    inference(resolution,[],[f346,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f346,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | sP0(sK5,sK3,sK6,X0) | v1_xboole_0(sK4)) )),
% 0.22/0.53    inference(resolution,[],[f344,f335])).
% 0.22/0.53  fof(f335,plain,(
% 0.22/0.53    v1_partfun1(sK6,sK3) | v1_xboole_0(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f334,f59])).
% 0.22/0.53  fof(f334,plain,(
% 0.22/0.53    v1_partfun1(sK6,sK3) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | v1_xboole_0(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f333,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    v1_funct_1(sK6)),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f333,plain,(
% 0.22/0.53    v1_partfun1(sK6,sK3) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | v1_xboole_0(sK4)),
% 0.22/0.53    inference(resolution,[],[f69,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    v1_funct_2(sK6,sK3,sK4)),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.53  fof(f344,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_partfun1(sK6,X0) | sP0(sK5,X0,sK6,X1) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f342,f57])).
% 0.22/0.53  fof(f342,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP0(sK5,X0,sK6,X1) | ~v1_partfun1(sK6,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK6)) )),
% 0.22/0.53    inference(resolution,[],[f101,f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    r1_partfun1(sK5,sK6)),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ( ! [X4,X0,X3,X1] : (~r1_partfun1(X0,X4) | sP0(X0,X1,X4,X3) | ~v1_partfun1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4)) )),
% 0.22/0.53    inference(equality_resolution,[],[f92])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | ~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4))) & ((r1_partfun1(X0,sK10(X0,X1,X2,X3)) & v1_partfun1(sK10(X0,X1,X2,X3),X1) & sK10(X0,X1,X2,X3) = X2 & m1_subset_1(sK10(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(sK10(X0,X1,X2,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f50,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ! [X3,X2,X1,X0] : (? [X5] : (r1_partfun1(X0,X5) & v1_partfun1(X5,X1) & X2 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(X5)) => (r1_partfun1(X0,sK10(X0,X1,X2,X3)) & v1_partfun1(sK10(X0,X1,X2,X3),X1) & sK10(X0,X1,X2,X3) = X2 & m1_subset_1(sK10(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(sK10(X0,X1,X2,X3))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r1_partfun1(X0,X4) | ~v1_partfun1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X4))) & (? [X5] : (r1_partfun1(X0,X5) & v1_partfun1(X5,X1) & X2 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_1(X5)) | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.53    inference(rectify,[],[f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ! [X2,X0,X4,X1] : ((sP0(X2,X0,X4,X1) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~sP0(X2,X0,X4,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f23])).
% 0.22/0.53  fof(f417,plain,(
% 0.22/0.53    sK5 = k2_zfmisc_1(sK3,sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f416,f142])).
% 0.22/0.53  fof(f416,plain,(
% 0.22/0.53    ~r1_tarski(k1_xboole_0,sK5) | sK5 = k2_zfmisc_1(sK3,sK4)),
% 0.22/0.53    inference(forward_demodulation,[],[f373,f98])).
% 0.22/0.53  fof(f373,plain,(
% 0.22/0.53    ~r1_tarski(k2_zfmisc_1(sK3,k1_xboole_0),sK5) | sK5 = k2_zfmisc_1(sK3,sK4)),
% 0.22/0.53    inference(backward_demodulation,[],[f122,f365])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    ~r1_tarski(k2_zfmisc_1(sK3,sK4),sK5) | sK5 = k2_zfmisc_1(sK3,sK4)),
% 0.22/0.53    inference(resolution,[],[f72,f108])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    r1_tarski(sK5,k2_zfmisc_1(sK3,sK4))),
% 0.22/0.53    inference(resolution,[],[f76,f56])).
% 0.22/0.53  fof(f423,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP2(k1_xboole_0,X0,X1) | ~r1_tarski(sK5,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(backward_demodulation,[],[f179,f419])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(sK5,k2_zfmisc_1(X0,X1)) | sP2(sK5,X0,X1)) )),
% 0.22/0.53    inference(resolution,[],[f175,f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f547,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,X0,k1_xboole_0)) | ~sP2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.22/0.53    inference(resolution,[],[f540,f100])).
% 0.22/0.53  fof(f540,plain,(
% 0.22/0.53    ( ! [X2,X1] : (~sP1(X2,k1_xboole_0,k1_xboole_0,X1) | r2_hidden(k1_xboole_0,X1)) )),
% 0.22/0.53    inference(resolution,[],[f538,f84])).
% 0.22/0.53  fof(f538,plain,(
% 0.22/0.53    ( ! [X0] : (sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f537,f129])).
% 0.22/0.53  fof(f537,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f536,f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f536,plain,(
% 0.22/0.53    ( ! [X0] : (sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.22/0.53    inference(resolution,[],[f452,f133])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.53    inference(superposition,[],[f63,f127])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f452,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_partfun1(k1_xboole_0,X0) | sP0(k1_xboole_0,X0,k1_xboole_0,X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f451,f437])).
% 0.22/0.53  fof(f437,plain,(
% 0.22/0.53    k1_xboole_0 = sK6),
% 0.22/0.53    inference(forward_demodulation,[],[f436,f98])).
% 0.22/0.53  fof(f436,plain,(
% 0.22/0.53    sK6 = k2_zfmisc_1(sK3,k1_xboole_0)),
% 0.22/0.53    inference(forward_demodulation,[],[f435,f365])).
% 0.22/0.53  fof(f435,plain,(
% 0.22/0.53    k2_zfmisc_1(sK3,sK4) = sK6),
% 0.22/0.53    inference(subsumption_resolution,[],[f434,f142])).
% 0.22/0.53  fof(f434,plain,(
% 0.22/0.53    ~r1_tarski(k1_xboole_0,sK6) | k2_zfmisc_1(sK3,sK4) = sK6),
% 0.22/0.53    inference(forward_demodulation,[],[f374,f98])).
% 0.22/0.53  fof(f374,plain,(
% 0.22/0.53    ~r1_tarski(k2_zfmisc_1(sK3,k1_xboole_0),sK6) | k2_zfmisc_1(sK3,sK4) = sK6),
% 0.22/0.53    inference(backward_demodulation,[],[f123,f365])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    ~r1_tarski(k2_zfmisc_1(sK3,sK4),sK6) | k2_zfmisc_1(sK3,sK4) = sK6),
% 0.22/0.53    inference(resolution,[],[f72,f109])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    r1_tarski(sK6,k2_zfmisc_1(sK3,sK4))),
% 0.22/0.53    inference(resolution,[],[f76,f59])).
% 0.22/0.53  fof(f451,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP0(k1_xboole_0,X0,k1_xboole_0,X1) | ~v1_partfun1(k1_xboole_0,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f448,f437])).
% 0.22/0.53  fof(f448,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_partfun1(k1_xboole_0,X0) | sP0(k1_xboole_0,X0,sK6,X1) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(backward_demodulation,[],[f425,f437])).
% 0.22/0.53  fof(f425,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP0(k1_xboole_0,X0,sK6,X1) | ~v1_partfun1(sK6,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(backward_demodulation,[],[f344,f419])).
% 0.22/0.53  fof(f449,plain,(
% 0.22/0.53    ~r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 0.22/0.53    inference(backward_demodulation,[],[f429,f437])).
% 0.22/0.53  fof(f429,plain,(
% 0.22/0.53    ~r2_hidden(sK6,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 0.22/0.53    inference(backward_demodulation,[],[f413,f419])).
% 0.22/0.53  fof(f413,plain,(
% 0.22/0.53    ~r2_hidden(sK6,k5_partfun1(k1_xboole_0,k1_xboole_0,sK5))),
% 0.22/0.53    inference(forward_demodulation,[],[f370,f366])).
% 0.22/0.53  fof(f366,plain,(
% 0.22/0.53    k1_xboole_0 = sK3),
% 0.22/0.53    inference(subsumption_resolution,[],[f61,f365])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    k1_xboole_0 != sK4 | k1_xboole_0 = sK3),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f370,plain,(
% 0.22/0.53    ~r2_hidden(sK6,k5_partfun1(sK3,k1_xboole_0,sK5))),
% 0.22/0.53    inference(backward_demodulation,[],[f62,f365])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (10850)------------------------------
% 0.22/0.53  % (10850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10850)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (10850)Memory used [KB]: 6524
% 0.22/0.53  % (10850)Time elapsed: 0.087 s
% 0.22/0.53  % (10850)------------------------------
% 0.22/0.53  % (10850)------------------------------
% 0.22/0.53  % (10842)Success in time 0.166 s
%------------------------------------------------------------------------------
