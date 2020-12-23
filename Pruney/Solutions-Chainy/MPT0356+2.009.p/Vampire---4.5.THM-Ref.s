%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   64 (  97 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  202 ( 348 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(subsumption_resolution,[],[f196,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f196,plain,(
    ~ r1_tarski(sK3,sK3) ),
    inference(resolution,[],[f176,f150])).

fof(f150,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f148,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f148,plain,(
    r1_tarski(sK2,k4_xboole_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f145,f35])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(sK3,k3_subset_1(sK1,sK2))
    & r1_tarski(sK2,k3_subset_1(sK1,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
            & r1_tarski(X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(sK1,sK2))
          & r1_tarski(sK2,k3_subset_1(sK1,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,k3_subset_1(sK1,sK2))
        & r1_tarski(sK2,k3_subset_1(sK1,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
   => ( ~ r1_tarski(sK3,k3_subset_1(sK1,sK2))
      & r1_tarski(sK2,k3_subset_1(sK1,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,k3_subset_1(X0,X2))
             => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(f145,plain,
    ( r1_tarski(sK2,k4_xboole_0(sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f36,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f36,plain,(
    r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f176,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(sK2,X1)
      | ~ r1_tarski(sK3,X1) ) ),
    inference(resolution,[],[f174,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f55,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f174,plain,(
    ~ r1_xboole_0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f172,f118])).

fof(f118,plain,(
    r1_tarski(sK3,sK1) ),
    inference(resolution,[],[f116,f78])).

fof(f78,plain,(
    r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f75,f38])).

fof(f38,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f75,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f39,f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f49,f61])).

fof(f61,plain,(
    ! [X0] : sP0(X0,k1_zfmisc_1(X0)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f6,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | r1_tarski(X3,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f172,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | ~ r1_tarski(sK3,sK1) ),
    inference(resolution,[],[f58,f149])).

fof(f149,plain,(
    ~ r1_tarski(sK3,k4_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f146,f34])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f146,plain,
    ( ~ r1_tarski(sK3,k4_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f37,f43])).

fof(f37,plain,(
    ~ r1_tarski(sK3,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:55:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (29796)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (29799)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (29816)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (29798)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (29800)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (29808)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (29798)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 1.24/0.51  % (29806)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.24/0.51  % SZS output start Proof for theBenchmark
% 1.24/0.51  fof(f200,plain,(
% 1.24/0.51    $false),
% 1.24/0.51    inference(subsumption_resolution,[],[f196,f59])).
% 1.24/0.51  fof(f59,plain,(
% 1.24/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.24/0.51    inference(equality_resolution,[],[f45])).
% 1.24/0.51  fof(f45,plain,(
% 1.24/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.24/0.51    inference(cnf_transformation,[],[f27])).
% 1.24/0.51  fof(f27,plain,(
% 1.24/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.24/0.51    inference(flattening,[],[f26])).
% 1.24/0.51  fof(f26,plain,(
% 1.24/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.24/0.51    inference(nnf_transformation,[],[f1])).
% 1.24/0.51  fof(f1,axiom,(
% 1.24/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.24/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.24/0.51  fof(f196,plain,(
% 1.24/0.51    ~r1_tarski(sK3,sK3)),
% 1.24/0.51    inference(resolution,[],[f176,f150])).
% 1.24/0.51  fof(f150,plain,(
% 1.24/0.51    r1_xboole_0(sK2,sK3)),
% 1.24/0.51    inference(resolution,[],[f148,f57])).
% 1.24/0.51  fof(f57,plain,(
% 1.24/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.24/0.51    inference(cnf_transformation,[],[f17])).
% 1.24/0.51  fof(f17,plain,(
% 1.24/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.24/0.51    inference(ennf_transformation,[],[f2])).
% 1.24/0.51  fof(f2,axiom,(
% 1.24/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.24/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.24/0.52  fof(f148,plain,(
% 1.24/0.52    r1_tarski(sK2,k4_xboole_0(sK1,sK3))),
% 1.24/0.52    inference(subsumption_resolution,[],[f145,f35])).
% 1.24/0.52  fof(f35,plain,(
% 1.24/0.52    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 1.24/0.52    inference(cnf_transformation,[],[f24])).
% 1.24/0.52  fof(f24,plain,(
% 1.24/0.52    (~r1_tarski(sK3,k3_subset_1(sK1,sK2)) & r1_tarski(sK2,k3_subset_1(sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 1.24/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f23,f22])).
% 1.24/0.52  fof(f22,plain,(
% 1.24/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(X2,k3_subset_1(sK1,sK2)) & r1_tarski(sK2,k3_subset_1(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f23,plain,(
% 1.24/0.52    ? [X2] : (~r1_tarski(X2,k3_subset_1(sK1,sK2)) & r1_tarski(sK2,k3_subset_1(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) => (~r1_tarski(sK3,k3_subset_1(sK1,sK2)) & r1_tarski(sK2,k3_subset_1(sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1)))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f13,plain,(
% 1.24/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.24/0.52    inference(flattening,[],[f12])).
% 1.24/0.52  fof(f12,plain,(
% 1.24/0.52    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.24/0.52    inference(ennf_transformation,[],[f11])).
% 1.24/0.52  fof(f11,negated_conjecture,(
% 1.24/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.24/0.52    inference(negated_conjecture,[],[f10])).
% 1.24/0.52  fof(f10,conjecture,(
% 1.24/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).
% 1.24/0.52  fof(f145,plain,(
% 1.24/0.52    r1_tarski(sK2,k4_xboole_0(sK1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 1.24/0.52    inference(superposition,[],[f36,f43])).
% 1.24/0.52  fof(f43,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.24/0.52    inference(cnf_transformation,[],[f15])).
% 1.24/0.52  fof(f15,plain,(
% 1.24/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.24/0.52    inference(ennf_transformation,[],[f8])).
% 1.24/0.52  fof(f8,axiom,(
% 1.24/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.24/0.52  fof(f36,plain,(
% 1.24/0.52    r1_tarski(sK2,k3_subset_1(sK1,sK3))),
% 1.24/0.52    inference(cnf_transformation,[],[f24])).
% 1.24/0.52  fof(f176,plain,(
% 1.24/0.52    ( ! [X1] : (~r1_xboole_0(sK2,X1) | ~r1_tarski(sK3,X1)) )),
% 1.24/0.52    inference(resolution,[],[f174,f87])).
% 1.24/0.52  fof(f87,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (r1_xboole_0(X2,X0) | ~r1_tarski(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.24/0.52    inference(superposition,[],[f55,f47])).
% 1.24/0.52  fof(f47,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f28])).
% 1.24/0.52  fof(f28,plain,(
% 1.24/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.24/0.52    inference(nnf_transformation,[],[f3])).
% 1.24/0.52  fof(f3,axiom,(
% 1.24/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.24/0.52  fof(f55,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f16])).
% 1.24/0.52  fof(f16,plain,(
% 1.24/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.24/0.52    inference(ennf_transformation,[],[f4])).
% 1.24/0.52  fof(f4,axiom,(
% 1.24/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.24/0.52  fof(f174,plain,(
% 1.24/0.52    ~r1_xboole_0(sK3,sK2)),
% 1.24/0.52    inference(subsumption_resolution,[],[f172,f118])).
% 1.24/0.52  fof(f118,plain,(
% 1.24/0.52    r1_tarski(sK3,sK1)),
% 1.24/0.52    inference(resolution,[],[f116,f78])).
% 1.24/0.52  fof(f78,plain,(
% 1.24/0.52    r2_hidden(sK3,k1_zfmisc_1(sK1))),
% 1.24/0.52    inference(subsumption_resolution,[],[f75,f38])).
% 1.24/0.52  fof(f38,plain,(
% 1.24/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.24/0.52    inference(cnf_transformation,[],[f9])).
% 1.24/0.52  fof(f9,axiom,(
% 1.24/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.24/0.52  fof(f75,plain,(
% 1.24/0.52    r2_hidden(sK3,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1))),
% 1.24/0.52    inference(resolution,[],[f39,f35])).
% 1.24/0.52  fof(f39,plain,(
% 1.24/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f25])).
% 1.24/0.52  fof(f25,plain,(
% 1.24/0.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.24/0.52    inference(nnf_transformation,[],[f14])).
% 1.24/0.52  fof(f14,plain,(
% 1.24/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.24/0.52    inference(ennf_transformation,[],[f7])).
% 1.24/0.52  fof(f7,axiom,(
% 1.24/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.24/0.52  fof(f116,plain,(
% 1.24/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.24/0.52    inference(resolution,[],[f49,f61])).
% 1.24/0.52  fof(f61,plain,(
% 1.24/0.52    ( ! [X0] : (sP0(X0,k1_zfmisc_1(X0))) )),
% 1.24/0.52    inference(equality_resolution,[],[f53])).
% 1.24/0.52  fof(f53,plain,(
% 1.24/0.52    ( ! [X0,X1] : (sP0(X0,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.24/0.52    inference(cnf_transformation,[],[f33])).
% 1.24/0.52  fof(f33,plain,(
% 1.24/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_zfmisc_1(X0) != X1))),
% 1.24/0.52    inference(nnf_transformation,[],[f21])).
% 1.24/0.52  fof(f21,plain,(
% 1.24/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> sP0(X0,X1))),
% 1.24/0.52    inference(definition_folding,[],[f6,f20])).
% 1.24/0.52  fof(f20,plain,(
% 1.24/0.52    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.24/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.24/0.52  fof(f6,axiom,(
% 1.24/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.24/0.52  fof(f49,plain,(
% 1.24/0.52    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r2_hidden(X3,X1) | r1_tarski(X3,X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f32])).
% 1.24/0.52  fof(f32,plain,(
% 1.24/0.52    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 1.24/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 1.24/0.52  fof(f31,plain,(
% 1.24/0.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f30,plain,(
% 1.24/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 1.24/0.52    inference(rectify,[],[f29])).
% 1.24/0.52  fof(f29,plain,(
% 1.24/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 1.24/0.52    inference(nnf_transformation,[],[f20])).
% 1.24/0.52  fof(f172,plain,(
% 1.24/0.52    ~r1_xboole_0(sK3,sK2) | ~r1_tarski(sK3,sK1)),
% 1.24/0.52    inference(resolution,[],[f58,f149])).
% 1.24/0.52  fof(f149,plain,(
% 1.24/0.52    ~r1_tarski(sK3,k4_xboole_0(sK1,sK2))),
% 1.24/0.52    inference(subsumption_resolution,[],[f146,f34])).
% 1.24/0.52  fof(f34,plain,(
% 1.24/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 1.24/0.52    inference(cnf_transformation,[],[f24])).
% 1.24/0.52  fof(f146,plain,(
% 1.24/0.52    ~r1_tarski(sK3,k4_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 1.24/0.52    inference(superposition,[],[f37,f43])).
% 1.24/0.52  fof(f37,plain,(
% 1.24/0.52    ~r1_tarski(sK3,k3_subset_1(sK1,sK2))),
% 1.24/0.52    inference(cnf_transformation,[],[f24])).
% 1.24/0.52  fof(f58,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f19])).
% 1.24/0.52  fof(f19,plain,(
% 1.24/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 1.24/0.52    inference(flattening,[],[f18])).
% 1.24/0.52  fof(f18,plain,(
% 1.24/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.24/0.52    inference(ennf_transformation,[],[f5])).
% 1.24/0.52  fof(f5,axiom,(
% 1.24/0.52    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 1.24/0.52  % SZS output end Proof for theBenchmark
% 1.24/0.52  % (29798)------------------------------
% 1.24/0.52  % (29798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (29798)Termination reason: Refutation
% 1.24/0.52  
% 1.24/0.52  % (29798)Memory used [KB]: 6140
% 1.24/0.52  % (29798)Time elapsed: 0.097 s
% 1.24/0.52  % (29798)------------------------------
% 1.24/0.52  % (29798)------------------------------
% 1.24/0.52  % (29807)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.24/0.52  % (29793)Success in time 0.158 s
%------------------------------------------------------------------------------
