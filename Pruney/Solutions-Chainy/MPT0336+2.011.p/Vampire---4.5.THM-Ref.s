%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:24 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 101 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   15
%              Number of atoms          :  146 ( 297 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1208,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1207,f39])).

fof(f39,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f1207,plain,(
    ~ r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f1070,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1070,plain,(
    ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f974,f771])).

fof(f771,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f727,f114])).

fof(f114,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f51,f38])).

fof(f38,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f727,plain,
    ( r2_hidden(sK3,sK1)
    | r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f647,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f647,plain,
    ( ~ r1_xboole_0(k1_tarski(sK3),sK1)
    | r1_xboole_0(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f638])).

fof(f638,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(k1_tarski(sK3),sK1) ),
    inference(superposition,[],[f84,f554])).

fof(f554,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(k1_tarski(sK3),sK1) ),
    inference(resolution,[],[f372,f92])).

fof(f92,plain,(
    ! [X10,X8,X9] :
      ( r1_xboole_0(X10,k3_xboole_0(X9,X8))
      | ~ r1_xboole_0(X10,X8) ) ),
    inference(superposition,[],[f62,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f372,plain,
    ( ~ r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f210,f54])).

fof(f210,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f73,f37])).

fof(f37,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | ~ r1_xboole_0(X3,X4)
      | k1_xboole_0 = X3 ) ),
    inference(superposition,[],[f57,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f84,plain,(
    ! [X6,X5] :
      ( k1_xboole_0 != k3_xboole_0(X6,X5)
      | r1_xboole_0(X5,X6) ) ),
    inference(superposition,[],[f58,f45])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f974,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f973,f39])).

fof(f973,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(trivial_inequality_removal,[],[f968])).

fof(f968,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f963,f74])).

fof(f74,plain,(
    ! [X6,X5] :
      ( k1_xboole_0 = k3_xboole_0(X6,X5)
      | ~ r1_xboole_0(X5,X6) ) ),
    inference(superposition,[],[f57,f45])).

fof(f963,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f159,f63])).

fof(f63,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f54,f40])).

fof(f40,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f159,plain,(
    ! [X19,X17,X18] :
      ( r1_xboole_0(X17,k2_xboole_0(X18,X19))
      | k1_xboole_0 != k3_xboole_0(X17,X19)
      | ~ r1_xboole_0(X17,X18) ) ),
    inference(superposition,[],[f58,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:00:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (15282)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.44  % (15290)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.46  % (15294)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (15284)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (15293)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (15283)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (15291)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (15286)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (15289)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (15297)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (15295)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (15281)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (15285)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (15298)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (15292)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (15288)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (15296)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (15287)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.53/0.55  % (15284)Refutation found. Thanks to Tanya!
% 1.53/0.55  % SZS status Theorem for theBenchmark
% 1.53/0.55  % SZS output start Proof for theBenchmark
% 1.53/0.55  fof(f1208,plain,(
% 1.53/0.55    $false),
% 1.53/0.55    inference(subsumption_resolution,[],[f1207,f39])).
% 1.53/0.55  fof(f39,plain,(
% 1.53/0.55    r1_xboole_0(sK2,sK1)),
% 1.53/0.55    inference(cnf_transformation,[],[f32])).
% 1.53/0.55  fof(f32,plain,(
% 1.53/0.55    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.53/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f31])).
% 1.53/0.55  fof(f31,plain,(
% 1.53/0.55    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.53/0.55    introduced(choice_axiom,[])).
% 1.53/0.55  fof(f24,plain,(
% 1.53/0.55    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.53/0.55    inference(flattening,[],[f23])).
% 1.53/0.55  fof(f23,plain,(
% 1.53/0.55    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.53/0.55    inference(ennf_transformation,[],[f20])).
% 1.53/0.55  fof(f20,negated_conjecture,(
% 1.53/0.55    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.53/0.55    inference(negated_conjecture,[],[f19])).
% 1.53/0.55  fof(f19,conjecture,(
% 1.53/0.55    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.53/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.53/0.55  fof(f1207,plain,(
% 1.53/0.55    ~r1_xboole_0(sK2,sK1)),
% 1.53/0.55    inference(resolution,[],[f1070,f54])).
% 1.53/0.55  fof(f54,plain,(
% 1.53/0.55    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.55    inference(cnf_transformation,[],[f28])).
% 1.53/0.55  fof(f28,plain,(
% 1.53/0.55    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.53/0.55    inference(ennf_transformation,[],[f5])).
% 1.53/0.55  fof(f5,axiom,(
% 1.53/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.53/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.53/0.55  fof(f1070,plain,(
% 1.53/0.55    ~r1_xboole_0(sK1,sK2)),
% 1.53/0.55    inference(resolution,[],[f974,f771])).
% 1.53/0.55  fof(f771,plain,(
% 1.53/0.55    r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK1,sK2)),
% 1.53/0.55    inference(resolution,[],[f727,f114])).
% 1.53/0.55  fof(f114,plain,(
% 1.53/0.55    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 1.53/0.55    inference(resolution,[],[f51,f38])).
% 1.53/0.55  fof(f38,plain,(
% 1.53/0.55    r2_hidden(sK3,sK2)),
% 1.53/0.55    inference(cnf_transformation,[],[f32])).
% 1.53/0.55  fof(f51,plain,(
% 1.53/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.53/0.55    inference(cnf_transformation,[],[f34])).
% 1.53/0.55  fof(f34,plain,(
% 1.53/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.53/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f33])).
% 1.53/0.55  fof(f33,plain,(
% 1.53/0.55    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.53/0.55    introduced(choice_axiom,[])).
% 1.53/0.55  fof(f25,plain,(
% 1.53/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.53/0.55    inference(ennf_transformation,[],[f22])).
% 1.53/0.55  fof(f22,plain,(
% 1.53/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.55    inference(rectify,[],[f6])).
% 1.53/0.55  fof(f6,axiom,(
% 1.53/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.53/0.55  fof(f727,plain,(
% 1.53/0.55    r2_hidden(sK3,sK1) | r1_xboole_0(sK1,sK0)),
% 1.53/0.55    inference(resolution,[],[f647,f52])).
% 1.53/0.55  fof(f52,plain,(
% 1.53/0.55    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.53/0.55    inference(cnf_transformation,[],[f26])).
% 1.53/0.55  fof(f26,plain,(
% 1.53/0.55    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.53/0.55    inference(ennf_transformation,[],[f18])).
% 1.53/0.55  fof(f18,axiom,(
% 1.53/0.55    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.53/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.53/0.55  fof(f647,plain,(
% 1.53/0.55    ~r1_xboole_0(k1_tarski(sK3),sK1) | r1_xboole_0(sK1,sK0)),
% 1.53/0.55    inference(trivial_inequality_removal,[],[f638])).
% 1.53/0.55  fof(f638,plain,(
% 1.53/0.55    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,sK0) | ~r1_xboole_0(k1_tarski(sK3),sK1)),
% 1.53/0.55    inference(superposition,[],[f84,f554])).
% 1.53/0.55  fof(f554,plain,(
% 1.53/0.55    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~r1_xboole_0(k1_tarski(sK3),sK1)),
% 1.53/0.55    inference(resolution,[],[f372,f92])).
% 1.53/0.55  fof(f92,plain,(
% 1.53/0.55    ( ! [X10,X8,X9] : (r1_xboole_0(X10,k3_xboole_0(X9,X8)) | ~r1_xboole_0(X10,X8)) )),
% 1.53/0.55    inference(superposition,[],[f62,f45])).
% 1.53/0.55  fof(f45,plain,(
% 1.53/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.53/0.55    inference(cnf_transformation,[],[f2])).
% 1.53/0.55  fof(f2,axiom,(
% 1.53/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.53/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.53/0.55  fof(f62,plain,(
% 1.53/0.55    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.55    inference(cnf_transformation,[],[f30])).
% 1.53/0.55  fof(f30,plain,(
% 1.53/0.55    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.53/0.55    inference(ennf_transformation,[],[f10])).
% 1.53/0.55  fof(f10,axiom,(
% 1.53/0.55    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.53/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).
% 1.53/0.55  fof(f372,plain,(
% 1.53/0.55    ~r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.53/0.55    inference(resolution,[],[f210,f54])).
% 1.53/0.55  fof(f210,plain,(
% 1.53/0.55    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.53/0.55    inference(resolution,[],[f73,f37])).
% 1.53/0.55  fof(f37,plain,(
% 1.53/0.55    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.53/0.55    inference(cnf_transformation,[],[f32])).
% 1.53/0.55  fof(f73,plain,(
% 1.53/0.55    ( ! [X4,X3] : (~r1_tarski(X3,X4) | ~r1_xboole_0(X3,X4) | k1_xboole_0 = X3) )),
% 1.53/0.55    inference(superposition,[],[f57,f53])).
% 1.53/0.55  fof(f53,plain,(
% 1.53/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.53/0.55    inference(cnf_transformation,[],[f27])).
% 1.53/0.55  fof(f27,plain,(
% 1.53/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.53/0.55    inference(ennf_transformation,[],[f9])).
% 1.53/0.55  fof(f9,axiom,(
% 1.53/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.53/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.53/0.55  fof(f57,plain,(
% 1.53/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.55    inference(cnf_transformation,[],[f36])).
% 1.53/0.55  fof(f36,plain,(
% 1.53/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.53/0.55    inference(nnf_transformation,[],[f3])).
% 1.53/0.55  fof(f3,axiom,(
% 1.53/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.53/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.53/0.55  fof(f84,plain,(
% 1.53/0.55    ( ! [X6,X5] : (k1_xboole_0 != k3_xboole_0(X6,X5) | r1_xboole_0(X5,X6)) )),
% 1.53/0.55    inference(superposition,[],[f58,f45])).
% 1.53/0.55  fof(f58,plain,(
% 1.53/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.53/0.55    inference(cnf_transformation,[],[f36])).
% 1.53/0.55  fof(f974,plain,(
% 1.53/0.55    ~r1_xboole_0(sK1,sK0)),
% 1.53/0.55    inference(subsumption_resolution,[],[f973,f39])).
% 1.53/0.55  fof(f973,plain,(
% 1.53/0.55    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK2,sK1)),
% 1.53/0.55    inference(trivial_inequality_removal,[],[f968])).
% 1.53/0.55  fof(f968,plain,(
% 1.53/0.55    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK2,sK1)),
% 1.53/0.55    inference(superposition,[],[f963,f74])).
% 1.53/0.55  fof(f74,plain,(
% 1.53/0.55    ( ! [X6,X5] : (k1_xboole_0 = k3_xboole_0(X6,X5) | ~r1_xboole_0(X5,X6)) )),
% 1.53/0.55    inference(superposition,[],[f57,f45])).
% 1.53/0.55  fof(f963,plain,(
% 1.53/0.55    k1_xboole_0 != k3_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0)),
% 1.53/0.55    inference(resolution,[],[f159,f63])).
% 1.53/0.55  fof(f63,plain,(
% 1.53/0.55    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 1.53/0.55    inference(resolution,[],[f54,f40])).
% 1.53/0.55  fof(f40,plain,(
% 1.53/0.55    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.53/0.55    inference(cnf_transformation,[],[f32])).
% 1.53/0.55  fof(f159,plain,(
% 1.53/0.55    ( ! [X19,X17,X18] : (r1_xboole_0(X17,k2_xboole_0(X18,X19)) | k1_xboole_0 != k3_xboole_0(X17,X19) | ~r1_xboole_0(X17,X18)) )),
% 1.53/0.55    inference(superposition,[],[f58,f61])).
% 1.53/0.55  fof(f61,plain,(
% 1.53/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.55    inference(cnf_transformation,[],[f29])).
% 1.53/0.55  fof(f29,plain,(
% 1.53/0.55    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 1.53/0.55    inference(ennf_transformation,[],[f11])).
% 1.53/0.55  fof(f11,axiom,(
% 1.53/0.55    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 1.53/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 1.53/0.55  % SZS output end Proof for theBenchmark
% 1.53/0.55  % (15284)------------------------------
% 1.53/0.55  % (15284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.55  % (15284)Termination reason: Refutation
% 1.53/0.55  
% 1.53/0.55  % (15284)Memory used [KB]: 2686
% 1.53/0.55  % (15284)Time elapsed: 0.142 s
% 1.53/0.55  % (15284)------------------------------
% 1.53/0.55  % (15284)------------------------------
% 1.53/0.55  % (15280)Success in time 0.185 s
%------------------------------------------------------------------------------
