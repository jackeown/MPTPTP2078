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
% DateTime   : Thu Dec  3 12:30:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 129 expanded)
%              Number of leaves         :   10 (  36 expanded)
%              Depth                    :   24
%              Number of atoms          :   95 ( 238 expanded)
%              Number of equality atoms :   41 ( 101 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1623,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1606,f21])).

fof(f21,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f1606,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f219,f1451])).

fof(f1451,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f1446,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1446,plain,(
    r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f1429,f55])).

fof(f55,plain,(
    ! [X4] : k2_xboole_0(X4,X4) = X4 ),
    inference(resolution,[],[f27,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f23,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1429,plain,(
    ! [X8] : r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(X8,sK1)) ),
    inference(trivial_inequality_removal,[],[f1421])).

fof(f1421,plain,(
    ! [X8] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(X8,sK1)) ) ),
    inference(superposition,[],[f159,f1293])).

fof(f1293,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(X1,sK1))) ),
    inference(forward_demodulation,[],[f1281,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1281,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X1,sK1),sK2)) ),
    inference(superposition,[],[f944,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f944,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(X0,sK1)),sK2) ),
    inference(resolution,[],[f932,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f932,plain,(
    ! [X1] : r1_tarski(k4_xboole_0(sK0,k2_xboole_0(X1,sK1)),sK2) ),
    inference(forward_demodulation,[],[f931,f32])).

fof(f931,plain,(
    ! [X1] : r1_tarski(k4_xboole_0(k4_xboole_0(sK0,X1),sK1),sK2) ),
    inference(trivial_inequality_removal,[],[f922])).

fof(f922,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,X1),sK1),sK2) ) ),
    inference(superposition,[],[f159,f710])).

fof(f710,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f640,f31])).

fof(f640,plain,(
    ! [X12] : r1_tarski(k4_xboole_0(sK0,X12),k2_xboole_0(sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f617])).

fof(f617,plain,(
    ! [X12] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k4_xboole_0(sK0,X12),k2_xboole_0(sK1,sK2)) ) ),
    inference(superposition,[],[f159,f183])).

fof(f183,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f172,f25])).

fof(f172,plain,(
    ! [X14] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X14)) ),
    inference(forward_demodulation,[],[f152,f65])).

fof(f65,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5) ),
    inference(resolution,[],[f31,f47])).

fof(f47,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(superposition,[],[f23,f37])).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f25,f22])).

fof(f152,plain,(
    ! [X14] : k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X14)) = k4_xboole_0(k1_xboole_0,X14) ),
    inference(superposition,[],[f32,f61])).

fof(f61,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f31,f19])).

fof(f19,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f159,plain,(
    ! [X6,X7,X5] :
      ( k1_xboole_0 != k4_xboole_0(X5,k2_xboole_0(X6,X7))
      | r1_tarski(k4_xboole_0(X5,X6),X7) ) ),
    inference(superposition,[],[f30,f32])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f219,plain,(
    ! [X3] : r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X3)) ),
    inference(trivial_inequality_removal,[],[f218])).

fof(f218,plain,(
    ! [X3] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X3)) ) ),
    inference(superposition,[],[f30,f173])).

fof(f173,plain,(
    ! [X15] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X15)) ),
    inference(forward_demodulation,[],[f153,f65])).

fof(f153,plain,(
    ! [X15] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X15)) = k4_xboole_0(k1_xboole_0,X15) ),
    inference(superposition,[],[f32,f124])).

fof(f124,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f35,f20])).

fof(f20,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:58:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (10097)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.46  % (10094)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (10100)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (10099)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (10091)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (10102)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (10089)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (10090)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (10092)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (10093)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (10095)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (10104)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (10098)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (10105)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (10088)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (10103)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (10096)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (10100)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (10101)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.32/0.53  % SZS output start Proof for theBenchmark
% 1.32/0.53  fof(f1623,plain,(
% 1.32/0.53    $false),
% 1.32/0.53    inference(subsumption_resolution,[],[f1606,f21])).
% 1.32/0.53  fof(f21,plain,(
% 1.32/0.53    ~r1_tarski(sK0,sK1)),
% 1.32/0.53    inference(cnf_transformation,[],[f16])).
% 1.32/0.53  fof(f16,plain,(
% 1.32/0.53    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 1.32/0.53  fof(f15,plain,(
% 1.32/0.53    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f13,plain,(
% 1.32/0.53    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.32/0.53    inference(flattening,[],[f12])).
% 1.32/0.53  fof(f12,plain,(
% 1.32/0.53    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.32/0.53    inference(ennf_transformation,[],[f11])).
% 1.32/0.53  fof(f11,negated_conjecture,(
% 1.32/0.53    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.32/0.53    inference(negated_conjecture,[],[f10])).
% 1.32/0.53  fof(f10,conjecture,(
% 1.32/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 1.32/0.53  fof(f1606,plain,(
% 1.32/0.53    r1_tarski(sK0,sK1)),
% 1.32/0.53    inference(superposition,[],[f219,f1451])).
% 1.32/0.53  fof(f1451,plain,(
% 1.32/0.53    sK1 = k2_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 1.32/0.53    inference(resolution,[],[f1446,f27])).
% 1.32/0.53  fof(f27,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.32/0.53    inference(cnf_transformation,[],[f14])).
% 1.32/0.53  fof(f14,plain,(
% 1.32/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.32/0.53    inference(ennf_transformation,[],[f5])).
% 1.32/0.53  fof(f5,axiom,(
% 1.32/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.32/0.53  fof(f1446,plain,(
% 1.32/0.53    r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 1.32/0.53    inference(superposition,[],[f1429,f55])).
% 1.32/0.53  fof(f55,plain,(
% 1.32/0.53    ( ! [X4] : (k2_xboole_0(X4,X4) = X4) )),
% 1.32/0.53    inference(resolution,[],[f27,f36])).
% 1.32/0.53  fof(f36,plain,(
% 1.32/0.53    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.32/0.53    inference(superposition,[],[f23,f22])).
% 1.32/0.53  fof(f22,plain,(
% 1.32/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f6])).
% 1.32/0.53  fof(f6,axiom,(
% 1.32/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.32/0.53  fof(f23,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f9])).
% 1.32/0.53  fof(f9,axiom,(
% 1.32/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.32/0.53  fof(f1429,plain,(
% 1.32/0.53    ( ! [X8] : (r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(X8,sK1))) )),
% 1.32/0.53    inference(trivial_inequality_removal,[],[f1421])).
% 1.32/0.53  fof(f1421,plain,(
% 1.32/0.53    ( ! [X8] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(X8,sK1))) )),
% 1.32/0.53    inference(superposition,[],[f159,f1293])).
% 1.32/0.53  fof(f1293,plain,(
% 1.32/0.53    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(X1,sK1)))) )),
% 1.32/0.53    inference(forward_demodulation,[],[f1281,f25])).
% 1.32/0.53  fof(f25,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f1])).
% 1.32/0.53  fof(f1,axiom,(
% 1.32/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.32/0.53  fof(f1281,plain,(
% 1.32/0.53    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X1,sK1),sK2))) )),
% 1.32/0.53    inference(superposition,[],[f944,f32])).
% 1.32/0.53  fof(f32,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f7])).
% 1.32/0.53  fof(f7,axiom,(
% 1.32/0.53    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.32/0.53  fof(f944,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(X0,sK1)),sK2)) )),
% 1.32/0.53    inference(resolution,[],[f932,f31])).
% 1.32/0.53  fof(f31,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f18])).
% 1.32/0.53  fof(f18,plain,(
% 1.32/0.53    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.32/0.53    inference(nnf_transformation,[],[f4])).
% 1.32/0.53  fof(f4,axiom,(
% 1.32/0.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.32/0.53  fof(f932,plain,(
% 1.32/0.53    ( ! [X1] : (r1_tarski(k4_xboole_0(sK0,k2_xboole_0(X1,sK1)),sK2)) )),
% 1.32/0.53    inference(forward_demodulation,[],[f931,f32])).
% 1.32/0.53  fof(f931,plain,(
% 1.32/0.53    ( ! [X1] : (r1_tarski(k4_xboole_0(k4_xboole_0(sK0,X1),sK1),sK2)) )),
% 1.32/0.53    inference(trivial_inequality_removal,[],[f922])).
% 1.32/0.53  fof(f922,plain,(
% 1.32/0.53    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,X1),sK1),sK2)) )),
% 1.32/0.53    inference(superposition,[],[f159,f710])).
% 1.32/0.53  fof(f710,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),k2_xboole_0(sK1,sK2))) )),
% 1.32/0.53    inference(resolution,[],[f640,f31])).
% 1.32/0.53  fof(f640,plain,(
% 1.32/0.53    ( ! [X12] : (r1_tarski(k4_xboole_0(sK0,X12),k2_xboole_0(sK1,sK2))) )),
% 1.32/0.53    inference(trivial_inequality_removal,[],[f617])).
% 1.32/0.53  fof(f617,plain,(
% 1.32/0.53    ( ! [X12] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(sK0,X12),k2_xboole_0(sK1,sK2))) )),
% 1.32/0.53    inference(superposition,[],[f159,f183])).
% 1.32/0.53  fof(f183,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2)))) )),
% 1.32/0.53    inference(superposition,[],[f172,f25])).
% 1.32/0.53  fof(f172,plain,(
% 1.32/0.53    ( ! [X14] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X14))) )),
% 1.32/0.53    inference(forward_demodulation,[],[f152,f65])).
% 1.32/0.53  fof(f65,plain,(
% 1.32/0.53    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)) )),
% 1.32/0.53    inference(resolution,[],[f31,f47])).
% 1.32/0.53  fof(f47,plain,(
% 1.32/0.53    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 1.32/0.53    inference(superposition,[],[f23,f37])).
% 1.32/0.53  fof(f37,plain,(
% 1.32/0.53    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.32/0.53    inference(superposition,[],[f25,f22])).
% 1.32/0.53  fof(f152,plain,(
% 1.32/0.53    ( ! [X14] : (k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X14)) = k4_xboole_0(k1_xboole_0,X14)) )),
% 1.32/0.53    inference(superposition,[],[f32,f61])).
% 1.32/0.53  fof(f61,plain,(
% 1.32/0.53    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.32/0.53    inference(resolution,[],[f31,f19])).
% 1.32/0.53  fof(f19,plain,(
% 1.32/0.53    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 1.32/0.53    inference(cnf_transformation,[],[f16])).
% 1.32/0.53  fof(f159,plain,(
% 1.32/0.53    ( ! [X6,X7,X5] : (k1_xboole_0 != k4_xboole_0(X5,k2_xboole_0(X6,X7)) | r1_tarski(k4_xboole_0(X5,X6),X7)) )),
% 1.32/0.53    inference(superposition,[],[f30,f32])).
% 1.32/0.53  fof(f30,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f18])).
% 1.32/0.53  fof(f219,plain,(
% 1.32/0.53    ( ! [X3] : (r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X3))) )),
% 1.32/0.53    inference(trivial_inequality_removal,[],[f218])).
% 1.32/0.53  fof(f218,plain,(
% 1.32/0.53    ( ! [X3] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X3))) )),
% 1.32/0.53    inference(superposition,[],[f30,f173])).
% 1.32/0.53  fof(f173,plain,(
% 1.32/0.53    ( ! [X15] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X15))) )),
% 1.32/0.53    inference(forward_demodulation,[],[f153,f65])).
% 1.32/0.53  fof(f153,plain,(
% 1.32/0.53    ( ! [X15] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X15)) = k4_xboole_0(k1_xboole_0,X15)) )),
% 1.32/0.53    inference(superposition,[],[f32,f124])).
% 1.32/0.53  fof(f124,plain,(
% 1.32/0.53    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.32/0.53    inference(resolution,[],[f35,f20])).
% 1.32/0.53  fof(f20,plain,(
% 1.32/0.53    r1_xboole_0(sK0,sK2)),
% 1.32/0.53    inference(cnf_transformation,[],[f16])).
% 1.32/0.53  fof(f35,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.32/0.53    inference(definition_unfolding,[],[f28,f26])).
% 1.32/0.53  fof(f26,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f8])).
% 1.32/0.53  fof(f8,axiom,(
% 1.32/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.32/0.53  fof(f28,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f17])).
% 1.32/0.53  fof(f17,plain,(
% 1.32/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.32/0.53    inference(nnf_transformation,[],[f3])).
% 1.32/0.53  fof(f3,axiom,(
% 1.32/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.32/0.53  % SZS output end Proof for theBenchmark
% 1.32/0.53  % (10100)------------------------------
% 1.32/0.53  % (10100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (10100)Termination reason: Refutation
% 1.32/0.53  
% 1.32/0.53  % (10100)Memory used [KB]: 2302
% 1.32/0.53  % (10100)Time elapsed: 0.090 s
% 1.32/0.53  % (10100)------------------------------
% 1.32/0.53  % (10100)------------------------------
% 1.32/0.53  % (10087)Success in time 0.171 s
%------------------------------------------------------------------------------
