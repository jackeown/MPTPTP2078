%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 188 expanded)
%              Number of leaves         :   11 (  58 expanded)
%              Depth                    :   20
%              Number of atoms          :   89 ( 294 expanded)
%              Number of equality atoms :   55 ( 152 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1209,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1208])).

fof(f1208,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f1190,f48])).

fof(f48,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f43,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f43,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f32,f22])).

fof(f22,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1190,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f39,f1133])).

fof(f1133,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f783,f51])).

fof(f51,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f47,f21])).

fof(f47,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f32,f40])).

fof(f40,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f35,f31])).

fof(f31,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f20,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f783,plain,(
    ! [X12,X11] : k4_xboole_0(sK0,X12) = k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(X11,sK2))) ),
    inference(forward_demodulation,[],[f782,f71])).

fof(f71,plain,(
    ! [X4] : k2_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f64,f21])).

fof(f64,plain,(
    ! [X4] : k2_xboole_0(k4_xboole_0(X4,k1_xboole_0),k1_xboole_0) = X4 ),
    inference(superposition,[],[f33,f22])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

% (8298)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f782,plain,(
    ! [X12,X11] : k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(X11,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X12),k1_xboole_0) ),
    inference(forward_demodulation,[],[f768,f48])).

fof(f768,plain,(
    ! [X12,X11] : k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(X11,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X12),k4_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f37,f725])).

fof(f725,plain,(
    ! [X1] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X1,sK2)) ),
    inference(forward_demodulation,[],[f724,f21])).

fof(f724,plain,(
    ! [X1] : k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(X1,sK2)) ),
    inference(forward_demodulation,[],[f723,f68])).

fof(f68,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[],[f22,f33])).

fof(f723,plain,(
    ! [X1] : k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X1)),sK2)) = k4_xboole_0(sK0,k4_xboole_0(X1,sK2)) ),
    inference(forward_demodulation,[],[f702,f623])).

fof(f623,plain,(
    ! [X39] : k4_xboole_0(sK0,k4_xboole_0(X39,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X39),sK0) ),
    inference(forward_demodulation,[],[f557,f21])).

fof(f557,plain,(
    ! [X39] : k4_xboole_0(sK0,k4_xboole_0(X39,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X39),k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f37,f38])).

fof(f38,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f28,f19])).

fof(f19,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f702,plain,(
    ! [X1] : k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X1)),sK2)) = k2_xboole_0(k4_xboole_0(sK0,X1),sK0) ),
    inference(superposition,[],[f623,f257])).

fof(f257,plain,(
    ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) ),
    inference(forward_demodulation,[],[f240,f217])).

fof(f217,plain,(
    ! [X23] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X23))) = k4_xboole_0(sK0,X23) ),
    inference(forward_demodulation,[],[f172,f21])).

fof(f172,plain,(
    ! [X23] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X23))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X23) ),
    inference(superposition,[],[f36,f38])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f29,f23,f23])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f240,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))) ),
    inference(superposition,[],[f217,f32])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f30,f23])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f39,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f34,f18])).

fof(f18,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f27,f23])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:12:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (8295)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (8296)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (8291)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (8289)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (8286)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (8303)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (8290)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (8294)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (8299)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (8288)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (8293)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (8287)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.50  % (8300)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.51  % (8292)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (8302)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (8288)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f1209,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f1208])).
% 0.20/0.51  fof(f1208,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0),
% 0.20/0.51    inference(superposition,[],[f1190,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f43,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 0.20/0.51    inference(superposition,[],[f32,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f24,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.51  fof(f1190,plain,(
% 0.20/0.51    k1_xboole_0 != k4_xboole_0(sK0,sK0)),
% 0.20/0.51    inference(backward_demodulation,[],[f39,f1133])).
% 0.20/0.51  fof(f1133,plain,(
% 0.20/0.51    sK0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.51    inference(superposition,[],[f783,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.51    inference(forward_demodulation,[],[f47,f21])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.20/0.51    inference(superposition,[],[f32,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 0.20/0.51    inference(resolution,[],[f35,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.51    inference(definition_unfolding,[],[f20,f23])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.51    inference(negated_conjecture,[],[f10])).
% 0.20/0.51  fof(f10,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f26,f23])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.51  fof(f783,plain,(
% 0.20/0.51    ( ! [X12,X11] : (k4_xboole_0(sK0,X12) = k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(X11,sK2)))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f782,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X4] : (k2_xboole_0(X4,k1_xboole_0) = X4) )),
% 0.20/0.51    inference(forward_demodulation,[],[f64,f21])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X4] : (k2_xboole_0(k4_xboole_0(X4,k1_xboole_0),k1_xboole_0) = X4) )),
% 0.20/0.51    inference(superposition,[],[f33,f22])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f25,f23])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  % (8298)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.20/0.51  fof(f782,plain,(
% 0.20/0.51    ( ! [X12,X11] : (k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(X11,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X12),k1_xboole_0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f768,f48])).
% 0.20/0.51  fof(f768,plain,(
% 0.20/0.51    ( ! [X12,X11] : (k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(X11,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X12),k4_xboole_0(sK0,sK0))) )),
% 0.20/0.51    inference(superposition,[],[f37,f725])).
% 0.20/0.51  fof(f725,plain,(
% 0.20/0.51    ( ! [X1] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X1,sK2))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f724,f21])).
% 0.20/0.51  fof(f724,plain,(
% 0.20/0.51    ( ! [X1] : (k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(X1,sK2))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f723,f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 0.20/0.51    inference(superposition,[],[f22,f33])).
% 0.20/0.51  fof(f723,plain,(
% 0.20/0.51    ( ! [X1] : (k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X1)),sK2)) = k4_xboole_0(sK0,k4_xboole_0(X1,sK2))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f702,f623])).
% 0.20/0.51  fof(f623,plain,(
% 0.20/0.51    ( ! [X39] : (k4_xboole_0(sK0,k4_xboole_0(X39,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X39),sK0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f557,f21])).
% 0.20/0.51  fof(f557,plain,(
% 0.20/0.51    ( ! [X39] : (k4_xboole_0(sK0,k4_xboole_0(X39,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X39),k4_xboole_0(sK0,k1_xboole_0))) )),
% 0.20/0.51    inference(superposition,[],[f37,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.20/0.51    inference(resolution,[],[f28,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    r1_tarski(sK0,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 0.20/0.51    inference(unused_predicate_definition_removal,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.51  fof(f702,plain,(
% 0.20/0.51    ( ! [X1] : (k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X1)),sK2)) = k2_xboole_0(k4_xboole_0(sK0,X1),sK0)) )),
% 0.20/0.51    inference(superposition,[],[f623,f257])).
% 0.20/0.51  fof(f257,plain,(
% 0.20/0.51    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f240,f217])).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    ( ! [X23] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X23))) = k4_xboole_0(sK0,X23)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f172,f21])).
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    ( ! [X23] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X23))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X23)) )),
% 0.20/0.51    inference(superposition,[],[f36,f38])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f29,f23,f23])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.51  fof(f240,plain,(
% 0.20/0.51    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) )),
% 0.20/0.51    inference(superposition,[],[f217,f32])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f30,f23])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.51    inference(resolution,[],[f34,f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ~r1_xboole_0(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f27,f23])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (8288)------------------------------
% 0.20/0.51  % (8288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8288)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (8288)Memory used [KB]: 6524
% 0.20/0.51  % (8288)Time elapsed: 0.075 s
% 0.20/0.51  % (8288)------------------------------
% 0.20/0.51  % (8288)------------------------------
% 0.20/0.51  % (8282)Success in time 0.152 s
%------------------------------------------------------------------------------
