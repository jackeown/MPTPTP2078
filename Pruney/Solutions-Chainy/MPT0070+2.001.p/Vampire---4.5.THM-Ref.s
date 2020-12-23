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
% DateTime   : Thu Dec  3 12:30:26 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 323 expanded)
%              Number of leaves         :   11 ( 103 expanded)
%              Depth                    :   24
%              Number of atoms          :  111 ( 450 expanded)
%              Number of equality atoms :   60 ( 272 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4699,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f4698])).

fof(f4698,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f4697,f39])).

fof(f39,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(resolution,[],[f31,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f24,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f4697,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f44,f4675])).

fof(f4675,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f2746,f4610])).

fof(f4610,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f4584,f22])).

fof(f4584,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f133,f4291])).

fof(f4291,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f4262,f31])).

fof(f4262,plain,(
    r1_tarski(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f4224,f2797])).

fof(f2797,plain,(
    sK2 = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f2665,f22])).

fof(f2665,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f133,f593])).

fof(f593,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f569,f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f569,plain,(
    ! [X16] : k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK1),X16)) ),
    inference(forward_demodulation,[],[f506,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f45,f31])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f24,f39])).

fof(f506,plain,(
    ! [X16] : k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK1),X16)) = k4_xboole_0(k1_xboole_0,X16) ),
    inference(superposition,[],[f120,f57])).

fof(f57,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f35,f20])).

fof(f20,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f120,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f27,f27])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f4224,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0)) ),
    inference(forward_demodulation,[],[f4223,f246])).

fof(f246,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(forward_demodulation,[],[f245,f22])).

fof(f245,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f244,f39])).

fof(f244,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,k4_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f243,f61])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f32,f22])).

fof(f243,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1))) ),
    inference(forward_demodulation,[],[f235,f22])).

fof(f235,plain,(
    ! [X1] : k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k1_xboole_0) ),
    inference(superposition,[],[f33,f192])).

fof(f192,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X3),X3) ),
    inference(superposition,[],[f61,f39])).

fof(f4223,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,sK1)),k4_xboole_0(X0,sK0)) ),
    inference(forward_demodulation,[],[f4176,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f4176,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(sK1,k1_xboole_0)),k4_xboole_0(X0,sK0)) ),
    inference(superposition,[],[f170,f1840])).

fof(f1840,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(sK1,k4_xboole_0(X2,sK0))) ),
    inference(forward_demodulation,[],[f1819,f25])).

fof(f1819,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,sK0),sK1)) ),
    inference(superposition,[],[f1615,f120])).

fof(f1615,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),sK1) ),
    inference(resolution,[],[f1599,f31])).

fof(f1599,plain,(
    ! [X62] : r1_tarski(k4_xboole_0(sK0,X62),sK1) ),
    inference(forward_demodulation,[],[f1558,f246])).

fof(f1558,plain,(
    ! [X62] : r1_tarski(k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X62)),sK1) ),
    inference(superposition,[],[f577,f37])).

fof(f37,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f31,f19])).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f577,plain,(
    ! [X6,X7,X5] : r1_tarski(k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X5),X7)),X5) ),
    inference(forward_demodulation,[],[f519,f32])).

fof(f519,plain,(
    ! [X6,X7,X5] : r1_tarski(k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X7),X5) ),
    inference(superposition,[],[f24,f120])).

fof(f170,plain,(
    ! [X12,X13,X11] : r1_tarski(k4_xboole_0(X11,k2_xboole_0(X12,k4_xboole_0(X11,k2_xboole_0(X12,X13)))),X13) ),
    inference(forward_demodulation,[],[f155,f32])).

fof(f155,plain,(
    ! [X12,X13,X11] : r1_tarski(k4_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,k2_xboole_0(X12,X13))),X13) ),
    inference(superposition,[],[f122,f32])).

fof(f122,plain,(
    ! [X6,X5] : r1_tarski(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X5) ),
    inference(superposition,[],[f24,f33])).

fof(f133,plain,(
    ! [X10,X9] : k4_xboole_0(X9,X10) = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f110,f22])).

fof(f110,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) ),
    inference(superposition,[],[f33,f38])).

fof(f38,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f31,f24])).

fof(f2746,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X11,X10)) = X10 ),
    inference(forward_demodulation,[],[f2660,f22])).

fof(f2660,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k1_xboole_0) = k4_xboole_0(X10,k4_xboole_0(X11,X10)) ),
    inference(superposition,[],[f133,f760])).

fof(f760,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f668,f39])).

fof(f668,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f111,f23])).

fof(f111,plain,(
    ! [X12,X13,X11] : k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X11,X12))) = k4_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,k2_xboole_0(X12,X13))) ),
    inference(superposition,[],[f33,f32])).

fof(f44,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f34,f21])).

fof(f21,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (25351)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (25355)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (25344)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (25341)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (25349)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (25347)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (25348)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (25342)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (25354)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (25345)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (25346)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (25343)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (25352)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (25357)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (25356)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (25358)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (25350)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.51  % (25353)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.87/0.61  % (25342)Refutation found. Thanks to Tanya!
% 1.87/0.61  % SZS status Theorem for theBenchmark
% 1.87/0.61  % SZS output start Proof for theBenchmark
% 1.87/0.61  fof(f4699,plain,(
% 1.87/0.61    $false),
% 1.87/0.61    inference(trivial_inequality_removal,[],[f4698])).
% 1.87/0.61  fof(f4698,plain,(
% 1.87/0.61    k1_xboole_0 != k1_xboole_0),
% 1.87/0.61    inference(superposition,[],[f4697,f39])).
% 1.87/0.61  fof(f39,plain,(
% 1.87/0.61    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 1.87/0.61    inference(resolution,[],[f31,f36])).
% 1.87/0.61  fof(f36,plain,(
% 1.87/0.61    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.87/0.61    inference(superposition,[],[f24,f22])).
% 1.87/0.61  fof(f22,plain,(
% 1.87/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.87/0.61    inference(cnf_transformation,[],[f7])).
% 1.87/0.61  fof(f7,axiom,(
% 1.87/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.87/0.61  fof(f24,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f6])).
% 1.87/0.61  fof(f6,axiom,(
% 1.87/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.87/0.61  fof(f31,plain,(
% 1.87/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f18])).
% 1.87/0.61  fof(f18,plain,(
% 1.87/0.61    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.87/0.61    inference(nnf_transformation,[],[f5])).
% 1.87/0.61  fof(f5,axiom,(
% 1.87/0.61    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.87/0.61  fof(f4697,plain,(
% 1.87/0.61    k1_xboole_0 != k4_xboole_0(sK0,sK0)),
% 1.87/0.61    inference(backward_demodulation,[],[f44,f4675])).
% 1.87/0.61  fof(f4675,plain,(
% 1.87/0.61    sK0 = k4_xboole_0(sK0,sK2)),
% 1.87/0.61    inference(superposition,[],[f2746,f4610])).
% 1.87/0.61  fof(f4610,plain,(
% 1.87/0.61    sK2 = k4_xboole_0(sK2,sK0)),
% 1.87/0.61    inference(forward_demodulation,[],[f4584,f22])).
% 1.87/0.61  fof(f4584,plain,(
% 1.87/0.61    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.87/0.61    inference(superposition,[],[f133,f4291])).
% 1.87/0.61  fof(f4291,plain,(
% 1.87/0.61    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.87/0.61    inference(resolution,[],[f4262,f31])).
% 1.87/0.61  fof(f4262,plain,(
% 1.87/0.61    r1_tarski(sK2,k4_xboole_0(sK2,sK0))),
% 1.87/0.61    inference(superposition,[],[f4224,f2797])).
% 1.87/0.61  fof(f2797,plain,(
% 1.87/0.61    sK2 = k4_xboole_0(sK2,sK1)),
% 1.87/0.61    inference(forward_demodulation,[],[f2665,f22])).
% 1.87/0.61  fof(f2665,plain,(
% 1.87/0.61    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.87/0.61    inference(superposition,[],[f133,f593])).
% 1.87/0.61  fof(f593,plain,(
% 1.87/0.61    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 1.87/0.61    inference(superposition,[],[f569,f23])).
% 1.87/0.61  fof(f23,plain,(
% 1.87/0.61    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.87/0.61    inference(cnf_transformation,[],[f12])).
% 1.87/0.61  fof(f12,plain,(
% 1.87/0.61    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.87/0.61    inference(rectify,[],[f4])).
% 1.87/0.61  fof(f4,axiom,(
% 1.87/0.61    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.87/0.61  fof(f569,plain,(
% 1.87/0.61    ( ! [X16] : (k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK1),X16))) )),
% 1.87/0.61    inference(forward_demodulation,[],[f506,f46])).
% 1.87/0.61  fof(f46,plain,(
% 1.87/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.87/0.61    inference(resolution,[],[f45,f31])).
% 1.87/0.61  fof(f45,plain,(
% 1.87/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.87/0.61    inference(superposition,[],[f24,f39])).
% 1.87/0.61  fof(f506,plain,(
% 1.87/0.61    ( ! [X16] : (k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK1),X16)) = k4_xboole_0(k1_xboole_0,X16)) )),
% 1.87/0.61    inference(superposition,[],[f120,f57])).
% 1.87/0.61  fof(f57,plain,(
% 1.87/0.61    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.87/0.61    inference(resolution,[],[f35,f20])).
% 1.87/0.61  fof(f20,plain,(
% 1.87/0.61    r1_xboole_0(sK1,sK2)),
% 1.87/0.61    inference(cnf_transformation,[],[f16])).
% 1.87/0.61  fof(f16,plain,(
% 1.87/0.61    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 1.87/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 1.87/0.61  fof(f15,plain,(
% 1.87/0.61    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 1.87/0.61    introduced(choice_axiom,[])).
% 1.87/0.61  fof(f14,plain,(
% 1.87/0.61    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 1.87/0.61    inference(flattening,[],[f13])).
% 1.87/0.61  fof(f13,plain,(
% 1.87/0.61    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 1.87/0.61    inference(ennf_transformation,[],[f11])).
% 1.87/0.61  fof(f11,negated_conjecture,(
% 1.87/0.61    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.87/0.61    inference(negated_conjecture,[],[f10])).
% 1.87/0.61  fof(f10,conjecture,(
% 1.87/0.61    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.87/0.61  fof(f35,plain,(
% 1.87/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.87/0.61    inference(definition_unfolding,[],[f28,f27])).
% 1.87/0.61  fof(f27,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f9])).
% 1.87/0.61  fof(f9,axiom,(
% 1.87/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.87/0.61  fof(f28,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f17])).
% 1.87/0.61  fof(f17,plain,(
% 1.87/0.61    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.87/0.61    inference(nnf_transformation,[],[f3])).
% 1.87/0.61  fof(f3,axiom,(
% 1.87/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.87/0.61  fof(f120,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) )),
% 1.87/0.61    inference(superposition,[],[f32,f33])).
% 1.87/0.61  fof(f33,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.87/0.61    inference(definition_unfolding,[],[f26,f27,f27])).
% 1.87/0.61  fof(f26,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f2])).
% 1.87/0.61  fof(f2,axiom,(
% 1.87/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.87/0.61  fof(f32,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f8])).
% 1.87/0.61  fof(f8,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.87/0.61  fof(f4224,plain,(
% 1.87/0.61    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0))) )),
% 1.87/0.61    inference(forward_demodulation,[],[f4223,f246])).
% 1.87/0.61  fof(f246,plain,(
% 1.87/0.61    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.87/0.61    inference(forward_demodulation,[],[f245,f22])).
% 1.87/0.61  fof(f245,plain,(
% 1.87/0.61    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,k1_xboole_0)) )),
% 1.87/0.61    inference(forward_demodulation,[],[f244,f39])).
% 1.87/0.61  fof(f244,plain,(
% 1.87/0.61    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,k4_xboole_0(X1,X1))) )),
% 1.87/0.61    inference(forward_demodulation,[],[f243,f61])).
% 1.87/0.61  fof(f61,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) )),
% 1.87/0.61    inference(superposition,[],[f32,f22])).
% 1.87/0.61  fof(f243,plain,(
% 1.87/0.61    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1)))) )),
% 1.87/0.61    inference(forward_demodulation,[],[f235,f22])).
% 1.87/0.61  fof(f235,plain,(
% 1.87/0.61    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k1_xboole_0)) )),
% 1.87/0.61    inference(superposition,[],[f33,f192])).
% 1.87/0.61  fof(f192,plain,(
% 1.87/0.61    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X3),X3)) )),
% 1.87/0.61    inference(superposition,[],[f61,f39])).
% 1.87/0.61  fof(f4223,plain,(
% 1.87/0.61    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,sK1)),k4_xboole_0(X0,sK0))) )),
% 1.87/0.61    inference(forward_demodulation,[],[f4176,f25])).
% 1.87/0.61  fof(f25,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f1])).
% 1.87/0.61  fof(f1,axiom,(
% 1.87/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.87/0.61  fof(f4176,plain,(
% 1.87/0.61    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(sK1,k1_xboole_0)),k4_xboole_0(X0,sK0))) )),
% 1.87/0.61    inference(superposition,[],[f170,f1840])).
% 1.87/0.61  fof(f1840,plain,(
% 1.87/0.61    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(sK1,k4_xboole_0(X2,sK0)))) )),
% 1.87/0.61    inference(forward_demodulation,[],[f1819,f25])).
% 1.87/0.61  fof(f1819,plain,(
% 1.87/0.61    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,sK0),sK1))) )),
% 1.87/0.61    inference(superposition,[],[f1615,f120])).
% 1.87/0.61  fof(f1615,plain,(
% 1.87/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),sK1)) )),
% 1.87/0.61    inference(resolution,[],[f1599,f31])).
% 1.87/0.61  fof(f1599,plain,(
% 1.87/0.61    ( ! [X62] : (r1_tarski(k4_xboole_0(sK0,X62),sK1)) )),
% 1.87/0.61    inference(forward_demodulation,[],[f1558,f246])).
% 1.87/0.61  fof(f1558,plain,(
% 1.87/0.61    ( ! [X62] : (r1_tarski(k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X62)),sK1)) )),
% 1.87/0.61    inference(superposition,[],[f577,f37])).
% 1.87/0.61  fof(f37,plain,(
% 1.87/0.61    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.87/0.61    inference(resolution,[],[f31,f19])).
% 1.87/0.61  fof(f19,plain,(
% 1.87/0.61    r1_tarski(sK0,sK1)),
% 1.87/0.61    inference(cnf_transformation,[],[f16])).
% 1.87/0.61  fof(f577,plain,(
% 1.87/0.61    ( ! [X6,X7,X5] : (r1_tarski(k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X5),X7)),X5)) )),
% 1.87/0.61    inference(forward_demodulation,[],[f519,f32])).
% 1.87/0.61  fof(f519,plain,(
% 1.87/0.61    ( ! [X6,X7,X5] : (r1_tarski(k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X7),X5)) )),
% 1.87/0.61    inference(superposition,[],[f24,f120])).
% 1.87/0.61  fof(f170,plain,(
% 1.87/0.61    ( ! [X12,X13,X11] : (r1_tarski(k4_xboole_0(X11,k2_xboole_0(X12,k4_xboole_0(X11,k2_xboole_0(X12,X13)))),X13)) )),
% 1.87/0.61    inference(forward_demodulation,[],[f155,f32])).
% 1.87/0.61  fof(f155,plain,(
% 1.87/0.61    ( ! [X12,X13,X11] : (r1_tarski(k4_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,k2_xboole_0(X12,X13))),X13)) )),
% 1.87/0.61    inference(superposition,[],[f122,f32])).
% 1.87/0.61  fof(f122,plain,(
% 1.87/0.61    ( ! [X6,X5] : (r1_tarski(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X5)) )),
% 1.87/0.61    inference(superposition,[],[f24,f33])).
% 1.87/0.61  fof(f133,plain,(
% 1.87/0.61    ( ! [X10,X9] : (k4_xboole_0(X9,X10) = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 1.87/0.61    inference(forward_demodulation,[],[f110,f22])).
% 1.87/0.61  fof(f110,plain,(
% 1.87/0.61    ( ! [X10,X9] : (k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0)) )),
% 1.87/0.61    inference(superposition,[],[f33,f38])).
% 1.87/0.61  fof(f38,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.87/0.61    inference(resolution,[],[f31,f24])).
% 1.87/0.61  fof(f2746,plain,(
% 1.87/0.61    ( ! [X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X11,X10)) = X10) )),
% 1.87/0.61    inference(forward_demodulation,[],[f2660,f22])).
% 1.87/0.61  fof(f2660,plain,(
% 1.87/0.61    ( ! [X10,X11] : (k4_xboole_0(X10,k1_xboole_0) = k4_xboole_0(X10,k4_xboole_0(X11,X10))) )),
% 1.87/0.61    inference(superposition,[],[f133,f760])).
% 1.87/0.61  fof(f760,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 1.87/0.61    inference(forward_demodulation,[],[f668,f39])).
% 1.87/0.61  fof(f668,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) )),
% 1.87/0.61    inference(superposition,[],[f111,f23])).
% 1.87/0.61  fof(f111,plain,(
% 1.87/0.61    ( ! [X12,X13,X11] : (k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X11,X12))) = k4_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,k2_xboole_0(X12,X13)))) )),
% 1.87/0.61    inference(superposition,[],[f33,f32])).
% 1.87/0.61  fof(f44,plain,(
% 1.87/0.61    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.87/0.61    inference(resolution,[],[f34,f21])).
% 1.87/0.61  fof(f21,plain,(
% 1.87/0.61    ~r1_xboole_0(sK0,sK2)),
% 1.87/0.61    inference(cnf_transformation,[],[f16])).
% 1.87/0.61  fof(f34,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.87/0.61    inference(definition_unfolding,[],[f29,f27])).
% 1.87/0.61  fof(f29,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.87/0.61    inference(cnf_transformation,[],[f17])).
% 1.87/0.61  % SZS output end Proof for theBenchmark
% 1.87/0.61  % (25342)------------------------------
% 1.87/0.61  % (25342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (25342)Termination reason: Refutation
% 1.87/0.61  
% 1.87/0.61  % (25342)Memory used [KB]: 4605
% 1.87/0.61  % (25342)Time elapsed: 0.186 s
% 1.87/0.61  % (25342)------------------------------
% 1.87/0.61  % (25342)------------------------------
% 1.87/0.61  % (25340)Success in time 0.26 s
%------------------------------------------------------------------------------
