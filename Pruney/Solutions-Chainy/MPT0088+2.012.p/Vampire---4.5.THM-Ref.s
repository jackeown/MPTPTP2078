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
% DateTime   : Thu Dec  3 12:31:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 510 expanded)
%              Number of leaves         :   11 ( 172 expanded)
%              Depth                    :   21
%              Number of atoms          :   89 ( 537 expanded)
%              Number of equality atoms :   62 ( 495 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3633,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3598,f17])).

fof(f17,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f3598,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f593,f2838])).

fof(f2838,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f2786,f441])).

fof(f441,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(X4,X3) ),
    inference(superposition,[],[f275,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f275,plain,(
    ! [X4,X5] : k2_xboole_0(X5,X4) = k4_xboole_0(k2_xboole_0(X4,X5),k1_xboole_0) ),
    inference(forward_demodulation,[],[f255,f92])).

fof(f92,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f83,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f83,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f27,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f28,f19])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f255,plain,(
    ! [X4,X5] : k2_xboole_0(X5,X4) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X4,k2_xboole_0(X5,X4))) ),
    inference(superposition,[],[f204,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(forward_demodulation,[],[f39,f23])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f23,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f204,plain,(
    ! [X17,X16] : k4_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X16,X17)) = X17 ),
    inference(forward_demodulation,[],[f203,f19])).

fof(f203,plain,(
    ! [X17,X16] : k4_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X16,X17)) = k4_xboole_0(X17,k1_xboole_0) ),
    inference(forward_demodulation,[],[f176,f92])).

fof(f176,plain,(
    ! [X17,X16] : k4_xboole_0(X17,k4_xboole_0(X17,k2_xboole_0(X16,X17))) = k4_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X16,X17)) ),
    inference(superposition,[],[f29,f24])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f21,f21])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2786,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f998,f452])).

fof(f452,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X2),X2) ),
    inference(forward_demodulation,[],[f435,f19])).

fof(f435,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),X2) = k4_xboole_0(k2_xboole_0(X2,X3),k1_xboole_0) ),
    inference(superposition,[],[f275,f23])).

fof(f998,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[],[f27,f982])).

fof(f982,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f947,f19])).

fof(f947,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f30,f59])).

fof(f59,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f32,f16])).

fof(f16,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f25,f21])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f593,plain,(
    ! [X4,X2,X3] : r1_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2))) ),
    inference(superposition,[],[f517,f441])).

fof(f517,plain,(
    ! [X21,X19,X20] : r1_xboole_0(X21,k4_xboole_0(X19,k2_xboole_0(X20,X21))) ),
    inference(superposition,[],[f504,f27])).

fof(f504,plain,(
    ! [X14,X13] : r1_xboole_0(X13,k4_xboole_0(X14,X13)) ),
    inference(subsumption_resolution,[],[f500,f33])).

fof(f500,plain,(
    ! [X14,X13] :
      ( k1_xboole_0 != k4_xboole_0(X13,X13)
      | r1_xboole_0(X13,k4_xboole_0(X14,X13)) ) ),
    inference(superposition,[],[f31,f471])).

fof(f471,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(backward_demodulation,[],[f35,f470])).

fof(f470,plain,(
    ! [X28,X27] : k4_xboole_0(k2_xboole_0(X27,X28),k4_xboole_0(X28,X27)) = X27 ),
    inference(backward_demodulation,[],[f431,f469])).

fof(f469,plain,(
    ! [X17,X16] : k4_xboole_0(X16,X17) = k4_xboole_0(k2_xboole_0(X17,X16),X17) ),
    inference(forward_demodulation,[],[f468,f456])).

fof(f456,plain,(
    ! [X10,X9] : k2_xboole_0(X10,X9) = k2_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X9,X10)) ),
    inference(backward_demodulation,[],[f272,f452])).

fof(f272,plain,(
    ! [X10,X9] : k2_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X9,X10)) = k2_xboole_0(k4_xboole_0(X9,X10),X10) ),
    inference(superposition,[],[f23,f204])).

fof(f468,plain,(
    ! [X17,X16] : k4_xboole_0(X16,X17) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X16,X17),k2_xboole_0(X16,X17)),X17) ),
    inference(backward_demodulation,[],[f266,f441])).

fof(f266,plain,(
    ! [X17,X16] : k4_xboole_0(X16,X17) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X16,X17)),X17) ),
    inference(superposition,[],[f204,f204])).

fof(f431,plain,(
    ! [X28,X27] : k4_xboole_0(k2_xboole_0(X27,X28),k4_xboole_0(k2_xboole_0(X27,X28),X27)) = X27 ),
    inference(superposition,[],[f204,f129])).

fof(f129,plain,(
    ! [X8,X7] : k2_xboole_0(X7,X8) = k2_xboole_0(k2_xboole_0(X7,X8),X7) ),
    inference(forward_demodulation,[],[f125,f43])).

fof(f43,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f38,f19])).

fof(f38,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f24,f19])).

fof(f125,plain,(
    ! [X8,X7] : k2_xboole_0(k2_xboole_0(X7,X8),X7) = k2_xboole_0(k2_xboole_0(X7,X8),k1_xboole_0) ),
    inference(superposition,[],[f23,f106])).

fof(f106,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f78,f97])).

fof(f97,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f92,f43])).

fof(f78,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f27,f33])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f24,f23])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f21])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (21222)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.43  % (21216)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.46  % (21210)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (21217)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (21209)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (21218)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (21211)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (21221)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (21212)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (21214)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (21213)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (21219)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.50  % (21216)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f3633,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f3598,f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.20/0.50    inference(negated_conjecture,[],[f10])).
% 0.20/0.50  fof(f10,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 0.20/0.50  fof(f3598,plain,(
% 0.20/0.50    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.20/0.50    inference(superposition,[],[f593,f2838])).
% 0.20/0.50  fof(f2838,plain,(
% 0.20/0.50    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.50    inference(forward_demodulation,[],[f2786,f441])).
% 0.20/0.50  fof(f441,plain,(
% 0.20/0.50    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(X4,X3)) )),
% 0.20/0.50    inference(superposition,[],[f275,f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.50  fof(f275,plain,(
% 0.20/0.50    ( ! [X4,X5] : (k2_xboole_0(X5,X4) = k4_xboole_0(k2_xboole_0(X4,X5),k1_xboole_0)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f255,f92])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f83,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 0.20/0.50    inference(superposition,[],[f27,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.50    inference(backward_demodulation,[],[f28,f19])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f18,f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.50  fof(f255,plain,(
% 0.20/0.50    ( ! [X4,X5] : (k2_xboole_0(X5,X4) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X4,k2_xboole_0(X5,X4)))) )),
% 0.20/0.50    inference(superposition,[],[f204,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f39,f23])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(superposition,[],[f23,f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    ( ! [X17,X16] : (k4_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X16,X17)) = X17) )),
% 0.20/0.50    inference(forward_demodulation,[],[f203,f19])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    ( ! [X17,X16] : (k4_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X16,X17)) = k4_xboole_0(X17,k1_xboole_0)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f176,f92])).
% 0.20/0.50  fof(f176,plain,(
% 0.20/0.50    ( ! [X17,X16] : (k4_xboole_0(X17,k4_xboole_0(X17,k2_xboole_0(X16,X17))) = k4_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X16,X17))) )),
% 0.20/0.50    inference(superposition,[],[f29,f24])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f20,f21,f21])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.50  fof(f2786,plain,(
% 0.20/0.50    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))),
% 0.20/0.50    inference(superposition,[],[f998,f452])).
% 0.20/0.50  fof(f452,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X2),X2)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f435,f19])).
% 0.20/0.50  fof(f435,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),X2) = k4_xboole_0(k2_xboole_0(X2,X3),k1_xboole_0)) )),
% 0.20/0.50    inference(superposition,[],[f275,f23])).
% 0.20/0.50  fof(f998,plain,(
% 0.20/0.50    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0)) )),
% 0.20/0.50    inference(superposition,[],[f27,f982])).
% 0.20/0.50  fof(f982,plain,(
% 0.20/0.50    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.50    inference(forward_demodulation,[],[f947,f19])).
% 0.20/0.50  fof(f947,plain,(
% 0.20/0.50    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.20/0.50    inference(superposition,[],[f30,f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.20/0.50    inference(resolution,[],[f32,f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f25,f21])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f22,f21])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.50  fof(f593,plain,(
% 0.20/0.50    ( ! [X4,X2,X3] : (r1_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2)))) )),
% 0.20/0.50    inference(superposition,[],[f517,f441])).
% 0.20/0.50  fof(f517,plain,(
% 0.20/0.50    ( ! [X21,X19,X20] : (r1_xboole_0(X21,k4_xboole_0(X19,k2_xboole_0(X20,X21)))) )),
% 0.20/0.50    inference(superposition,[],[f504,f27])).
% 0.20/0.50  fof(f504,plain,(
% 0.20/0.50    ( ! [X14,X13] : (r1_xboole_0(X13,k4_xboole_0(X14,X13))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f500,f33])).
% 0.20/0.50  fof(f500,plain,(
% 0.20/0.50    ( ! [X14,X13] : (k1_xboole_0 != k4_xboole_0(X13,X13) | r1_xboole_0(X13,k4_xboole_0(X14,X13))) )),
% 0.20/0.50    inference(superposition,[],[f31,f471])).
% 0.20/0.50  fof(f471,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 0.20/0.50    inference(backward_demodulation,[],[f35,f470])).
% 0.20/0.50  fof(f470,plain,(
% 0.20/0.50    ( ! [X28,X27] : (k4_xboole_0(k2_xboole_0(X27,X28),k4_xboole_0(X28,X27)) = X27) )),
% 0.20/0.50    inference(backward_demodulation,[],[f431,f469])).
% 0.20/0.50  fof(f469,plain,(
% 0.20/0.50    ( ! [X17,X16] : (k4_xboole_0(X16,X17) = k4_xboole_0(k2_xboole_0(X17,X16),X17)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f468,f456])).
% 0.20/0.50  fof(f456,plain,(
% 0.20/0.50    ( ! [X10,X9] : (k2_xboole_0(X10,X9) = k2_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X9,X10))) )),
% 0.20/0.50    inference(backward_demodulation,[],[f272,f452])).
% 0.20/0.50  fof(f272,plain,(
% 0.20/0.50    ( ! [X10,X9] : (k2_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X9,X10)) = k2_xboole_0(k4_xboole_0(X9,X10),X10)) )),
% 0.20/0.50    inference(superposition,[],[f23,f204])).
% 0.20/0.50  fof(f468,plain,(
% 0.20/0.50    ( ! [X17,X16] : (k4_xboole_0(X16,X17) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X16,X17),k2_xboole_0(X16,X17)),X17)) )),
% 0.20/0.50    inference(backward_demodulation,[],[f266,f441])).
% 0.20/0.50  fof(f266,plain,(
% 0.20/0.50    ( ! [X17,X16] : (k4_xboole_0(X16,X17) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X16,X17)),X17)) )),
% 0.20/0.50    inference(superposition,[],[f204,f204])).
% 0.20/0.50  fof(f431,plain,(
% 0.20/0.50    ( ! [X28,X27] : (k4_xboole_0(k2_xboole_0(X27,X28),k4_xboole_0(k2_xboole_0(X27,X28),X27)) = X27) )),
% 0.20/0.50    inference(superposition,[],[f204,f129])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    ( ! [X8,X7] : (k2_xboole_0(X7,X8) = k2_xboole_0(k2_xboole_0(X7,X8),X7)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f125,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.20/0.50    inference(forward_demodulation,[],[f38,f19])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 0.20/0.50    inference(superposition,[],[f24,f19])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    ( ! [X8,X7] : (k2_xboole_0(k2_xboole_0(X7,X8),X7) = k2_xboole_0(k2_xboole_0(X7,X8),k1_xboole_0)) )),
% 0.20/0.50    inference(superposition,[],[f23,f106])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 0.20/0.50    inference(backward_demodulation,[],[f78,f97])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 0.20/0.50    inference(superposition,[],[f92,f43])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 0.20/0.50    inference(superposition,[],[f27,f33])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.20/0.50    inference(superposition,[],[f24,f23])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f26,f21])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (21216)------------------------------
% 0.20/0.50  % (21216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21216)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (21216)Memory used [KB]: 12665
% 0.20/0.50  % (21216)Time elapsed: 0.069 s
% 0.20/0.50  % (21216)------------------------------
% 0.20/0.50  % (21216)------------------------------
% 0.20/0.50  % (21206)Success in time 0.143 s
%------------------------------------------------------------------------------
