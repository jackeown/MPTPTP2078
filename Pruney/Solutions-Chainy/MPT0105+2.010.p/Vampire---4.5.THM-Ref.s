%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:05 EST 2020

% Result     : Theorem 4.32s
% Output     : Refutation 4.54s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 170 expanded)
%              Number of leaves         :   12 (  55 expanded)
%              Depth                    :   21
%              Number of atoms          :   80 ( 186 expanded)
%              Number of equality atoms :   64 ( 164 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23036,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f23035])).

fof(f23035,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f19,f15770])).

fof(f15770,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k5_xboole_0(X4,k4_xboole_0(X5,X4)) ),
    inference(subsumption_resolution,[],[f15714,f22])).

fof(f22,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f15714,plain,(
    ! [X4,X5] :
      ( k2_xboole_0(X4,X5) = k5_xboole_0(X4,k4_xboole_0(X5,X4))
      | ~ r1_xboole_0(k4_xboole_0(X5,X4),X4) ) ),
    inference(superposition,[],[f12786,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f12786,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X1,X0) = k2_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(backward_demodulation,[],[f254,f12409])).

fof(f12409,plain,(
    ! [X4] : k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0)) = X4 ),
    inference(backward_demodulation,[],[f233,f12403])).

fof(f12403,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(backward_demodulation,[],[f44,f11929])).

fof(f11929,plain,(
    ! [X0] : k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(backward_demodulation,[],[f54,f11928])).

fof(f11928,plain,(
    ! [X15] : k5_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(forward_demodulation,[],[f11927,f4610])).

fof(f4610,plain,(
    ! [X2] : k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k3_xboole_0(X2,k1_xboole_0))) = X2 ),
    inference(superposition,[],[f1994,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1994,plain,(
    ! [X9] : k5_xboole_0(k5_xboole_0(X9,k1_xboole_0),k3_xboole_0(X9,k1_xboole_0)) = X9 ),
    inference(superposition,[],[f233,f210])).

fof(f210,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f195,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f195,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f35,f54])).

fof(f35,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f24,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f11927,plain,(
    ! [X15] : k5_xboole_0(X15,k1_xboole_0) = k5_xboole_0(X15,k5_xboole_0(k1_xboole_0,k3_xboole_0(X15,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f11877,f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f11877,plain,(
    ! [X15] : k5_xboole_0(X15,k5_xboole_0(k1_xboole_0,k3_xboole_0(X15,k1_xboole_0))) = k5_xboole_0(k2_xboole_0(X15,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f342,f10182])).

fof(f10182,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f9433,f29])).

fof(f9433,plain,(
    ! [X4] : k5_xboole_0(k1_xboole_0,X4) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X4),k1_xboole_0) ),
    inference(resolution,[],[f1045,f3994])).

fof(f3994,plain,(
    ! [X9] : r1_xboole_0(k5_xboole_0(k1_xboole_0,X9),k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X9))) ),
    inference(superposition,[],[f63,f78])).

fof(f78,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f29,f65])).

fof(f65,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f64,f21])).

fof(f64,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f58,f20])).

fof(f58,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f27,f42])).

fof(f42,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f33,f21])).

fof(f33,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f24,f21])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f63,plain,(
    ! [X6,X7] : r1_xboole_0(k5_xboole_0(X6,X7),k3_xboole_0(X6,X7)) ),
    inference(superposition,[],[f22,f27])).

fof(f1045,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))
      | k5_xboole_0(X1,k1_xboole_0) = X1 ) ),
    inference(superposition,[],[f113,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f113,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f54,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f342,plain,(
    ! [X6,X8,X7] : k5_xboole_0(k2_xboole_0(X6,X7),X8) = k5_xboole_0(X6,k5_xboole_0(X7,k5_xboole_0(k3_xboole_0(X6,X7),X8))) ),
    inference(forward_demodulation,[],[f333,f29])).

fof(f333,plain,(
    ! [X6,X8,X7] : k5_xboole_0(X6,k5_xboole_0(k5_xboole_0(X7,k3_xboole_0(X6,X7)),X8)) = k5_xboole_0(k2_xboole_0(X6,X7),X8) ),
    inference(superposition,[],[f29,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f29,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f27,f20])).

fof(f44,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = k4_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f24,f33])).

fof(f233,plain,(
    ! [X4] : k5_xboole_0(k3_xboole_0(X4,X4),k3_xboole_0(X4,k1_xboole_0)) = X4 ),
    inference(forward_demodulation,[],[f228,f20])).

fof(f228,plain,(
    ! [X4] : k2_xboole_0(X4,k1_xboole_0) = k5_xboole_0(k3_xboole_0(X4,X4),k3_xboole_0(X4,k1_xboole_0)) ),
    inference(superposition,[],[f26,f210])).

fof(f254,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f239,f29])).

fof(f239,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X0,k1_xboole_0))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f49,f39])).

fof(f39,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = k3_xboole_0(X1,k1_xboole_0)
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(forward_demodulation,[],[f34,f33])).

fof(f34,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = k4_xboole_0(X1,X1)
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(superposition,[],[f24,f28])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f26,f23])).

fof(f19,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (10534)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.43  % (10542)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.44  % (10532)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (10543)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (10536)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (10535)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (10544)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (10529)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (10533)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (10531)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (10540)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (10530)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (10540)Refutation not found, incomplete strategy% (10540)------------------------------
% 0.21/0.50  % (10540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10540)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (10540)Memory used [KB]: 10490
% 0.21/0.50  % (10540)Time elapsed: 0.094 s
% 0.21/0.50  % (10540)------------------------------
% 0.21/0.50  % (10540)------------------------------
% 0.21/0.51  % (10546)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (10541)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (10539)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (10538)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (10537)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (10545)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 4.32/0.92  % (10532)Refutation found. Thanks to Tanya!
% 4.32/0.92  % SZS status Theorem for theBenchmark
% 4.54/0.94  % SZS output start Proof for theBenchmark
% 4.54/0.94  fof(f23036,plain,(
% 4.54/0.94    $false),
% 4.54/0.94    inference(trivial_inequality_removal,[],[f23035])).
% 4.54/0.94  fof(f23035,plain,(
% 4.54/0.94    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)),
% 4.54/0.94    inference(superposition,[],[f19,f15770])).
% 4.54/0.94  fof(f15770,plain,(
% 4.54/0.94    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k5_xboole_0(X4,k4_xboole_0(X5,X4))) )),
% 4.54/0.94    inference(subsumption_resolution,[],[f15714,f22])).
% 4.54/0.94  fof(f22,plain,(
% 4.54/0.94    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 4.54/0.94    inference(cnf_transformation,[],[f8])).
% 4.54/0.94  fof(f8,axiom,(
% 4.54/0.94    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 4.54/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 4.54/0.94  fof(f15714,plain,(
% 4.54/0.94    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k5_xboole_0(X4,k4_xboole_0(X5,X4)) | ~r1_xboole_0(k4_xboole_0(X5,X4),X4)) )),
% 4.54/0.94    inference(superposition,[],[f12786,f25])).
% 4.54/0.94  fof(f25,plain,(
% 4.54/0.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.54/0.94    inference(cnf_transformation,[],[f5])).
% 4.54/0.94  fof(f5,axiom,(
% 4.54/0.94    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.54/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 4.54/0.94  fof(f12786,plain,(
% 4.54/0.94    ( ! [X0,X1] : (k5_xboole_0(X1,X0) = k2_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 4.54/0.94    inference(backward_demodulation,[],[f254,f12409])).
% 4.54/0.94  fof(f12409,plain,(
% 4.54/0.94    ( ! [X4] : (k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0)) = X4) )),
% 4.54/0.94    inference(backward_demodulation,[],[f233,f12403])).
% 4.54/0.94  fof(f12403,plain,(
% 4.54/0.94    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 4.54/0.94    inference(backward_demodulation,[],[f44,f11929])).
% 4.54/0.94  fof(f11929,plain,(
% 4.54/0.94    ( ! [X0] : (k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 4.54/0.94    inference(backward_demodulation,[],[f54,f11928])).
% 4.54/0.94  fof(f11928,plain,(
% 4.54/0.94    ( ! [X15] : (k5_xboole_0(X15,k1_xboole_0) = X15) )),
% 4.54/0.94    inference(forward_demodulation,[],[f11927,f4610])).
% 4.54/0.94  fof(f4610,plain,(
% 4.54/0.94    ( ! [X2] : (k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k3_xboole_0(X2,k1_xboole_0))) = X2) )),
% 4.54/0.94    inference(superposition,[],[f1994,f29])).
% 4.54/0.94  fof(f29,plain,(
% 4.54/0.94    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.54/0.94    inference(cnf_transformation,[],[f10])).
% 4.54/0.94  fof(f10,axiom,(
% 4.54/0.94    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.54/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.54/0.94  fof(f1994,plain,(
% 4.54/0.94    ( ! [X9] : (k5_xboole_0(k5_xboole_0(X9,k1_xboole_0),k3_xboole_0(X9,k1_xboole_0)) = X9) )),
% 4.54/0.94    inference(superposition,[],[f233,f210])).
% 4.54/0.94  fof(f210,plain,(
% 4.54/0.94    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 4.54/0.94    inference(forward_demodulation,[],[f195,f21])).
% 4.54/0.94  fof(f21,plain,(
% 4.54/0.94    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.54/0.94    inference(cnf_transformation,[],[f6])).
% 4.54/0.94  fof(f6,axiom,(
% 4.54/0.94    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.54/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 4.54/0.94  fof(f195,plain,(
% 4.54/0.94    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 4.54/0.94    inference(superposition,[],[f35,f54])).
% 4.54/0.94  fof(f35,plain,(
% 4.54/0.94    ( ! [X4,X3] : (k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 4.54/0.94    inference(superposition,[],[f24,f24])).
% 4.54/0.94  fof(f24,plain,(
% 4.54/0.94    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.54/0.94    inference(cnf_transformation,[],[f7])).
% 4.54/0.94  fof(f7,axiom,(
% 4.54/0.94    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.54/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.54/0.94  fof(f11927,plain,(
% 4.54/0.94    ( ! [X15] : (k5_xboole_0(X15,k1_xboole_0) = k5_xboole_0(X15,k5_xboole_0(k1_xboole_0,k3_xboole_0(X15,k1_xboole_0)))) )),
% 4.54/0.94    inference(forward_demodulation,[],[f11877,f20])).
% 4.54/0.94  fof(f20,plain,(
% 4.54/0.94    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.54/0.94    inference(cnf_transformation,[],[f4])).
% 4.54/0.94  fof(f4,axiom,(
% 4.54/0.94    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 4.54/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 4.54/0.94  fof(f11877,plain,(
% 4.54/0.94    ( ! [X15] : (k5_xboole_0(X15,k5_xboole_0(k1_xboole_0,k3_xboole_0(X15,k1_xboole_0))) = k5_xboole_0(k2_xboole_0(X15,k1_xboole_0),k1_xboole_0)) )),
% 4.54/0.94    inference(superposition,[],[f342,f10182])).
% 4.54/0.94  fof(f10182,plain,(
% 4.54/0.94    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))) )),
% 4.54/0.94    inference(superposition,[],[f9433,f29])).
% 4.54/0.94  fof(f9433,plain,(
% 4.54/0.94    ( ! [X4] : (k5_xboole_0(k1_xboole_0,X4) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X4),k1_xboole_0)) )),
% 4.54/0.94    inference(resolution,[],[f1045,f3994])).
% 4.54/0.94  fof(f3994,plain,(
% 4.54/0.94    ( ! [X9] : (r1_xboole_0(k5_xboole_0(k1_xboole_0,X9),k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X9)))) )),
% 4.54/0.94    inference(superposition,[],[f63,f78])).
% 4.54/0.94  fof(f78,plain,(
% 4.54/0.94    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 4.54/0.94    inference(superposition,[],[f29,f65])).
% 4.54/0.94  fof(f65,plain,(
% 4.54/0.94    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 4.54/0.94    inference(forward_demodulation,[],[f64,f21])).
% 4.54/0.94  fof(f64,plain,(
% 4.54/0.94    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 4.54/0.94    inference(forward_demodulation,[],[f58,f20])).
% 4.54/0.94  fof(f58,plain,(
% 4.54/0.94    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 4.54/0.94    inference(superposition,[],[f27,f42])).
% 4.54/0.94  fof(f42,plain,(
% 4.54/0.94    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)),
% 4.54/0.94    inference(superposition,[],[f33,f21])).
% 4.54/0.94  fof(f33,plain,(
% 4.54/0.94    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 4.54/0.94    inference(superposition,[],[f24,f21])).
% 4.54/0.94  fof(f27,plain,(
% 4.54/0.94    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 4.54/0.94    inference(cnf_transformation,[],[f3])).
% 4.54/0.94  fof(f3,axiom,(
% 4.54/0.94    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.54/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 4.54/0.94  fof(f63,plain,(
% 4.54/0.94    ( ! [X6,X7] : (r1_xboole_0(k5_xboole_0(X6,X7),k3_xboole_0(X6,X7))) )),
% 4.54/0.94    inference(superposition,[],[f22,f27])).
% 4.54/0.94  fof(f1045,plain,(
% 4.54/0.94    ( ! [X1] : (~r1_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) | k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 4.54/0.94    inference(superposition,[],[f113,f28])).
% 4.54/0.94  fof(f28,plain,(
% 4.54/0.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 4.54/0.94    inference(cnf_transformation,[],[f16])).
% 4.54/0.94  fof(f16,plain,(
% 4.54/0.94    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 4.54/0.94    inference(ennf_transformation,[],[f14])).
% 4.54/0.94  fof(f14,plain,(
% 4.54/0.94    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 4.54/0.94    inference(unused_predicate_definition_removal,[],[f9])).
% 4.54/0.94  fof(f9,axiom,(
% 4.54/0.94    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 4.54/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 4.54/0.94  fof(f113,plain,(
% 4.54/0.94    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) )),
% 4.54/0.94    inference(superposition,[],[f54,f23])).
% 4.54/0.94  fof(f23,plain,(
% 4.54/0.94    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.54/0.94    inference(cnf_transformation,[],[f1])).
% 4.54/0.94  fof(f1,axiom,(
% 4.54/0.94    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.54/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.54/0.94  fof(f342,plain,(
% 4.54/0.94    ( ! [X6,X8,X7] : (k5_xboole_0(k2_xboole_0(X6,X7),X8) = k5_xboole_0(X6,k5_xboole_0(X7,k5_xboole_0(k3_xboole_0(X6,X7),X8)))) )),
% 4.54/0.94    inference(forward_demodulation,[],[f333,f29])).
% 4.54/0.94  fof(f333,plain,(
% 4.54/0.94    ( ! [X6,X8,X7] : (k5_xboole_0(X6,k5_xboole_0(k5_xboole_0(X7,k3_xboole_0(X6,X7)),X8)) = k5_xboole_0(k2_xboole_0(X6,X7),X8)) )),
% 4.54/0.94    inference(superposition,[],[f29,f73])).
% 4.54/0.94  fof(f73,plain,(
% 4.54/0.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 4.54/0.94    inference(superposition,[],[f29,f26])).
% 4.54/0.94  fof(f26,plain,(
% 4.54/0.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 4.54/0.94    inference(cnf_transformation,[],[f11])).
% 4.54/0.94  fof(f11,axiom,(
% 4.54/0.94    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.54/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 4.54/0.94  fof(f54,plain,(
% 4.54/0.94    ( ! [X0] : (k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0)) )),
% 4.54/0.94    inference(superposition,[],[f27,f20])).
% 4.54/0.94  fof(f44,plain,(
% 4.54/0.94    ( ! [X1] : (k3_xboole_0(X1,X1) = k4_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) )),
% 4.54/0.94    inference(superposition,[],[f24,f33])).
% 4.54/0.94  fof(f233,plain,(
% 4.54/0.94    ( ! [X4] : (k5_xboole_0(k3_xboole_0(X4,X4),k3_xboole_0(X4,k1_xboole_0)) = X4) )),
% 4.54/0.94    inference(forward_demodulation,[],[f228,f20])).
% 4.54/0.94  fof(f228,plain,(
% 4.54/0.94    ( ! [X4] : (k2_xboole_0(X4,k1_xboole_0) = k5_xboole_0(k3_xboole_0(X4,X4),k3_xboole_0(X4,k1_xboole_0))) )),
% 4.54/0.94    inference(superposition,[],[f26,f210])).
% 4.54/0.94  fof(f254,plain,(
% 4.54/0.94    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) | ~r1_xboole_0(X0,X1)) )),
% 4.54/0.94    inference(forward_demodulation,[],[f239,f29])).
% 4.54/0.94  fof(f239,plain,(
% 4.54/0.94    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X0,k1_xboole_0)) | ~r1_xboole_0(X0,X1)) )),
% 4.54/0.94    inference(superposition,[],[f49,f39])).
% 4.54/0.94  fof(f39,plain,(
% 4.54/0.94    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k3_xboole_0(X1,k1_xboole_0) | ~r1_xboole_0(X1,X2)) )),
% 4.54/0.94    inference(forward_demodulation,[],[f34,f33])).
% 4.54/0.94  fof(f34,plain,(
% 4.54/0.94    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k4_xboole_0(X1,X1) | ~r1_xboole_0(X1,X2)) )),
% 4.54/0.94    inference(superposition,[],[f24,f28])).
% 4.54/0.94  fof(f49,plain,(
% 4.54/0.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0))) )),
% 4.54/0.94    inference(superposition,[],[f26,f23])).
% 4.54/0.94  fof(f19,plain,(
% 4.54/0.94    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 4.54/0.94    inference(cnf_transformation,[],[f18])).
% 4.54/0.94  fof(f18,plain,(
% 4.54/0.94    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 4.54/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 4.54/0.94  fof(f17,plain,(
% 4.54/0.94    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 4.54/0.94    introduced(choice_axiom,[])).
% 4.54/0.94  fof(f15,plain,(
% 4.54/0.94    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.54/0.94    inference(ennf_transformation,[],[f13])).
% 4.54/0.94  fof(f13,negated_conjecture,(
% 4.54/0.94    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.54/0.94    inference(negated_conjecture,[],[f12])).
% 4.54/0.94  fof(f12,conjecture,(
% 4.54/0.94    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.54/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 4.54/0.94  % SZS output end Proof for theBenchmark
% 4.54/0.94  % (10532)------------------------------
% 4.54/0.94  % (10532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/0.94  % (10532)Termination reason: Refutation
% 4.54/0.94  
% 4.54/0.94  % (10532)Memory used [KB]: 13176
% 4.54/0.94  % (10532)Time elapsed: 0.478 s
% 4.54/0.94  % (10532)------------------------------
% 4.54/0.94  % (10532)------------------------------
% 4.54/0.94  % (10525)Success in time 0.587 s
%------------------------------------------------------------------------------
