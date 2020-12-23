%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:15 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 102 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 116 expanded)
%              Number of equality atoms :   55 ( 100 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1142,plain,(
    $false ),
    inference(resolution,[],[f1103,f903])).

fof(f903,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f902])).

fof(f902,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f839,f159])).

fof(f159,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f78,f27])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f78,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f63,f42])).

fof(f42,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f27,f24])).

fof(f24,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f63,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f34,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f839,plain,
    ( k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK0,sK1),sK0))
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f36,f202])).

fof(f202,plain,(
    ! [X8,X9] :
      ( k5_xboole_0(X8,X9) = k4_xboole_0(X9,X8)
      | ~ r1_tarski(X8,X9) ) ),
    inference(superposition,[],[f78,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f31,f29,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f36,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f22,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f20])).

fof(f20,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1103,plain,(
    ! [X8,X7] : r1_tarski(k4_xboole_0(X7,X8),X7) ),
    inference(trivial_inequality_removal,[],[f1087])).

fof(f1087,plain,(
    ! [X8,X7] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k4_xboole_0(X7,X8),X7) ) ),
    inference(superposition,[],[f33,f1024])).

fof(f1024,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),X9) ),
    inference(superposition,[],[f265,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f59,f24])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f37,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f51,f42])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f37,f25])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f37,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f26,f29])).

fof(f26,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f265,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X1,X0)) = k4_xboole_0(k4_xboole_0(X2,X0),X1) ),
    inference(forward_demodulation,[],[f239,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f35,f29])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f239,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X1,X0)) = k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f41,f39])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (19104)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.45  % (19093)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (19089)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (19088)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (19099)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (19101)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (19092)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (19098)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (19097)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (19095)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (19096)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (19091)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (19102)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (19105)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (19090)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (19099)Refutation not found, incomplete strategy% (19099)------------------------------
% 0.20/0.50  % (19099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (19099)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (19099)Memory used [KB]: 10490
% 0.20/0.50  % (19099)Time elapsed: 0.091 s
% 0.20/0.50  % (19099)------------------------------
% 0.20/0.50  % (19099)------------------------------
% 0.20/0.51  % (19100)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.51  % (19103)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.51  % (19094)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.38/0.53  % (19092)Refutation found. Thanks to Tanya!
% 1.38/0.53  % SZS status Theorem for theBenchmark
% 1.38/0.53  % SZS output start Proof for theBenchmark
% 1.38/0.53  fof(f1142,plain,(
% 1.38/0.53    $false),
% 1.38/0.53    inference(resolution,[],[f1103,f903])).
% 1.38/0.53  fof(f903,plain,(
% 1.38/0.53    ~r1_tarski(k4_xboole_0(sK0,sK1),sK0)),
% 1.38/0.53    inference(trivial_inequality_removal,[],[f902])).
% 1.38/0.53  fof(f902,plain,(
% 1.38/0.53    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) | ~r1_tarski(k4_xboole_0(sK0,sK1),sK0)),
% 1.38/0.53    inference(forward_demodulation,[],[f839,f159])).
% 1.38/0.53  fof(f159,plain,(
% 1.38/0.53    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.38/0.53    inference(superposition,[],[f78,f27])).
% 1.38/0.53  fof(f27,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f1])).
% 1.38/0.53  fof(f1,axiom,(
% 1.38/0.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.38/0.53  fof(f78,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.38/0.53    inference(forward_demodulation,[],[f63,f42])).
% 1.38/0.53  fof(f42,plain,(
% 1.38/0.53    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.38/0.53    inference(superposition,[],[f27,f24])).
% 1.38/0.53  fof(f24,plain,(
% 1.38/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.38/0.53    inference(cnf_transformation,[],[f10])).
% 1.38/0.53  fof(f10,axiom,(
% 1.38/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.38/0.53  fof(f63,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.38/0.53    inference(superposition,[],[f34,f23])).
% 1.38/0.53  fof(f23,plain,(
% 1.38/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f12])).
% 1.38/0.53  fof(f12,axiom,(
% 1.38/0.53    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.38/0.53  fof(f34,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f11])).
% 1.38/0.53  fof(f11,axiom,(
% 1.38/0.53    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.38/0.53  fof(f839,plain,(
% 1.38/0.53    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK0,sK1),sK0)) | ~r1_tarski(k4_xboole_0(sK0,sK1),sK0)),
% 1.38/0.53    inference(superposition,[],[f36,f202])).
% 1.38/0.53  fof(f202,plain,(
% 1.38/0.53    ( ! [X8,X9] : (k5_xboole_0(X8,X9) = k4_xboole_0(X9,X8) | ~r1_tarski(X8,X9)) )),
% 1.38/0.53    inference(superposition,[],[f78,f137])).
% 1.38/0.53  fof(f137,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.38/0.53    inference(backward_demodulation,[],[f40,f39])).
% 1.38/0.53  fof(f39,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 1.38/0.53    inference(definition_unfolding,[],[f31,f29,f29])).
% 1.38/0.53  fof(f29,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f13])).
% 1.38/0.53  fof(f13,axiom,(
% 1.38/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.38/0.53  fof(f31,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f3])).
% 1.38/0.53  fof(f3,axiom,(
% 1.38/0.53    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.38/0.53  fof(f40,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.38/0.53    inference(definition_unfolding,[],[f32,f29])).
% 1.38/0.53  fof(f32,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f18])).
% 1.38/0.53  fof(f18,plain,(
% 1.38/0.53    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 1.38/0.53    inference(ennf_transformation,[],[f6])).
% 1.38/0.53  fof(f6,axiom,(
% 1.38/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 1.38/0.53  fof(f36,plain,(
% 1.38/0.53    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.38/0.53    inference(definition_unfolding,[],[f22,f28])).
% 1.38/0.53  fof(f28,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f9])).
% 1.38/0.53  fof(f9,axiom,(
% 1.38/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.38/0.53  fof(f22,plain,(
% 1.38/0.53    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.38/0.53    inference(cnf_transformation,[],[f21])).
% 1.38/0.53  fof(f21,plain,(
% 1.38/0.53    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.38/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f20])).
% 1.38/0.53  fof(f20,plain,(
% 1.38/0.53    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.38/0.53    introduced(choice_axiom,[])).
% 1.38/0.53  fof(f17,plain,(
% 1.38/0.53    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.38/0.53    inference(ennf_transformation,[],[f15])).
% 1.38/0.53  fof(f15,negated_conjecture,(
% 1.38/0.53    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.38/0.53    inference(negated_conjecture,[],[f14])).
% 1.38/0.53  fof(f14,conjecture,(
% 1.38/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.38/0.53  fof(f1103,plain,(
% 1.38/0.53    ( ! [X8,X7] : (r1_tarski(k4_xboole_0(X7,X8),X7)) )),
% 1.38/0.53    inference(trivial_inequality_removal,[],[f1087])).
% 1.38/0.53  fof(f1087,plain,(
% 1.38/0.53    ( ! [X8,X7] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(X7,X8),X7)) )),
% 1.38/0.53    inference(superposition,[],[f33,f1024])).
% 1.38/0.53  fof(f1024,plain,(
% 1.38/0.53    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),X9)) )),
% 1.38/0.53    inference(superposition,[],[f265,f62])).
% 1.38/0.53  fof(f62,plain,(
% 1.38/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.38/0.53    inference(forward_demodulation,[],[f59,f24])).
% 1.38/0.53  fof(f59,plain,(
% 1.38/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) )),
% 1.38/0.53    inference(superposition,[],[f37,f56])).
% 1.38/0.53  fof(f56,plain,(
% 1.38/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.38/0.53    inference(forward_demodulation,[],[f51,f42])).
% 1.38/0.53  fof(f51,plain,(
% 1.38/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 1.38/0.53    inference(superposition,[],[f37,f25])).
% 1.38/0.53  fof(f25,plain,(
% 1.38/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.38/0.53    inference(cnf_transformation,[],[f4])).
% 1.38/0.53  fof(f4,axiom,(
% 1.38/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.38/0.53  fof(f37,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 1.38/0.53    inference(definition_unfolding,[],[f26,f29])).
% 1.38/0.53  fof(f26,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f7])).
% 1.38/0.53  fof(f7,axiom,(
% 1.38/0.53    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.38/0.53  fof(f265,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X1,X0)) = k4_xboole_0(k4_xboole_0(X2,X0),X1)) )),
% 1.38/0.53    inference(forward_demodulation,[],[f239,f41])).
% 1.38/0.53  fof(f41,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 1.38/0.53    inference(definition_unfolding,[],[f35,f29])).
% 1.38/0.53  fof(f35,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f5])).
% 1.38/0.53  fof(f5,axiom,(
% 1.38/0.53    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.38/0.53  fof(f239,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X1,X0)) = k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 1.38/0.53    inference(superposition,[],[f41,f39])).
% 1.38/0.53  fof(f33,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f19])).
% 1.38/0.53  fof(f19,plain,(
% 1.38/0.53    ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 1.38/0.53    inference(ennf_transformation,[],[f16])).
% 1.38/0.53  fof(f16,plain,(
% 1.38/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 => r1_tarski(X0,X1))),
% 1.38/0.53    inference(unused_predicate_definition_removal,[],[f2])).
% 1.38/0.53  fof(f2,axiom,(
% 1.38/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.38/0.53  % SZS output end Proof for theBenchmark
% 1.38/0.53  % (19092)------------------------------
% 1.38/0.53  % (19092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (19092)Termination reason: Refutation
% 1.38/0.53  
% 1.38/0.53  % (19092)Memory used [KB]: 6908
% 1.38/0.53  % (19092)Time elapsed: 0.126 s
% 1.38/0.53  % (19092)------------------------------
% 1.38/0.53  % (19092)------------------------------
% 1.38/0.54  % (19087)Success in time 0.178 s
%------------------------------------------------------------------------------
