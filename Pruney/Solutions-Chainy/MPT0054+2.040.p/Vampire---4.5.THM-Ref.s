%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:03 EST 2020

% Result     : Theorem 5.01s
% Output     : Refutation 5.01s
% Verified   : 
% Statistics : Number of formulae       :   53 (  81 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :   61 (  93 expanded)
%              Number of equality atoms :   48 (  74 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22620,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f22553])).

fof(f22553,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f22552])).

fof(f22552,plain,
    ( $false
    | spl2_1 ),
    inference(trivial_inequality_removal,[],[f22551])).

fof(f22551,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)
    | spl2_1 ),
    inference(superposition,[],[f37,f20349])).

fof(f20349,plain,(
    ! [X47,X48] : k4_xboole_0(X47,X48) = k4_xboole_0(X47,k3_xboole_0(X47,X48)) ),
    inference(forward_demodulation,[],[f20206,f8903])).

fof(f8903,plain,(
    ! [X26,X24,X25] : k4_xboole_0(X26,X24) = k4_xboole_0(k4_xboole_0(X26,X24),k3_xboole_0(X25,X24)) ),
    inference(superposition,[],[f372,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f22,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f372,plain,(
    ! [X26,X27,X25] : k4_xboole_0(X26,k2_xboole_0(X27,X25)) = k4_xboole_0(k4_xboole_0(X26,k2_xboole_0(X27,X25)),X25) ),
    inference(forward_demodulation,[],[f371,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f371,plain,(
    ! [X26,X27,X25] : k4_xboole_0(k4_xboole_0(X26,k2_xboole_0(X27,X25)),X25) = k4_xboole_0(k4_xboole_0(X26,X27),X25) ),
    inference(forward_demodulation,[],[f357,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f23,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f357,plain,(
    ! [X26,X27,X25] : k4_xboole_0(k4_xboole_0(X26,k2_xboole_0(X27,X25)),X25) = k4_xboole_0(k2_xboole_0(X25,k4_xboole_0(X26,X27)),X25) ),
    inference(superposition,[],[f42,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f24,f26])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f20206,plain,(
    ! [X47,X48] : k4_xboole_0(k4_xboole_0(X47,X48),k3_xboole_0(X47,X48)) = k4_xboole_0(X47,k3_xboole_0(X47,X48)) ),
    inference(superposition,[],[f23,f16864])).

fof(f16864,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = X4 ),
    inference(forward_demodulation,[],[f16735,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f16735,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k2_xboole_0(X4,X5)) = k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f109,f7452])).

fof(f7452,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X8,X9),X9) ),
    inference(forward_demodulation,[],[f7451,f101])).

fof(f101,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f41,f23])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f25,f18])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f7451,plain,(
    ! [X8,X9] : k2_xboole_0(k4_xboole_0(X8,X9),X9) = k2_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f7362,f24])).

fof(f7362,plain,(
    ! [X8,X9] : k2_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(X8,X9)) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f24,f283])).

fof(f283,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f52,f20])).

fof(f52,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f23,f24])).

fof(f109,plain,(
    ! [X10,X8,X9] : k2_xboole_0(k4_xboole_0(X8,X9),k3_xboole_0(X8,X10)) = k3_xboole_0(X8,k2_xboole_0(k4_xboole_0(X8,X9),X10)) ),
    inference(superposition,[],[f27,f41])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f37,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_1
  <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f38,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (18891)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.41  % (18888)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.41  % (18889)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.41  % (18890)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.46  % (18885)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.46  % (18884)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.46  % (18886)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.46  % (18887)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.47  % (18892)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.48  % (18894)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.48  % (18895)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.48  % (18893)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 5.01/1.01  % (18885)Time limit reached!
% 5.01/1.01  % (18885)------------------------------
% 5.01/1.01  % (18885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.01/1.01  % (18885)Termination reason: Time limit
% 5.01/1.01  
% 5.01/1.01  % (18885)Memory used [KB]: 22259
% 5.01/1.01  % (18885)Time elapsed: 0.603 s
% 5.01/1.01  % (18885)------------------------------
% 5.01/1.01  % (18885)------------------------------
% 5.01/1.04  % (18890)Refutation found. Thanks to Tanya!
% 5.01/1.04  % SZS status Theorem for theBenchmark
% 5.01/1.04  % SZS output start Proof for theBenchmark
% 5.01/1.04  fof(f22620,plain,(
% 5.01/1.04    $false),
% 5.01/1.04    inference(avatar_sat_refutation,[],[f38,f22553])).
% 5.01/1.04  fof(f22553,plain,(
% 5.01/1.04    spl2_1),
% 5.01/1.04    inference(avatar_contradiction_clause,[],[f22552])).
% 5.01/1.04  fof(f22552,plain,(
% 5.01/1.04    $false | spl2_1),
% 5.01/1.04    inference(trivial_inequality_removal,[],[f22551])).
% 5.01/1.04  fof(f22551,plain,(
% 5.01/1.04    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) | spl2_1),
% 5.01/1.04    inference(superposition,[],[f37,f20349])).
% 5.01/1.04  fof(f20349,plain,(
% 5.01/1.04    ( ! [X47,X48] : (k4_xboole_0(X47,X48) = k4_xboole_0(X47,k3_xboole_0(X47,X48))) )),
% 5.01/1.04    inference(forward_demodulation,[],[f20206,f8903])).
% 5.01/1.04  fof(f8903,plain,(
% 5.01/1.04    ( ! [X26,X24,X25] : (k4_xboole_0(X26,X24) = k4_xboole_0(k4_xboole_0(X26,X24),k3_xboole_0(X25,X24))) )),
% 5.01/1.04    inference(superposition,[],[f372,f30])).
% 5.01/1.04  fof(f30,plain,(
% 5.01/1.04    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 5.01/1.04    inference(superposition,[],[f22,f19])).
% 5.01/1.04  fof(f19,plain,(
% 5.01/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.01/1.04    inference(cnf_transformation,[],[f2])).
% 5.01/1.04  fof(f2,axiom,(
% 5.01/1.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.01/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.01/1.04  fof(f22,plain,(
% 5.01/1.04    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 5.01/1.04    inference(cnf_transformation,[],[f5])).
% 5.01/1.04  fof(f5,axiom,(
% 5.01/1.04    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 5.01/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 5.01/1.04  fof(f372,plain,(
% 5.01/1.04    ( ! [X26,X27,X25] : (k4_xboole_0(X26,k2_xboole_0(X27,X25)) = k4_xboole_0(k4_xboole_0(X26,k2_xboole_0(X27,X25)),X25)) )),
% 5.01/1.04    inference(forward_demodulation,[],[f371,f26])).
% 5.01/1.04  fof(f26,plain,(
% 5.01/1.04    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 5.01/1.04    inference(cnf_transformation,[],[f10])).
% 5.01/1.04  fof(f10,axiom,(
% 5.01/1.04    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 5.01/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 5.01/1.04  fof(f371,plain,(
% 5.01/1.04    ( ! [X26,X27,X25] : (k4_xboole_0(k4_xboole_0(X26,k2_xboole_0(X27,X25)),X25) = k4_xboole_0(k4_xboole_0(X26,X27),X25)) )),
% 5.01/1.04    inference(forward_demodulation,[],[f357,f42])).
% 5.01/1.04  fof(f42,plain,(
% 5.01/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 5.01/1.04    inference(superposition,[],[f23,f20])).
% 5.01/1.04  fof(f20,plain,(
% 5.01/1.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 5.01/1.04    inference(cnf_transformation,[],[f1])).
% 5.01/1.04  fof(f1,axiom,(
% 5.01/1.04    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.01/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 5.01/1.04  fof(f23,plain,(
% 5.01/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 5.01/1.04    inference(cnf_transformation,[],[f9])).
% 5.01/1.04  fof(f9,axiom,(
% 5.01/1.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 5.01/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 5.01/1.04  fof(f357,plain,(
% 5.01/1.04    ( ! [X26,X27,X25] : (k4_xboole_0(k4_xboole_0(X26,k2_xboole_0(X27,X25)),X25) = k4_xboole_0(k2_xboole_0(X25,k4_xboole_0(X26,X27)),X25)) )),
% 5.01/1.04    inference(superposition,[],[f42,f64])).
% 5.01/1.04  fof(f64,plain,(
% 5.01/1.04    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 5.01/1.04    inference(superposition,[],[f24,f26])).
% 5.01/1.04  fof(f24,plain,(
% 5.01/1.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.01/1.04    inference(cnf_transformation,[],[f8])).
% 5.01/1.04  fof(f8,axiom,(
% 5.01/1.04    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.01/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 5.01/1.04  fof(f20206,plain,(
% 5.01/1.04    ( ! [X47,X48] : (k4_xboole_0(k4_xboole_0(X47,X48),k3_xboole_0(X47,X48)) = k4_xboole_0(X47,k3_xboole_0(X47,X48))) )),
% 5.01/1.04    inference(superposition,[],[f23,f16864])).
% 5.01/1.04  fof(f16864,plain,(
% 5.01/1.04    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = X4) )),
% 5.01/1.04    inference(forward_demodulation,[],[f16735,f21])).
% 5.01/1.04  fof(f21,plain,(
% 5.01/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 5.01/1.04    inference(cnf_transformation,[],[f4])).
% 5.01/1.04  fof(f4,axiom,(
% 5.01/1.04    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 5.01/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 5.01/1.04  fof(f16735,plain,(
% 5.01/1.04    ( ! [X4,X5] : (k3_xboole_0(X4,k2_xboole_0(X4,X5)) = k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5))) )),
% 5.01/1.04    inference(superposition,[],[f109,f7452])).
% 5.01/1.04  fof(f7452,plain,(
% 5.01/1.04    ( ! [X8,X9] : (k2_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X8,X9),X9)) )),
% 5.01/1.04    inference(forward_demodulation,[],[f7451,f101])).
% 5.01/1.04  fof(f101,plain,(
% 5.01/1.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 5.01/1.04    inference(superposition,[],[f41,f23])).
% 5.01/1.04  fof(f41,plain,(
% 5.01/1.04    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 5.01/1.04    inference(resolution,[],[f25,f18])).
% 5.01/1.04  fof(f18,plain,(
% 5.01/1.04    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 5.01/1.04    inference(cnf_transformation,[],[f7])).
% 5.01/1.04  fof(f7,axiom,(
% 5.01/1.04    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 5.01/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 5.01/1.04  fof(f25,plain,(
% 5.01/1.04    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 5.01/1.04    inference(cnf_transformation,[],[f14])).
% 5.01/1.04  fof(f14,plain,(
% 5.01/1.04    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 5.01/1.04    inference(ennf_transformation,[],[f3])).
% 5.01/1.04  fof(f3,axiom,(
% 5.01/1.04    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 5.01/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 5.01/1.04  fof(f7451,plain,(
% 5.01/1.04    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(X8,X9),X9) = k2_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(X8,X9))) )),
% 5.01/1.04    inference(forward_demodulation,[],[f7362,f24])).
% 5.01/1.04  fof(f7362,plain,(
% 5.01/1.04    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(X8,X9)) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X8,X9)))) )),
% 5.01/1.04    inference(superposition,[],[f24,f283])).
% 5.01/1.04  fof(f283,plain,(
% 5.01/1.04    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1))) )),
% 5.01/1.04    inference(superposition,[],[f52,f20])).
% 5.01/1.04  fof(f52,plain,(
% 5.01/1.04    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) )),
% 5.01/1.04    inference(superposition,[],[f23,f24])).
% 5.01/1.04  fof(f109,plain,(
% 5.01/1.04    ( ! [X10,X8,X9] : (k2_xboole_0(k4_xboole_0(X8,X9),k3_xboole_0(X8,X10)) = k3_xboole_0(X8,k2_xboole_0(k4_xboole_0(X8,X9),X10))) )),
% 5.01/1.04    inference(superposition,[],[f27,f41])).
% 5.01/1.04  fof(f27,plain,(
% 5.01/1.04    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 5.01/1.04    inference(cnf_transformation,[],[f6])).
% 5.01/1.04  fof(f6,axiom,(
% 5.01/1.04    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 5.01/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).
% 5.01/1.04  fof(f37,plain,(
% 5.01/1.04    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | spl2_1),
% 5.01/1.04    inference(avatar_component_clause,[],[f35])).
% 5.01/1.04  fof(f35,plain,(
% 5.01/1.04    spl2_1 <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 5.01/1.04    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 5.01/1.04  fof(f38,plain,(
% 5.01/1.04    ~spl2_1),
% 5.01/1.04    inference(avatar_split_clause,[],[f17,f35])).
% 5.01/1.04  fof(f17,plain,(
% 5.01/1.04    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 5.01/1.04    inference(cnf_transformation,[],[f16])).
% 5.01/1.04  fof(f16,plain,(
% 5.01/1.04    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 5.01/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15])).
% 5.01/1.04  fof(f15,plain,(
% 5.01/1.04    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 5.01/1.04    introduced(choice_axiom,[])).
% 5.01/1.04  fof(f13,plain,(
% 5.01/1.04    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.01/1.04    inference(ennf_transformation,[],[f12])).
% 5.01/1.04  fof(f12,negated_conjecture,(
% 5.01/1.04    ~! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.01/1.04    inference(negated_conjecture,[],[f11])).
% 5.01/1.04  fof(f11,conjecture,(
% 5.01/1.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.01/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 5.01/1.04  % SZS output end Proof for theBenchmark
% 5.01/1.04  % (18890)------------------------------
% 5.01/1.04  % (18890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.01/1.04  % (18890)Termination reason: Refutation
% 5.01/1.04  
% 5.01/1.04  % (18890)Memory used [KB]: 26993
% 5.01/1.04  % (18890)Time elapsed: 0.627 s
% 5.01/1.04  % (18890)------------------------------
% 5.01/1.04  % (18890)------------------------------
% 5.01/1.04  % (18883)Success in time 0.686 s
%------------------------------------------------------------------------------
