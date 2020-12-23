%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:38 EST 2020

% Result     : Theorem 2.98s
% Output     : Refutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 526 expanded)
%              Number of leaves         :   13 ( 165 expanded)
%              Depth                    :   19
%              Number of atoms          :  115 ( 862 expanded)
%              Number of equality atoms :   49 ( 388 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6943,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f1561,f6935])).

fof(f6935,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f6934])).

fof(f6934,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f6933,f43])).

fof(f43,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f6933,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f6896,f94])).

fof(f94,plain,(
    sK0 = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f64,f92])).

fof(f92,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f90,f47])).

fof(f47,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f32,f17])).

fof(f17,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f90,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f34,f63])).

fof(f63,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f20,f47])).

fof(f20,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f64,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)) ),
    inference(resolution,[],[f62,f32])).

fof(f62,plain,(
    r1_tarski(sK0,sK0) ),
    inference(superposition,[],[f21,f47])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f6896,plain,(
    r1_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK2) ),
    inference(superposition,[],[f6379,f129])).

fof(f129,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f112,f125])).

fof(f125,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f104,f94])).

fof(f104,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f29,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f19,f24])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f112,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f29,f47])).

fof(f6379,plain,(
    ! [X8,X7,X9] : r1_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X7,X8))),X8) ),
    inference(subsumption_resolution,[],[f6378,f30])).

fof(f6378,plain,(
    ! [X8,X7,X9] :
      ( k1_xboole_0 != k4_xboole_0(X9,k4_xboole_0(X9,k1_xboole_0))
      | r1_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X7,X8))),X8) ) ),
    inference(forward_demodulation,[],[f6321,f587])).

fof(f587,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f560,f104])).

fof(f560,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f29,f493])).

fof(f493,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f472,f110])).

fof(f110,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f29,f30])).

fof(f472,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f29,f412])).

fof(f412,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f89,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f22,f24,f24])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f89,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),X3)) ),
    inference(resolution,[],[f34,f20])).

fof(f6321,plain,(
    ! [X8,X7,X9] :
      ( k1_xboole_0 != k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,X8))))
      | r1_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X7,X8))),X8) ) ),
    inference(superposition,[],[f361,f1149])).

fof(f1149,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(k4_xboole_0(X5,X6),X6) ),
    inference(backward_demodulation,[],[f416,f1148])).

fof(f1148,plain,(
    ! [X41,X40] : k4_xboole_0(X40,X41) = k5_xboole_0(k4_xboole_0(X40,X41),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1078,f587])).

fof(f1078,plain,(
    ! [X41,X40] : k4_xboole_0(X40,X41) = k5_xboole_0(k4_xboole_0(X40,X41),k4_xboole_0(k4_xboole_0(X40,X41),k4_xboole_0(X40,X41))) ),
    inference(superposition,[],[f29,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(resolution,[],[f32,f21])).

fof(f416,plain,(
    ! [X6,X5] : k4_xboole_0(k4_xboole_0(X5,X6),X6) = k5_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0) ),
    inference(superposition,[],[f29,f89])).

fof(f361,plain,(
    ! [X12,X13,X11] :
      ( k1_xboole_0 != k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X12,X13))))
      | r1_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13) ) ),
    inference(superposition,[],[f33,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f28,f24,f24,f24,f24])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1561,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f1560])).

fof(f1560,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f1559,f39])).

fof(f39,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1559,plain,(
    r1_tarski(sK0,sK1) ),
    inference(forward_demodulation,[],[f1542,f94])).

fof(f1542,plain,(
    r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK1) ),
    inference(superposition,[],[f1071,f129])).

fof(f1071,plain,(
    ! [X28,X26,X27] : r1_tarski(k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X26,X27))),X26) ),
    inference(superposition,[],[f363,f48])).

fof(f363,plain,(
    ! [X19,X17,X18] : r1_tarski(k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X18,k4_xboole_0(X18,X19)))),X19) ),
    inference(superposition,[],[f165,f35])).

fof(f165,plain,(
    ! [X10,X9] : r1_tarski(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X9) ),
    inference(superposition,[],[f21,f31])).

fof(f44,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f18,f41,f37])).

fof(f18,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:31:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (18697)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (18701)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (18686)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (18695)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (18685)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (18688)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (18687)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (18692)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (18699)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (18698)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (18684)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (18690)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (18696)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.52  % (18691)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (18693)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (18694)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.53  % (18689)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.56  % (18700)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 2.98/0.78  % (18693)Refutation found. Thanks to Tanya!
% 2.98/0.78  % SZS status Theorem for theBenchmark
% 2.98/0.79  % SZS output start Proof for theBenchmark
% 2.98/0.79  fof(f6943,plain,(
% 2.98/0.79    $false),
% 2.98/0.79    inference(avatar_sat_refutation,[],[f44,f1561,f6935])).
% 2.98/0.79  fof(f6935,plain,(
% 2.98/0.79    spl3_2),
% 2.98/0.79    inference(avatar_contradiction_clause,[],[f6934])).
% 2.98/0.79  fof(f6934,plain,(
% 2.98/0.79    $false | spl3_2),
% 2.98/0.79    inference(subsumption_resolution,[],[f6933,f43])).
% 2.98/0.79  fof(f43,plain,(
% 2.98/0.79    ~r1_xboole_0(sK0,sK2) | spl3_2),
% 2.98/0.79    inference(avatar_component_clause,[],[f41])).
% 2.98/0.79  fof(f41,plain,(
% 2.98/0.79    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 2.98/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.98/0.79  fof(f6933,plain,(
% 2.98/0.79    r1_xboole_0(sK0,sK2)),
% 2.98/0.79    inference(forward_demodulation,[],[f6896,f94])).
% 2.98/0.79  fof(f94,plain,(
% 2.98/0.79    sK0 = k4_xboole_0(sK0,k1_xboole_0)),
% 2.98/0.79    inference(backward_demodulation,[],[f64,f92])).
% 2.98/0.79  fof(f92,plain,(
% 2.98/0.79    k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 2.98/0.79    inference(forward_demodulation,[],[f90,f47])).
% 2.98/0.79  fof(f47,plain,(
% 2.98/0.79    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 2.98/0.79    inference(resolution,[],[f32,f17])).
% 2.98/0.79  fof(f17,plain,(
% 2.98/0.79    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 2.98/0.79    inference(cnf_transformation,[],[f15])).
% 2.98/0.79  fof(f15,plain,(
% 2.98/0.79    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 2.98/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 2.98/0.79  fof(f14,plain,(
% 2.98/0.79    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 2.98/0.79    introduced(choice_axiom,[])).
% 3.42/0.79  fof(f12,plain,(
% 3.42/0.79    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.42/0.79    inference(ennf_transformation,[],[f11])).
% 3.42/0.79  fof(f11,negated_conjecture,(
% 3.42/0.79    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.42/0.79    inference(negated_conjecture,[],[f10])).
% 3.42/0.79  fof(f10,conjecture,(
% 3.42/0.79    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.42/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 3.42/0.79  fof(f32,plain,(
% 3.42/0.79    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 3.42/0.79    inference(definition_unfolding,[],[f25,f24])).
% 3.42/0.79  fof(f24,plain,(
% 3.42/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.42/0.79    inference(cnf_transformation,[],[f8])).
% 3.42/0.79  fof(f8,axiom,(
% 3.42/0.79    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.42/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.42/0.79  fof(f25,plain,(
% 3.42/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.42/0.79    inference(cnf_transformation,[],[f13])).
% 3.42/0.79  fof(f13,plain,(
% 3.42/0.79    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.42/0.79    inference(ennf_transformation,[],[f5])).
% 3.42/0.79  fof(f5,axiom,(
% 3.42/0.79    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.42/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.42/0.79  fof(f90,plain,(
% 3.42/0.79    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))))),
% 3.42/0.79    inference(resolution,[],[f34,f63])).
% 3.42/0.79  fof(f63,plain,(
% 3.42/0.79    r1_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 3.42/0.79    inference(superposition,[],[f20,f47])).
% 3.42/0.79  fof(f20,plain,(
% 3.42/0.79    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.42/0.79    inference(cnf_transformation,[],[f9])).
% 3.42/0.79  fof(f9,axiom,(
% 3.42/0.79    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.42/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 3.42/0.79  fof(f34,plain,(
% 3.42/0.79    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.42/0.79    inference(definition_unfolding,[],[f26,f24])).
% 3.42/0.79  fof(f26,plain,(
% 3.42/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.42/0.79    inference(cnf_transformation,[],[f16])).
% 3.42/0.79  fof(f16,plain,(
% 3.42/0.79    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.42/0.79    inference(nnf_transformation,[],[f2])).
% 3.42/0.79  fof(f2,axiom,(
% 3.42/0.79    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.42/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 3.42/0.79  fof(f64,plain,(
% 3.42/0.79    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK0))),
% 3.42/0.79    inference(resolution,[],[f62,f32])).
% 3.42/0.79  fof(f62,plain,(
% 3.42/0.79    r1_tarski(sK0,sK0)),
% 3.42/0.79    inference(superposition,[],[f21,f47])).
% 3.42/0.79  fof(f21,plain,(
% 3.42/0.79    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.42/0.79    inference(cnf_transformation,[],[f7])).
% 3.42/0.79  fof(f7,axiom,(
% 3.42/0.79    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.42/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.42/0.79  fof(f6896,plain,(
% 3.42/0.79    r1_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK2)),
% 3.42/0.79    inference(superposition,[],[f6379,f129])).
% 3.42/0.79  fof(f129,plain,(
% 3.42/0.79    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 3.42/0.79    inference(backward_demodulation,[],[f112,f125])).
% 3.42/0.79  fof(f125,plain,(
% 3.42/0.79    k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 3.42/0.79    inference(superposition,[],[f104,f94])).
% 3.42/0.79  fof(f104,plain,(
% 3.42/0.79    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.42/0.79    inference(superposition,[],[f29,f30])).
% 3.42/0.79  fof(f30,plain,(
% 3.42/0.79    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.42/0.79    inference(definition_unfolding,[],[f19,f24])).
% 3.42/0.79  fof(f19,plain,(
% 3.42/0.79    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.42/0.79    inference(cnf_transformation,[],[f6])).
% 3.42/0.79  fof(f6,axiom,(
% 3.42/0.79    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.42/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 3.42/0.79  fof(f29,plain,(
% 3.42/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.42/0.79    inference(definition_unfolding,[],[f23,f24])).
% 3.42/0.79  fof(f23,plain,(
% 3.42/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.42/0.79    inference(cnf_transformation,[],[f3])).
% 3.42/0.79  fof(f3,axiom,(
% 3.42/0.79    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.42/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.42/0.79  fof(f112,plain,(
% 3.42/0.79    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0)),
% 3.42/0.79    inference(superposition,[],[f29,f47])).
% 3.42/0.79  fof(f6379,plain,(
% 3.42/0.79    ( ! [X8,X7,X9] : (r1_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X7,X8))),X8)) )),
% 3.42/0.79    inference(subsumption_resolution,[],[f6378,f30])).
% 3.42/0.79  fof(f6378,plain,(
% 3.42/0.79    ( ! [X8,X7,X9] : (k1_xboole_0 != k4_xboole_0(X9,k4_xboole_0(X9,k1_xboole_0)) | r1_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X7,X8))),X8)) )),
% 3.42/0.79    inference(forward_demodulation,[],[f6321,f587])).
% 3.42/0.79  fof(f587,plain,(
% 3.42/0.79    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 3.42/0.79    inference(forward_demodulation,[],[f560,f104])).
% 3.42/0.79  fof(f560,plain,(
% 3.42/0.79    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0)) )),
% 3.42/0.79    inference(superposition,[],[f29,f493])).
% 3.42/0.79  fof(f493,plain,(
% 3.42/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.42/0.79    inference(forward_demodulation,[],[f472,f110])).
% 3.42/0.79  fof(f110,plain,(
% 3.42/0.79    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 3.42/0.79    inference(superposition,[],[f29,f30])).
% 3.42/0.79  fof(f472,plain,(
% 3.42/0.79    ( ! [X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.42/0.79    inference(superposition,[],[f29,f412])).
% 3.42/0.79  fof(f412,plain,(
% 3.42/0.79    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 3.42/0.79    inference(superposition,[],[f89,f31])).
% 3.42/0.79  fof(f31,plain,(
% 3.42/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.42/0.79    inference(definition_unfolding,[],[f22,f24,f24])).
% 3.42/0.79  fof(f22,plain,(
% 3.42/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.42/0.79    inference(cnf_transformation,[],[f1])).
% 3.42/0.79  fof(f1,axiom,(
% 3.42/0.79    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.42/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.42/0.79  fof(f89,plain,(
% 3.42/0.79    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),X3))) )),
% 3.42/0.79    inference(resolution,[],[f34,f20])).
% 3.42/0.79  fof(f6321,plain,(
% 3.42/0.79    ( ! [X8,X7,X9] : (k1_xboole_0 != k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,X8)))) | r1_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X7,X8))),X8)) )),
% 3.42/0.79    inference(superposition,[],[f361,f1149])).
% 3.42/0.79  fof(f1149,plain,(
% 3.42/0.79    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(k4_xboole_0(X5,X6),X6)) )),
% 3.42/0.79    inference(backward_demodulation,[],[f416,f1148])).
% 3.42/0.79  fof(f1148,plain,(
% 3.42/0.79    ( ! [X41,X40] : (k4_xboole_0(X40,X41) = k5_xboole_0(k4_xboole_0(X40,X41),k1_xboole_0)) )),
% 3.42/0.79    inference(forward_demodulation,[],[f1078,f587])).
% 3.42/0.79  fof(f1078,plain,(
% 3.42/0.79    ( ! [X41,X40] : (k4_xboole_0(X40,X41) = k5_xboole_0(k4_xboole_0(X40,X41),k4_xboole_0(k4_xboole_0(X40,X41),k4_xboole_0(X40,X41)))) )),
% 3.42/0.79    inference(superposition,[],[f29,f48])).
% 3.42/0.79  fof(f48,plain,(
% 3.42/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))) )),
% 3.42/0.79    inference(resolution,[],[f32,f21])).
% 3.42/0.79  fof(f416,plain,(
% 3.42/0.79    ( ! [X6,X5] : (k4_xboole_0(k4_xboole_0(X5,X6),X6) = k5_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0)) )),
% 3.42/0.79    inference(superposition,[],[f29,f89])).
% 3.42/0.79  fof(f361,plain,(
% 3.42/0.79    ( ! [X12,X13,X11] : (k1_xboole_0 != k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X12,X13)))) | r1_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13)) )),
% 3.42/0.79    inference(superposition,[],[f33,f35])).
% 3.42/0.79  fof(f35,plain,(
% 3.42/0.79    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 3.42/0.79    inference(definition_unfolding,[],[f28,f24,f24,f24,f24])).
% 3.42/0.79  fof(f28,plain,(
% 3.42/0.79    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 3.42/0.79    inference(cnf_transformation,[],[f4])).
% 3.42/0.79  fof(f4,axiom,(
% 3.42/0.79    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 3.42/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 3.42/0.79  fof(f33,plain,(
% 3.42/0.79    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.42/0.79    inference(definition_unfolding,[],[f27,f24])).
% 3.42/0.79  fof(f27,plain,(
% 3.42/0.79    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.42/0.79    inference(cnf_transformation,[],[f16])).
% 3.42/0.79  fof(f1561,plain,(
% 3.42/0.79    spl3_1),
% 3.42/0.79    inference(avatar_contradiction_clause,[],[f1560])).
% 3.42/0.79  fof(f1560,plain,(
% 3.42/0.79    $false | spl3_1),
% 3.42/0.79    inference(subsumption_resolution,[],[f1559,f39])).
% 3.42/0.79  fof(f39,plain,(
% 3.42/0.79    ~r1_tarski(sK0,sK1) | spl3_1),
% 3.42/0.79    inference(avatar_component_clause,[],[f37])).
% 3.42/0.79  fof(f37,plain,(
% 3.42/0.79    spl3_1 <=> r1_tarski(sK0,sK1)),
% 3.42/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 3.42/0.79  fof(f1559,plain,(
% 3.42/0.79    r1_tarski(sK0,sK1)),
% 3.42/0.79    inference(forward_demodulation,[],[f1542,f94])).
% 3.42/0.79  fof(f1542,plain,(
% 3.42/0.79    r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK1)),
% 3.42/0.79    inference(superposition,[],[f1071,f129])).
% 3.42/0.79  fof(f1071,plain,(
% 3.42/0.79    ( ! [X28,X26,X27] : (r1_tarski(k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X26,X27))),X26)) )),
% 3.42/0.79    inference(superposition,[],[f363,f48])).
% 3.42/0.79  fof(f363,plain,(
% 3.42/0.79    ( ! [X19,X17,X18] : (r1_tarski(k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X18,k4_xboole_0(X18,X19)))),X19)) )),
% 3.42/0.79    inference(superposition,[],[f165,f35])).
% 3.42/0.79  fof(f165,plain,(
% 3.42/0.79    ( ! [X10,X9] : (r1_tarski(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X9)) )),
% 3.42/0.79    inference(superposition,[],[f21,f31])).
% 3.42/0.79  fof(f44,plain,(
% 3.42/0.79    ~spl3_1 | ~spl3_2),
% 3.42/0.79    inference(avatar_split_clause,[],[f18,f41,f37])).
% 3.42/0.79  fof(f18,plain,(
% 3.42/0.79    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 3.42/0.79    inference(cnf_transformation,[],[f15])).
% 3.42/0.79  % SZS output end Proof for theBenchmark
% 3.42/0.79  % (18693)------------------------------
% 3.42/0.79  % (18693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.42/0.79  % (18693)Termination reason: Refutation
% 3.42/0.79  
% 3.42/0.79  % (18693)Memory used [KB]: 13560
% 3.42/0.79  % (18693)Time elapsed: 0.340 s
% 3.42/0.79  % (18693)------------------------------
% 3.42/0.79  % (18693)------------------------------
% 3.42/0.80  % (18683)Success in time 0.436 s
%------------------------------------------------------------------------------
