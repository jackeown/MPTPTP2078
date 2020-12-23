%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 182 expanded)
%              Number of leaves         :   17 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  133 ( 299 expanded)
%              Number of equality atoms :   40 ( 143 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f807,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f139,f745,f796,f805,f806])).

fof(f806,plain,
    ( sK0 != k3_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f805,plain,
    ( ~ spl3_7
    | spl3_14 ),
    inference(avatar_contradiction_clause,[],[f804])).

fof(f804,plain,
    ( $false
    | ~ spl3_7
    | spl3_14 ),
    inference(subsumption_resolution,[],[f803,f730])).

fof(f730,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_7 ),
    inference(superposition,[],[f323,f138])).

fof(f138,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl3_7
  <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f323,plain,
    ( ! [X10,X8,X9] : r1_tarski(k3_xboole_0(X10,k5_xboole_0(X8,k3_xboole_0(X8,X9))),X8)
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f322,f152])).

fof(f152,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f151,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f151,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k5_xboole_0(sK0,sK0))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f147,f23])).

fof(f147,plain,
    ( ! [X2] : k3_xboole_0(X2,k5_xboole_0(sK0,sK0)) = k5_xboole_0(k3_xboole_0(X2,sK0),k3_xboole_0(X2,sK0))
    | ~ spl3_7 ),
    inference(superposition,[],[f44,f138])).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f43,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f35,f27,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f322,plain,(
    ! [X10,X8,X9] :
      ( k1_xboole_0 != k3_xboole_0(X10,k1_xboole_0)
      | r1_tarski(k3_xboole_0(X10,k5_xboole_0(X8,k3_xboole_0(X8,X9))),X8) ) ),
    inference(forward_demodulation,[],[f310,f23])).

fof(f310,plain,(
    ! [X10,X8,X9] :
      ( k1_xboole_0 != k3_xboole_0(X10,k5_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X9)),k5_xboole_0(X8,k3_xboole_0(X8,X9))))
      | r1_tarski(k3_xboole_0(X10,k5_xboole_0(X8,k3_xboole_0(X8,X9))),X8) ) ),
    inference(superposition,[],[f102,f62])).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(unit_resulting_resolution,[],[f38,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f25,f27])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(forward_demodulation,[],[f94,f44])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(superposition,[],[f42,f36])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f803,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_14 ),
    inference(unit_resulting_resolution,[],[f795,f28])).

fof(f795,plain,
    ( sK0 != k3_xboole_0(sK0,sK1)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f793])).

fof(f793,plain,
    ( spl3_14
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f796,plain,
    ( spl3_13
    | ~ spl3_14
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f343,f136,f793,f789])).

fof(f789,plain,
    ( spl3_13
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f343,plain,
    ( sK0 != k3_xboole_0(sK0,sK1)
    | r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl3_7 ),
    inference(superposition,[],[f103,f138])).

% (25997)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f103,plain,(
    ! [X4,X5,X3] :
      ( k3_xboole_0(X3,X4) != k3_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X5)))
      | r1_xboole_0(k3_xboole_0(X3,X4),X5) ) ),
    inference(forward_demodulation,[],[f95,f44])).

fof(f95,plain,(
    ! [X4,X5,X3] :
      ( k3_xboole_0(X3,X4) != k5_xboole_0(k3_xboole_0(X3,X4),k3_xboole_0(X3,k3_xboole_0(X4,X5)))
      | r1_xboole_0(k3_xboole_0(X3,X4),X5) ) ),
    inference(superposition,[],[f39,f36])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f27])).

% (26003)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f745,plain,
    ( spl3_1
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f744])).

fof(f744,plain,
    ( $false
    | spl3_1
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f730,f48])).

fof(f48,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f139,plain,
    ( spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f61,f55,f136])).

fof(f55,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f61,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f57,f28])).

fof(f57,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f58,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f37,f55])).

fof(f37,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f21,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f53,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f22,f50,f46])).

fof(f50,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f22,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:39:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (25990)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.46  % (25991)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (25998)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (25989)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (26001)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (25992)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (25999)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (25986)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (25988)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (25985)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (25987)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (26001)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f807,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f53,f58,f139,f745,f796,f805,f806])).
% 0.22/0.50  fof(f806,plain,(
% 0.22/0.50    sK0 != k3_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK2) | ~r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f805,plain,(
% 0.22/0.50    ~spl3_7 | spl3_14),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f804])).
% 0.22/0.50  fof(f804,plain,(
% 0.22/0.50    $false | (~spl3_7 | spl3_14)),
% 0.22/0.50    inference(subsumption_resolution,[],[f803,f730])).
% 0.22/0.50  fof(f730,plain,(
% 0.22/0.50    r1_tarski(sK0,sK1) | ~spl3_7),
% 0.22/0.50    inference(superposition,[],[f323,f138])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f136])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    spl3_7 <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f323,plain,(
% 0.22/0.50    ( ! [X10,X8,X9] : (r1_tarski(k3_xboole_0(X10,k5_xboole_0(X8,k3_xboole_0(X8,X9))),X8)) ) | ~spl3_7),
% 0.22/0.50    inference(subsumption_resolution,[],[f322,f152])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) ) | ~spl3_7),
% 0.22/0.50    inference(forward_demodulation,[],[f151,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k5_xboole_0(sK0,sK0))) ) | ~spl3_7),
% 0.22/0.50    inference(forward_demodulation,[],[f147,f23])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    ( ! [X2] : (k3_xboole_0(X2,k5_xboole_0(sK0,sK0)) = k5_xboole_0(k3_xboole_0(X2,sK0),k3_xboole_0(X2,sK0))) ) | ~spl3_7),
% 0.22/0.50    inference(superposition,[],[f44,f138])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) )),
% 0.22/0.50    inference(backward_demodulation,[],[f43,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f35,f27,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.50  fof(f322,plain,(
% 0.22/0.50    ( ! [X10,X8,X9] : (k1_xboole_0 != k3_xboole_0(X10,k1_xboole_0) | r1_tarski(k3_xboole_0(X10,k5_xboole_0(X8,k3_xboole_0(X8,X9))),X8)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f310,f23])).
% 0.22/0.50  fof(f310,plain,(
% 0.22/0.50    ( ! [X10,X8,X9] : (k1_xboole_0 != k3_xboole_0(X10,k5_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X9)),k5_xboole_0(X8,k3_xboole_0(X8,X9)))) | r1_tarski(k3_xboole_0(X10,k5_xboole_0(X8,k3_xboole_0(X8,X9))),X8)) )),
% 0.22/0.50    inference(superposition,[],[f102,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f38,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f25,f27])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f94,f44])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 != k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.50    inference(superposition,[],[f42,f36])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f33,f27])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.50  fof(f803,plain,(
% 0.22/0.50    ~r1_tarski(sK0,sK1) | spl3_14),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f795,f28])).
% 0.22/0.50  fof(f795,plain,(
% 0.22/0.50    sK0 != k3_xboole_0(sK0,sK1) | spl3_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f793])).
% 0.22/0.50  fof(f793,plain,(
% 0.22/0.50    spl3_14 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.50  fof(f796,plain,(
% 0.22/0.50    spl3_13 | ~spl3_14 | ~spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f343,f136,f793,f789])).
% 0.22/0.50  fof(f789,plain,(
% 0.22/0.50    spl3_13 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.50  fof(f343,plain,(
% 0.22/0.50    sK0 != k3_xboole_0(sK0,sK1) | r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | ~spl3_7),
% 0.22/0.50    inference(superposition,[],[f103,f138])).
% 0.22/0.50  % (25997)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ( ! [X4,X5,X3] : (k3_xboole_0(X3,X4) != k3_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X5))) | r1_xboole_0(k3_xboole_0(X3,X4),X5)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f95,f44])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ( ! [X4,X5,X3] : (k3_xboole_0(X3,X4) != k5_xboole_0(k3_xboole_0(X3,X4),k3_xboole_0(X3,k3_xboole_0(X4,X5))) | r1_xboole_0(k3_xboole_0(X3,X4),X5)) )),
% 0.22/0.50    inference(superposition,[],[f39,f36])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f30,f27])).
% 0.22/0.50  % (26003)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.50  fof(f745,plain,(
% 0.22/0.50    spl3_1 | ~spl3_7),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f744])).
% 0.22/0.50  fof(f744,plain,(
% 0.22/0.50    $false | (spl3_1 | ~spl3_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f730,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    spl3_7 | ~spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f61,f55,f136])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    spl3_3 <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_3),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f57,f28])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f55])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f55])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.22/0.50    inference(definition_unfolding,[],[f21,f27])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.50    inference(negated_conjecture,[],[f12])).
% 0.22/0.50  fof(f12,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ~spl3_1 | ~spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f22,f50,f46])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (26001)------------------------------
% 0.22/0.50  % (26001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26001)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (26001)Memory used [KB]: 11129
% 0.22/0.50  % (26001)Time elapsed: 0.032 s
% 0.22/0.50  % (26001)------------------------------
% 0.22/0.50  % (26001)------------------------------
% 0.22/0.51  % (25983)Success in time 0.146 s
%------------------------------------------------------------------------------
