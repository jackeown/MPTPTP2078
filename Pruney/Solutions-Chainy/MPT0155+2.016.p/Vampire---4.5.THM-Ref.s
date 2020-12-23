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
% DateTime   : Thu Dec  3 12:33:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  95 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 ( 128 expanded)
%              Number of equality atoms :   43 (  88 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f48,f52,f62,f75,f81])).

fof(f81,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f47,f79])).

fof(f79,plain,
    ( ! [X10,X8,X9] : k1_enumset1(X8,X9,X10) = k5_xboole_0(k1_enumset1(X8,X8,X8),k4_xboole_0(k1_enumset1(X8,X9,X10),k1_enumset1(X8,X8,X8)))
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(superposition,[],[f41,f74])).

fof(f74,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X2,X0,X1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X2,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f41,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_1
  <=> ! [X1,X0] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f47,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_2
  <=> k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f75,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f70,f60,f50,f73])).

fof(f50,plain,
    ( spl3_3
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f60,plain,
    ( spl3_5
  <=> ! [X1,X3,X0,X2,X4] : k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1))),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f70,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X2,X0,X1)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f67,f51])).

fof(f51,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f67,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k1_enumset1(X2,X2,X0),k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X0))) = k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(superposition,[],[f61,f51])).

fof(f61,plain,
    ( ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1))),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f62,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f37,f60])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1))),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f25,f31,f20,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1))),k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f24,f20,f29,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f23,f20,f29])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f19])).

fof(f18,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f52,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f34,f50])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f22,f20,f19,f29])).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f48,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f35,f45])).

fof(f35,plain,(
    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f17,f30])).

fof(f17,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f42,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f36,f40])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) ),
    inference(definition_unfolding,[],[f21,f20,f20,f20])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:49:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.43  % (25024)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.43  % (25016)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.44  % (25016)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f82,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f42,f48,f52,f62,f75,f81])).
% 0.20/0.44  fof(f81,plain,(
% 0.20/0.44    ~spl3_1 | spl3_2 | ~spl3_7),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f80])).
% 0.20/0.44  fof(f80,plain,(
% 0.20/0.44    $false | (~spl3_1 | spl3_2 | ~spl3_7)),
% 0.20/0.44    inference(subsumption_resolution,[],[f47,f79])).
% 0.20/0.44  fof(f79,plain,(
% 0.20/0.44    ( ! [X10,X8,X9] : (k1_enumset1(X8,X9,X10) = k5_xboole_0(k1_enumset1(X8,X8,X8),k4_xboole_0(k1_enumset1(X8,X9,X10),k1_enumset1(X8,X8,X8)))) ) | (~spl3_1 | ~spl3_7)),
% 0.20/0.44    inference(superposition,[],[f41,f74])).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X2,X0,X1)) ) | ~spl3_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f73])).
% 0.20/0.44  fof(f73,plain,(
% 0.20/0.44    spl3_7 <=> ! [X1,X0,X2] : k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X2,X0,X1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0))) ) | ~spl3_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f40])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    spl3_1 <=> ! [X1,X0] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0))) | spl3_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f45])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    spl3_2 <=> k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    spl3_7 | ~spl3_3 | ~spl3_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f70,f60,f50,f73])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    spl3_3 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    spl3_5 <=> ! [X1,X3,X0,X2,X4] : k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1))),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.44  fof(f70,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X2,X0,X1)) ) | (~spl3_3 | ~spl3_5)),
% 0.20/0.44    inference(forward_demodulation,[],[f67,f51])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1)))) ) | ~spl3_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f50])).
% 0.20/0.44  fof(f67,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X2,X2,X0),k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X0))) = k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)))) ) | (~spl3_3 | ~spl3_5)),
% 0.20/0.44    inference(superposition,[],[f61,f51])).
% 0.20/0.44  fof(f61,plain,(
% 0.20/0.44    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1))),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))) ) | ~spl3_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f60])).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    spl3_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f37,f60])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1))),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f25,f31,f20,f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1))),k1_enumset1(X0,X0,X0)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f24,f20,f29,f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f23,f20,f29])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.44    inference(definition_unfolding,[],[f18,f19])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,axiom,(
% 0.20/0.44    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    spl3_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f34,f50])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f22,f20,f19,f29])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.20/0.44  fof(f48,plain,(
% 0.20/0.44    ~spl3_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f35,f45])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))),
% 0.20/0.44    inference(definition_unfolding,[],[f17,f30])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.44    inference(ennf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.44    inference(negated_conjecture,[],[f12])).
% 0.20/0.44  fof(f12,conjecture,(
% 0.20/0.44    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    spl3_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f36,f40])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f21,f20,f20,f20])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (25016)------------------------------
% 0.20/0.44  % (25016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (25016)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (25016)Memory used [KB]: 6140
% 0.20/0.44  % (25016)Time elapsed: 0.011 s
% 0.20/0.44  % (25016)------------------------------
% 0.20/0.44  % (25016)------------------------------
% 0.20/0.45  % (25008)Success in time 0.094 s
%------------------------------------------------------------------------------
