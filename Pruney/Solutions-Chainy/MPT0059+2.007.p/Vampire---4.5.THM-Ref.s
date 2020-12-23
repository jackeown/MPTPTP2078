%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:13 EST 2020

% Result     : Theorem 1.11s
% Output     : Refutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 290 expanded)
%              Number of leaves         :   10 ( 103 expanded)
%              Depth                    :   11
%              Number of atoms          :   64 ( 316 expanded)
%              Number of equality atoms :   41 ( 282 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f678,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f129,f369,f641,f648,f668])).

fof(f668,plain,
    ( ~ spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f583,f126,f366])).

fof(f366,plain,
    ( spl3_3
  <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f126,plain,
    ( spl3_2
  <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f583,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))))
    | spl3_2 ),
    inference(superposition,[],[f128,f337])).

fof(f337,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,X5))) ),
    inference(superposition,[],[f133,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f18,f13])).

fof(f13,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f18,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f133,plain,(
    ! [X12,X13,X11] : k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X13)) = k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,X13))) ),
    inference(forward_demodulation,[],[f132,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f14,f13])).

fof(f14,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f132,plain,(
    ! [X12,X13,X11] : k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X13)) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,X13))))) ),
    inference(forward_demodulation,[],[f106,f51])).

fof(f51,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X4),X5)) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5))) ),
    inference(superposition,[],[f21,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f15,f13,f13])).

fof(f15,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f106,plain,(
    ! [X12,X13,X11] : k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X13)) = k4_xboole_0(X11,k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X13)))) ),
    inference(superposition,[],[f20,f23])).

fof(f128,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f648,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f645])).

fof(f645,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f368,f644])).

fof(f644,plain,(
    ! [X23,X21,X22] : k4_xboole_0(X22,k4_xboole_0(X21,X23)) = k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,X23)))) ),
    inference(forward_demodulation,[],[f561,f20])).

fof(f561,plain,(
    ! [X23,X21,X22] : k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X21,X23)))) = k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,X23)))) ),
    inference(superposition,[],[f337,f337])).

fof(f368,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f366])).

fof(f641,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f634])).

fof(f634,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f128,f633])).

fof(f633,plain,(
    ! [X17,X15,X16] : k4_xboole_0(X16,k4_xboole_0(X15,X17)) = k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X16,X17)))) ),
    inference(forward_demodulation,[],[f559,f338])).

fof(f338,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k4_xboole_0(X7,X8)) = k4_xboole_0(X6,k4_xboole_0(X7,k4_xboole_0(X6,k4_xboole_0(X7,X8)))) ),
    inference(superposition,[],[f133,f101])).

fof(f101,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X10,k4_xboole_0(X8,X9)) = k2_xboole_0(k4_xboole_0(X10,X8),k4_xboole_0(X10,k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f23,f20])).

fof(f559,plain,(
    ! [X17,X15,X16] : k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X16,X17)))) = k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X16,k4_xboole_0(X15,X17)))) ),
    inference(superposition,[],[f337,f337])).

fof(f369,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f340,f25,f366])).

fof(f25,plain,
    ( spl3_1
  <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f340,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))))
    | spl3_1 ),
    inference(superposition,[],[f27,f133])).

fof(f27,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f129,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f104,f25,f126])).

fof(f104,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))))
    | spl3_1 ),
    inference(superposition,[],[f27,f23])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f19,f25])).

fof(f19,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(definition_unfolding,[],[f12,f13])).

fof(f12,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:55:59 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.45  % (6363)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.46  % (6364)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.46  % (6364)Refutation not found, incomplete strategy% (6364)------------------------------
% 0.22/0.46  % (6364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (6364)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (6364)Memory used [KB]: 10490
% 0.22/0.46  % (6364)Time elapsed: 0.003 s
% 0.22/0.46  % (6364)------------------------------
% 0.22/0.46  % (6364)------------------------------
% 0.22/0.52  % (6366)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.53  % (6358)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 1.11/0.53  % (6357)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 1.11/0.54  % (6356)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 1.11/0.54  % (6363)Refutation found. Thanks to Tanya!
% 1.11/0.54  % SZS status Theorem for theBenchmark
% 1.11/0.54  % SZS output start Proof for theBenchmark
% 1.11/0.54  fof(f678,plain,(
% 1.11/0.54    $false),
% 1.11/0.54    inference(avatar_sat_refutation,[],[f28,f129,f369,f641,f648,f668])).
% 1.11/0.54  fof(f668,plain,(
% 1.11/0.54    ~spl3_3 | spl3_2),
% 1.11/0.54    inference(avatar_split_clause,[],[f583,f126,f366])).
% 1.11/0.54  fof(f366,plain,(
% 1.11/0.54    spl3_3 <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))))),
% 1.11/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.11/0.54  fof(f126,plain,(
% 1.11/0.54    spl3_2 <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))))),
% 1.11/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.11/0.54  fof(f583,plain,(
% 1.11/0.54    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) | spl3_2),
% 1.11/0.54    inference(superposition,[],[f128,f337])).
% 1.11/0.54  fof(f337,plain,(
% 1.11/0.54    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,X5)))) )),
% 1.11/0.54    inference(superposition,[],[f133,f23])).
% 1.11/0.54  fof(f23,plain,(
% 1.11/0.54    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 1.11/0.54    inference(definition_unfolding,[],[f18,f13])).
% 1.11/0.54  fof(f13,plain,(
% 1.11/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.11/0.54    inference(cnf_transformation,[],[f4])).
% 1.11/0.54  fof(f4,axiom,(
% 1.11/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.11/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.11/0.54  fof(f18,plain,(
% 1.11/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 1.11/0.54    inference(cnf_transformation,[],[f1])).
% 1.11/0.54  fof(f1,axiom,(
% 1.11/0.54    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.11/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).
% 1.11/0.54  fof(f133,plain,(
% 1.11/0.54    ( ! [X12,X13,X11] : (k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X13)) = k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,X13)))) )),
% 1.11/0.54    inference(forward_demodulation,[],[f132,f20])).
% 1.11/0.54  fof(f20,plain,(
% 1.11/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.11/0.54    inference(definition_unfolding,[],[f14,f13])).
% 1.11/0.54  fof(f14,plain,(
% 1.11/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.11/0.54    inference(cnf_transformation,[],[f3])).
% 1.11/0.54  fof(f3,axiom,(
% 1.11/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.11/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.11/0.54  fof(f132,plain,(
% 1.11/0.54    ( ! [X12,X13,X11] : (k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X13)) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,X13)))))) )),
% 1.11/0.54    inference(forward_demodulation,[],[f106,f51])).
% 1.11/0.54  fof(f51,plain,(
% 1.11/0.54    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X4),X5)) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5)))) )),
% 1.11/0.54    inference(superposition,[],[f21,f16])).
% 1.11/0.54  fof(f16,plain,(
% 1.11/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.11/0.54    inference(cnf_transformation,[],[f2])).
% 1.11/0.54  fof(f2,axiom,(
% 1.11/0.54    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.11/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.11/0.54  fof(f21,plain,(
% 1.11/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.11/0.54    inference(definition_unfolding,[],[f15,f13,f13])).
% 1.11/0.54  fof(f15,plain,(
% 1.11/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.11/0.54    inference(cnf_transformation,[],[f5])).
% 1.11/0.54  fof(f5,axiom,(
% 1.11/0.54    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.11/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.11/0.54  fof(f106,plain,(
% 1.11/0.54    ( ! [X12,X13,X11] : (k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X13)) = k4_xboole_0(X11,k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X13))))) )),
% 1.11/0.54    inference(superposition,[],[f20,f23])).
% 1.11/0.54  fof(f128,plain,(
% 1.11/0.54    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))) | spl3_2),
% 1.11/0.54    inference(avatar_component_clause,[],[f126])).
% 1.11/0.54  fof(f648,plain,(
% 1.11/0.54    spl3_3),
% 1.11/0.54    inference(avatar_contradiction_clause,[],[f645])).
% 1.11/0.54  fof(f645,plain,(
% 1.11/0.54    $false | spl3_3),
% 1.11/0.54    inference(subsumption_resolution,[],[f368,f644])).
% 1.11/0.54  fof(f644,plain,(
% 1.11/0.54    ( ! [X23,X21,X22] : (k4_xboole_0(X22,k4_xboole_0(X21,X23)) = k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,X23))))) )),
% 1.11/0.54    inference(forward_demodulation,[],[f561,f20])).
% 1.11/0.54  fof(f561,plain,(
% 1.11/0.54    ( ! [X23,X21,X22] : (k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X21,X23)))) = k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,X23))))) )),
% 1.11/0.54    inference(superposition,[],[f337,f337])).
% 1.11/0.54  fof(f368,plain,(
% 1.11/0.54    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) | spl3_3),
% 1.11/0.54    inference(avatar_component_clause,[],[f366])).
% 1.11/0.54  fof(f641,plain,(
% 1.11/0.54    spl3_2),
% 1.11/0.54    inference(avatar_contradiction_clause,[],[f634])).
% 1.11/0.54  fof(f634,plain,(
% 1.11/0.54    $false | spl3_2),
% 1.11/0.54    inference(subsumption_resolution,[],[f128,f633])).
% 1.11/0.54  fof(f633,plain,(
% 1.11/0.54    ( ! [X17,X15,X16] : (k4_xboole_0(X16,k4_xboole_0(X15,X17)) = k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X16,X17))))) )),
% 1.11/0.54    inference(forward_demodulation,[],[f559,f338])).
% 1.11/0.54  fof(f338,plain,(
% 1.11/0.54    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k4_xboole_0(X7,X8)) = k4_xboole_0(X6,k4_xboole_0(X7,k4_xboole_0(X6,k4_xboole_0(X7,X8))))) )),
% 1.11/0.54    inference(superposition,[],[f133,f101])).
% 1.11/0.54  fof(f101,plain,(
% 1.11/0.54    ( ! [X10,X8,X9] : (k4_xboole_0(X10,k4_xboole_0(X8,X9)) = k2_xboole_0(k4_xboole_0(X10,X8),k4_xboole_0(X10,k4_xboole_0(X8,X9)))) )),
% 1.11/0.54    inference(superposition,[],[f23,f20])).
% 1.11/0.54  fof(f559,plain,(
% 1.11/0.54    ( ! [X17,X15,X16] : (k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X16,X17)))) = k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X16,k4_xboole_0(X15,X17))))) )),
% 1.11/0.54    inference(superposition,[],[f337,f337])).
% 1.11/0.54  fof(f369,plain,(
% 1.11/0.54    ~spl3_3 | spl3_1),
% 1.11/0.54    inference(avatar_split_clause,[],[f340,f25,f366])).
% 1.11/0.54  fof(f25,plain,(
% 1.11/0.54    spl3_1 <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 1.11/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.11/0.54  fof(f340,plain,(
% 1.11/0.54    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) | spl3_1),
% 1.11/0.54    inference(superposition,[],[f27,f133])).
% 1.11/0.54  fof(f27,plain,(
% 1.11/0.54    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | spl3_1),
% 1.11/0.54    inference(avatar_component_clause,[],[f25])).
% 1.11/0.54  fof(f129,plain,(
% 1.11/0.54    ~spl3_2 | spl3_1),
% 1.11/0.54    inference(avatar_split_clause,[],[f104,f25,f126])).
% 1.11/0.54  fof(f104,plain,(
% 1.11/0.54    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))) | spl3_1),
% 1.11/0.54    inference(superposition,[],[f27,f23])).
% 1.11/0.54  fof(f28,plain,(
% 1.11/0.54    ~spl3_1),
% 1.11/0.54    inference(avatar_split_clause,[],[f19,f25])).
% 1.11/0.54  fof(f19,plain,(
% 1.11/0.54    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 1.11/0.54    inference(definition_unfolding,[],[f12,f13])).
% 1.11/0.54  fof(f12,plain,(
% 1.11/0.54    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.11/0.54    inference(cnf_transformation,[],[f11])).
% 1.11/0.54  fof(f11,plain,(
% 1.11/0.54    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.11/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).
% 1.11/0.54  fof(f10,plain,(
% 1.11/0.54    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) => k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.11/0.54    introduced(choice_axiom,[])).
% 1.11/0.54  fof(f9,plain,(
% 1.11/0.54    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.11/0.54    inference(ennf_transformation,[],[f8])).
% 1.11/0.54  fof(f8,negated_conjecture,(
% 1.11/0.54    ~! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.11/0.54    inference(negated_conjecture,[],[f7])).
% 1.11/0.54  fof(f7,conjecture,(
% 1.11/0.54    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.11/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.11/0.54  % SZS output end Proof for theBenchmark
% 1.11/0.54  % (6363)------------------------------
% 1.11/0.54  % (6363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.11/0.54  % (6363)Termination reason: Refutation
% 1.11/0.54  
% 1.11/0.54  % (6363)Memory used [KB]: 6908
% 1.11/0.54  % (6363)Time elapsed: 0.087 s
% 1.11/0.54  % (6363)------------------------------
% 1.11/0.54  % (6363)------------------------------
% 1.11/0.54  % (6352)Success in time 0.169 s
%------------------------------------------------------------------------------
