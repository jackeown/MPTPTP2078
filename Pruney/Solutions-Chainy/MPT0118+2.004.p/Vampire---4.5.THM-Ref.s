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
% DateTime   : Thu Dec  3 12:32:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  73 expanded)
%              Number of leaves         :   12 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 120 expanded)
%              Number of equality atoms :   36 (  65 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f27,f40,f44,f63,f67,f87])).

fof(f87,plain,
    ( ~ spl3_5
    | spl3_6
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f62,f78])).

fof(f78,plain,
    ( ! [X10,X11,X9] : k3_xboole_0(X9,k5_xboole_0(X10,k3_xboole_0(X10,X11))) = k3_xboole_0(X10,k5_xboole_0(X9,k3_xboole_0(X9,X11)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(superposition,[],[f66,f43])).

fof(f43,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f66,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f62,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) != k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_6
  <=> k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f67,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f45,f42,f21,f65])).

fof(f21,plain,
    ( spl3_1
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f45,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(superposition,[],[f43,f22])).

fof(f22,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f63,plain,
    ( ~ spl3_6
    | ~ spl3_2
    | spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f56,f42,f37,f25,f60])).

fof(f25,plain,
    ( spl3_2
  <=> ! [X1,X0] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f37,plain,
    ( spl3_4
  <=> k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f56,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) != k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_2
    | spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f51,f26])).

fof(f26,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f51,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) != k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))))
    | spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f39,f43])).

fof(f39,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f44,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f17,f42])).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f14,f12,f12])).

fof(f12,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f40,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f18,f11])).

fof(f11,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f18,plain,(
    k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1))) != k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
    inference(backward_demodulation,[],[f15,f11])).

fof(f15,plain,(
    k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1))) != k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f10,f12,f12])).

fof(f10,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1)
   => k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).

fof(f27,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f25])).

fof(f16,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f13,f12,f12])).

fof(f13,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f23,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f11,f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:00:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (6191)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (6191)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (6200)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f23,f27,f40,f44,f63,f67,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ~spl3_5 | spl3_6 | ~spl3_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    $false | (~spl3_5 | spl3_6 | ~spl3_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f62,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X10,X11,X9] : (k3_xboole_0(X9,k5_xboole_0(X10,k3_xboole_0(X10,X11))) = k3_xboole_0(X10,k5_xboole_0(X9,k3_xboole_0(X9,X11)))) ) | (~spl3_5 | ~spl3_7)),
% 0.21/0.48    inference(superposition,[],[f66,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) ) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl3_5 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2))) ) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl3_7 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) != k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl3_6 <=> k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl3_7 | ~spl3_1 | ~spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f45,f42,f21,f65])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    spl3_1 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2))) ) | (~spl3_1 | ~spl3_5)),
% 0.21/0.48    inference(superposition,[],[f43,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f21])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ~spl3_6 | ~spl3_2 | spl3_4 | ~spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f56,f42,f37,f25,f60])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    spl3_2 <=> ! [X1,X0] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    spl3_4 <=> k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) != k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | (~spl3_2 | spl3_4 | ~spl3_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f51,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))) ) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f25])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) != k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) | (spl3_4 | ~spl3_5)),
% 0.21/0.48    inference(superposition,[],[f39,f43])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) | spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f37])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f42])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f14,f12,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ~spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f37])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))),
% 0.21/0.48    inference(forward_demodulation,[],[f18,f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1))) != k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))),
% 0.21/0.48    inference(backward_demodulation,[],[f15,f11])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1))) != k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),
% 0.21/0.48    inference(definition_unfolding,[],[f10,f12,f12])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1) => k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f25])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f13,f12,f12])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f11,f21])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (6191)------------------------------
% 0.21/0.48  % (6191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (6191)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (6191)Memory used [KB]: 6140
% 0.21/0.48  % (6191)Time elapsed: 0.054 s
% 0.21/0.48  % (6191)------------------------------
% 0.21/0.48  % (6191)------------------------------
% 0.21/0.48  % (6173)Success in time 0.123 s
%------------------------------------------------------------------------------
