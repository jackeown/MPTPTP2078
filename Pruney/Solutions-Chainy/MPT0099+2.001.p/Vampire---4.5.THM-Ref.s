%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  67 expanded)
%              Number of leaves         :   17 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   99 ( 125 expanded)
%              Number of equality atoms :   43 (  56 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f28,f32,f36,f40,f48,f52,f58,f79,f82])).

fof(f82,plain,
    ( spl1_1
    | ~ spl1_2
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_9 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl1_1
    | ~ spl1_2
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f23,f80])).

fof(f80,plain,
    ( ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2)
    | ~ spl1_2
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f78,f75])).

fof(f75,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl1_2
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f72,f27])).

fof(f27,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl1_2
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f72,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0)
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(superposition,[],[f51,f47])).

fof(f47,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl1_6
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f51,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl1_7
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f78,plain,
    ( ! [X2] : k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl1_9
  <=> ! [X2] : k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f23,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl1_1
  <=> k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f79,plain,
    ( spl1_9
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f63,f56,f34,f77])).

fof(f34,plain,
    ( spl1_4
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f56,plain,
    ( spl1_8
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f63,plain,
    ( ! [X2] : k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(superposition,[],[f57,f35])).

fof(f35,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f57,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f58,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f19,f56])).

fof(f19,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f52,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f18,f50])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f48,plain,
    ( spl1_6
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f41,f38,f30,f46])).

fof(f30,plain,
    ( spl1_3
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f38,plain,
    ( spl1_5
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f41,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(superposition,[],[f39,f31])).

fof(f31,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f39,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f40,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f17,f38])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f36,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f16,f34])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f32,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f15,f30])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f28,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f24,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f13,f21])).

fof(f13,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).

fof(f11,plain,
    ( ? [X0] : k1_xboole_0 != k5_xboole_0(X0,X0)
   => k1_xboole_0 != k5_xboole_0(sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k5_xboole_0(X0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (12866)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (12861)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (12859)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (12861)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f24,f28,f32,f36,f40,f48,f52,f58,f79,f82])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    spl1_1 | ~spl1_2 | ~spl1_6 | ~spl1_7 | ~spl1_9),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f81])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    $false | (spl1_1 | ~spl1_2 | ~spl1_6 | ~spl1_7 | ~spl1_9)),
% 0.21/0.46    inference(subsumption_resolution,[],[f23,f80])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) ) | (~spl1_2 | ~spl1_6 | ~spl1_7 | ~spl1_9)),
% 0.21/0.46    inference(forward_demodulation,[],[f78,f75])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl1_2 | ~spl1_6 | ~spl1_7)),
% 0.21/0.46    inference(forward_demodulation,[],[f72,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl1_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    spl1_2 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0)) ) | (~spl1_6 | ~spl1_7)),
% 0.21/0.46    inference(superposition,[],[f51,f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl1_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    spl1_6 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) ) | ~spl1_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    spl1_7 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ( ! [X2] : (k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)) ) | ~spl1_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f77])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    spl1_9 <=> ! [X2] : k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    k1_xboole_0 != k5_xboole_0(sK0,sK0) | spl1_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    spl1_1 <=> k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    spl1_9 | ~spl1_4 | ~spl1_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f63,f56,f34,f77])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    spl1_4 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    spl1_8 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X2] : (k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)) ) | (~spl1_4 | ~spl1_8)),
% 0.21/0.46    inference(superposition,[],[f57,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl1_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f34])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ) | ~spl1_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f56])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    spl1_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f19,f56])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    spl1_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f18,f50])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    spl1_6 | ~spl1_3 | ~spl1_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f41,f38,f30,f46])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    spl1_3 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    spl1_5 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl1_3 | ~spl1_5)),
% 0.21/0.46    inference(superposition,[],[f39,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl1_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f30])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl1_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f38])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    spl1_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f17,f38])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    spl1_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f16,f34])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.46    inference(rectify,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    spl1_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f15,f30])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    spl1_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f14,f26])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ~spl1_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f13,f21])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    k1_xboole_0 != k5_xboole_0(sK0,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    k1_xboole_0 != k5_xboole_0(sK0,sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ? [X0] : k1_xboole_0 != k5_xboole_0(X0,X0) => k1_xboole_0 != k5_xboole_0(sK0,sK0)),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0] : k1_xboole_0 != k5_xboole_0(X0,X0)),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,negated_conjecture,(
% 0.21/0.46    ~! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.46    inference(negated_conjecture,[],[f7])).
% 0.21/0.46  fof(f7,conjecture,(
% 0.21/0.46    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (12861)------------------------------
% 0.21/0.46  % (12861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (12861)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (12861)Memory used [KB]: 6140
% 0.21/0.46  % (12861)Time elapsed: 0.043 s
% 0.21/0.46  % (12861)------------------------------
% 0.21/0.46  % (12861)------------------------------
% 0.21/0.46  % (12854)Success in time 0.106 s
%------------------------------------------------------------------------------
