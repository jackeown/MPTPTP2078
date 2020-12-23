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
% DateTime   : Thu Dec  3 12:34:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   67 (  83 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f65,f106,f119,f131,f211,f221])).

fof(f221,plain,
    ( spl9_1
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_26 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | spl9_1
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f40,f219])).

fof(f219,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X8,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k6_enumset1(X8,X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f214,f130])).

fof(f130,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl9_17
  <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f214,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = k2_xboole_0(k6_enumset1(X8,X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))
    | ~ spl9_16
    | ~ spl9_26 ),
    inference(superposition,[],[f210,f118])).

fof(f118,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl9_16
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f210,plain,
    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : k2_xboole_0(k1_tarski(X9),k2_xboole_0(k5_enumset1(X10,X11,X12,X13,X14,X15,X16),X17)) = k2_xboole_0(k6_enumset1(X9,X10,X11,X12,X13,X14,X15,X16),X17)
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl9_26
  <=> ! [X16,X9,X11,X13,X15,X17,X10,X12,X14] : k2_xboole_0(k1_tarski(X9),k2_xboole_0(k5_enumset1(X10,X11,X12,X13,X14,X15,X16),X17)) = k2_xboole_0(k6_enumset1(X9,X10,X11,X12,X13,X14,X15,X16),X17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f40,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl9_1
  <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f211,plain,
    ( spl9_26
    | ~ spl9_7
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f122,f104,f63,f209])).

fof(f63,plain,
    ( spl9_7
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f104,plain,
    ( spl9_15
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f122,plain,
    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : k2_xboole_0(k1_tarski(X9),k2_xboole_0(k5_enumset1(X10,X11,X12,X13,X14,X15,X16),X17)) = k2_xboole_0(k6_enumset1(X9,X10,X11,X12,X13,X14,X15,X16),X17)
    | ~ spl9_7
    | ~ spl9_15 ),
    inference(superposition,[],[f64,f105])).

fof(f105,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f104])).

fof(f64,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f131,plain,(
    spl9_17 ),
    inference(avatar_split_clause,[],[f36,f129])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

fof(f119,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f35,f117])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f106,plain,(
    spl9_15 ),
    inference(avatar_split_clause,[],[f34,f104])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

fof(f65,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f41,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f21,f38])).

fof(f21,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:18:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (20630)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (20628)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (20634)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (20629)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (20633)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (20641)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (20633)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f41,f65,f106,f119,f131,f211,f221])).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    spl9_1 | ~spl9_16 | ~spl9_17 | ~spl9_26),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f220])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    $false | (spl9_1 | ~spl9_16 | ~spl9_17 | ~spl9_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f40,f219])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X8,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k6_enumset1(X8,X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) ) | (~spl9_16 | ~spl9_17 | ~spl9_26)),
% 0.21/0.48    inference(forward_demodulation,[],[f214,f130])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) ) | ~spl9_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f129])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl9_17 <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = k2_xboole_0(k6_enumset1(X8,X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) ) | (~spl9_16 | ~spl9_26)),
% 0.21/0.48    inference(superposition,[],[f210,f118])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) ) | ~spl9_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f117])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    spl9_16 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : (k2_xboole_0(k1_tarski(X9),k2_xboole_0(k5_enumset1(X10,X11,X12,X13,X14,X15,X16),X17)) = k2_xboole_0(k6_enumset1(X9,X10,X11,X12,X13,X14,X15,X16),X17)) ) | ~spl9_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f209])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    spl9_26 <=> ! [X16,X9,X11,X13,X15,X17,X10,X12,X14] : k2_xboole_0(k1_tarski(X9),k2_xboole_0(k5_enumset1(X10,X11,X12,X13,X14,X15,X16),X17)) = k2_xboole_0(k6_enumset1(X9,X10,X11,X12,X13,X14,X15,X16),X17)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) | spl9_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    spl9_1 <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    spl9_26 | ~spl9_7 | ~spl9_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f122,f104,f63,f209])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl9_7 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl9_15 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : (k2_xboole_0(k1_tarski(X9),k2_xboole_0(k5_enumset1(X10,X11,X12,X13,X14,X15,X16),X17)) = k2_xboole_0(k6_enumset1(X9,X10,X11,X12,X13,X14,X15,X16),X17)) ) | (~spl9_7 | ~spl9_15)),
% 0.21/0.48    inference(superposition,[],[f64,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) ) | ~spl9_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl9_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f63])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl9_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f129])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl9_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f117])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl9_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f104])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl9_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f63])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ~spl9_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f38])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f18,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 0.21/0.48    inference(ennf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 0.21/0.48    inference(negated_conjecture,[],[f16])).
% 0.21/0.48  fof(f16,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (20633)------------------------------
% 0.21/0.48  % (20633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (20633)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (20633)Memory used [KB]: 6268
% 0.21/0.48  % (20633)Time elapsed: 0.066 s
% 0.21/0.48  % (20633)------------------------------
% 0.21/0.48  % (20633)------------------------------
% 0.21/0.48  % (20636)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (20642)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (20624)Success in time 0.121 s
%------------------------------------------------------------------------------
