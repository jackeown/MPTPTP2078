%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   76 ( 104 expanded)
%              Number of equality atoms :   33 (  47 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f208,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f49,f53,f65,f73,f83,f199,f207])).

fof(f207,plain,
    ( spl3_1
    | ~ spl3_11
    | ~ spl3_26 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | spl3_1
    | ~ spl3_11
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f40,f203])).

fof(f203,plain,
    ( ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X4,X3,X5)
    | ~ spl3_11
    | ~ spl3_26 ),
    inference(superposition,[],[f198,f82])).

fof(f82,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f198,plain,
    ( ! [X4,X2,X3] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl3_26
  <=> ! [X3,X2,X4] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f40,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f199,plain,
    ( spl3_26
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f106,f81,f47,f197])).

fof(f47,plain,
    ( spl3_3
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f106,plain,
    ( ! [X4,X2,X3] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(superposition,[],[f82,f48])).

fof(f48,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f83,plain,
    ( spl3_11
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f79,f71,f63,f51,f81])).

fof(f51,plain,
    ( spl3_4
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f63,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f71,plain,
    ( spl3_9
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f79,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f78,f64])).

fof(f64,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f78,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(superposition,[],[f72,f52])).

fof(f52,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f72,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f73,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f65,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f41,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f38])).

fof(f21,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:35:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.44  % (7212)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.44  % (7207)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.44  % (7212)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f208,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f41,f49,f53,f65,f73,f83,f199,f207])).
% 0.22/0.44  fof(f207,plain,(
% 0.22/0.44    spl3_1 | ~spl3_11 | ~spl3_26),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f206])).
% 0.22/0.44  fof(f206,plain,(
% 0.22/0.44    $false | (spl3_1 | ~spl3_11 | ~spl3_26)),
% 0.22/0.44    inference(subsumption_resolution,[],[f40,f203])).
% 0.22/0.44  fof(f203,plain,(
% 0.22/0.44    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k1_enumset1(X4,X3,X5)) ) | (~spl3_11 | ~spl3_26)),
% 0.22/0.44    inference(superposition,[],[f198,f82])).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) ) | ~spl3_11),
% 0.22/0.44    inference(avatar_component_clause,[],[f81])).
% 0.22/0.44  fof(f81,plain,(
% 0.22/0.44    spl3_11 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.44  fof(f198,plain,(
% 0.22/0.44    ( ! [X4,X2,X3] : (k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))) ) | ~spl3_26),
% 0.22/0.44    inference(avatar_component_clause,[],[f197])).
% 0.22/0.44  fof(f197,plain,(
% 0.22/0.44    spl3_26 <=> ! [X3,X2,X4] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) | spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f38])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK1,sK0,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f199,plain,(
% 0.22/0.44    spl3_26 | ~spl3_3 | ~spl3_11),
% 0.22/0.44    inference(avatar_split_clause,[],[f106,f81,f47,f197])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    spl3_3 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.44  fof(f106,plain,(
% 0.22/0.44    ( ! [X4,X2,X3] : (k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))) ) | (~spl3_3 | ~spl3_11)),
% 0.22/0.44    inference(superposition,[],[f82,f48])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl3_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f47])).
% 0.22/0.44  fof(f83,plain,(
% 0.22/0.44    spl3_11 | ~spl3_4 | ~spl3_7 | ~spl3_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f79,f71,f63,f51,f81])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    spl3_4 <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    spl3_7 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    spl3_9 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) ) | (~spl3_4 | ~spl3_7 | ~spl3_9)),
% 0.22/0.44    inference(forward_demodulation,[],[f78,f64])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) ) | ~spl3_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f63])).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) ) | (~spl3_4 | ~spl3_9)),
% 0.22/0.44    inference(superposition,[],[f72,f52])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) ) | ~spl3_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f51])).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) ) | ~spl3_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f71])).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    spl3_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f29,f71])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f27,f63])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f24,f51])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f23,f47])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    ~spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f38])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)),
% 0.22/0.44    inference(ennf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 0.22/0.44    inference(negated_conjecture,[],[f16])).
% 0.22/0.44  fof(f16,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (7212)------------------------------
% 0.22/0.44  % (7212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (7212)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (7212)Memory used [KB]: 6268
% 0.22/0.44  % (7212)Time elapsed: 0.005 s
% 0.22/0.44  % (7212)------------------------------
% 0.22/0.44  % (7212)------------------------------
% 0.22/0.44  % (7206)Success in time 0.076 s
%------------------------------------------------------------------------------
