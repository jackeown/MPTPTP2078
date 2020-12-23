%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  48 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   64 (  88 expanded)
%              Number of equality atoms :   28 (  40 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f23,f27,f41,f113,f143,f163])).

fof(f163,plain,
    ( spl4_1
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl4_1
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f18,f157])).

fof(f157,plain,
    ( ! [X10,X8,X11,X9] : k2_enumset1(X8,X10,X9,X11) = k2_enumset1(X8,X11,X9,X10)
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(superposition,[],[f142,f112])).

fof(f112,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X3,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X1,X0,X2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_8
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X3,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X1,X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f142,plain,
    ( ! [X14,X12,X15,X13] : k2_enumset1(X15,X12,X13,X14) = k2_xboole_0(k1_tarski(X15),k1_enumset1(X13,X14,X12))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl4_10
  <=> ! [X13,X15,X12,X14] : k2_enumset1(X15,X12,X13,X14) = k2_xboole_0(k1_tarski(X15),k1_enumset1(X13,X14,X12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f18,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f16,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f143,plain,
    ( spl4_10
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f49,f39,f21,f141])).

fof(f21,plain,
    ( spl4_2
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f39,plain,
    ( spl4_4
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f49,plain,
    ( ! [X14,X12,X15,X13] : k2_enumset1(X15,X12,X13,X14) = k2_xboole_0(k1_tarski(X15),k1_enumset1(X13,X14,X12))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f40,f22])).

fof(f22,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f21])).

fof(f40,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f113,plain,
    ( spl4_8
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f46,f39,f25,f111])).

fof(f25,plain,
    ( spl4_3
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f46,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X3,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X1,X0,X2))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(superposition,[],[f40,f26])).

fof(f26,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f41,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f13,f39])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f27,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f12,f25])).

fof(f12,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

fof(f23,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f11,f21])).

fof(f11,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f19,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f10,f16])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X3,X2,X1)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X3,X2,X1) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (4849)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.44  % (4848)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (4844)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (4850)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (4845)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (4849)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f164,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f19,f23,f27,f41,f113,f143,f163])).
% 0.21/0.46  fof(f163,plain,(
% 0.21/0.46    spl4_1 | ~spl4_8 | ~spl4_10),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f162])).
% 0.21/0.46  fof(f162,plain,(
% 0.21/0.46    $false | (spl4_1 | ~spl4_8 | ~spl4_10)),
% 0.21/0.46    inference(subsumption_resolution,[],[f18,f157])).
% 0.21/0.46  fof(f157,plain,(
% 0.21/0.46    ( ! [X10,X8,X11,X9] : (k2_enumset1(X8,X10,X9,X11) = k2_enumset1(X8,X11,X9,X10)) ) | (~spl4_8 | ~spl4_10)),
% 0.21/0.46    inference(superposition,[],[f142,f112])).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X3,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X1,X0,X2))) ) | ~spl4_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f111])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    spl4_8 <=> ! [X1,X3,X0,X2] : k2_enumset1(X3,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X1,X0,X2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.46  fof(f142,plain,(
% 0.21/0.46    ( ! [X14,X12,X15,X13] : (k2_enumset1(X15,X12,X13,X14) = k2_xboole_0(k1_tarski(X15),k1_enumset1(X13,X14,X12))) ) | ~spl4_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f141])).
% 0.21/0.46  fof(f141,plain,(
% 0.21/0.46    spl4_10 <=> ! [X13,X15,X12,X14] : k2_enumset1(X15,X12,X13,X14) = k2_xboole_0(k1_tarski(X15),k1_enumset1(X13,X14,X12))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1) | spl4_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK3,sK2,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.46  fof(f143,plain,(
% 0.21/0.46    spl4_10 | ~spl4_2 | ~spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f49,f39,f21,f141])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    spl4_2 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    spl4_4 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X14,X12,X15,X13] : (k2_enumset1(X15,X12,X13,X14) = k2_xboole_0(k1_tarski(X15),k1_enumset1(X13,X14,X12))) ) | (~spl4_2 | ~spl4_4)),
% 0.21/0.46    inference(superposition,[],[f40,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) ) | ~spl4_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f21])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) ) | ~spl4_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f39])).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    spl4_8 | ~spl4_3 | ~spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f46,f39,f25,f111])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    spl4_3 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X3,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X1,X0,X2))) ) | (~spl4_3 | ~spl4_4)),
% 0.21/0.46    inference(superposition,[],[f40,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)) ) | ~spl4_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f25])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f13,f39])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    spl4_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f12,f25])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    spl4_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f11,f21])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ~spl4_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f10,f16])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X3,X2,X1) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1)),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X3,X2,X1)),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (4849)------------------------------
% 0.21/0.46  % (4849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (4849)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (4849)Memory used [KB]: 6140
% 0.21/0.46  % (4849)Time elapsed: 0.048 s
% 0.21/0.46  % (4849)------------------------------
% 0.21/0.46  % (4849)------------------------------
% 0.21/0.46  % (4843)Success in time 0.111 s
%------------------------------------------------------------------------------
