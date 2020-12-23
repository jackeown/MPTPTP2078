%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  45 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 (  79 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f17,f21,f25,f29,f35,f41,f46])).

fof(f46,plain,
    ( ~ spl1_2
    | spl1_6 ),
    inference(avatar_contradiction_clause,[],[f42])).

fof(f42,plain,
    ( $false
    | ~ spl1_2
    | spl1_6 ),
    inference(unit_resulting_resolution,[],[f20,f40])).

fof(f40,plain,
    ( k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0)
    | spl1_6 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl1_6
  <=> k1_tarski(sK0) = k1_enumset1(sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f20,plain,
    ( ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl1_2
  <=> ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f41,plain,
    ( ~ spl1_6
    | ~ spl1_3
    | spl1_5 ),
    inference(avatar_split_clause,[],[f36,f32,f23,f38])).

fof(f23,plain,
    ( spl1_3
  <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f32,plain,
    ( spl1_5
  <=> k1_tarski(sK0) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f36,plain,
    ( k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0)
    | ~ spl1_3
    | spl1_5 ),
    inference(superposition,[],[f34,f24])).

fof(f24,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f23])).

fof(f34,plain,
    ( k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f32])).

fof(f35,plain,
    ( ~ spl1_5
    | spl1_1
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f30,f27,f14,f32])).

fof(f14,plain,
    ( spl1_1
  <=> k1_tarski(sK0) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f27,plain,
    ( spl1_4
  <=> ! [X1,X3,X0,X2] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f30,plain,
    ( k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl1_1
    | ~ spl1_4 ),
    inference(superposition,[],[f16,f28])).

fof(f28,plain,
    ( ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f27])).

fof(f16,plain,
    ( k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f29,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f12,f27])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

fof(f25,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f11,f23])).

fof(f11,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f10,f19])).

fof(f10,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

fof(f17,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f9,f14])).

fof(f9,plain,(
    k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).

fof(f7,plain,
    ( ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0)
   => k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (6569)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.44  % (6569)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f17,f21,f25,f29,f35,f41,f46])).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    ~spl1_2 | spl1_6),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f42])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    $false | (~spl1_2 | spl1_6)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f20,f40])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0) | spl1_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f38])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    spl1_6 <=> k1_tarski(sK0) = k1_enumset1(sK0,sK0,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) ) | ~spl1_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    spl1_2 <=> ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ~spl1_6 | ~spl1_3 | spl1_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f36,f32,f23,f38])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    spl1_3 <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    spl1_5 <=> k1_tarski(sK0) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    k1_tarski(sK0) != k1_enumset1(sK0,sK0,sK0) | (~spl1_3 | spl1_5)),
% 0.20/0.44    inference(superposition,[],[f34,f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) ) | ~spl1_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f23])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | spl1_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f32])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ~spl1_5 | spl1_1 | ~spl1_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f30,f27,f14,f32])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    spl1_1 <=> k1_tarski(sK0) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    spl1_4 <=> ! [X1,X3,X0,X2] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | (spl1_1 | ~spl1_4)),
% 0.20/0.44    inference(superposition,[],[f16,f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) ) | ~spl1_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f27])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) | spl1_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f14])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    spl1_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f12,f27])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    spl1_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f11,f23])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    spl1_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f10,f19])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ~spl1_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f9,f14])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).
% 0.20/0.44  fof(f7,plain,(
% 0.20/0.44    ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0) => k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f6,plain,(
% 0.20/0.44    ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0)),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,negated_conjecture,(
% 0.20/0.44    ~! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)),
% 0.20/0.44    inference(negated_conjecture,[],[f4])).
% 0.20/0.44  fof(f4,conjecture,(
% 0.20/0.44    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_enumset1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (6569)------------------------------
% 0.20/0.44  % (6569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (6569)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (6569)Memory used [KB]: 6140
% 0.20/0.44  % (6569)Time elapsed: 0.006 s
% 0.20/0.44  % (6569)------------------------------
% 0.20/0.44  % (6569)------------------------------
% 0.20/0.44  % (6557)Success in time 0.081 s
%------------------------------------------------------------------------------
