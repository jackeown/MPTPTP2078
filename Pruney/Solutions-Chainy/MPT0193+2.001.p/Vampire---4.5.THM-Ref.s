%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 (  62 expanded)
%              Number of leaves         :    9 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  82 expanded)
%              Number of equality atoms :   27 (  57 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f31,f47])).

fof(f47,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f46])).

fof(f46,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f45])).

fof(f45,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f42,f21])).

fof(f21,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl4_1
  <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f42,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK3,sK3,sK2))
    | spl4_2
    | ~ spl4_3 ),
    inference(superposition,[],[f26,f30])).

fof(f30,plain,
    ( ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X3))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl4_3
  <=> ! [X1,X3,X0,X2] : k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f26,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK1,sK1,sK3),k1_enumset1(sK0,sK0,sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl4_2
  <=> k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK1,sK1,sK3),k1_enumset1(sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f31,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f18,f29])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X3)) ),
    inference(definition_unfolding,[],[f13,f15,f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) ),
    inference(definition_unfolding,[],[f14,f12,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).

fof(f27,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f16,f24])).

fof(f16,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK1,sK1,sK3),k1_enumset1(sK0,sK0,sK2)) ),
    inference(definition_unfolding,[],[f10,f15,f15])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

fof(f22,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f17,f20])).

fof(f17,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f11,f12,f12])).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:39:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (31992)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.44  % (31999)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.44  % (31999)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f22,f27,f31,f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ~spl4_1 | spl4_2 | ~spl4_3),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    $false | (~spl4_1 | spl4_2 | ~spl4_3)),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) | (~spl4_1 | spl4_2 | ~spl4_3)),
% 0.21/0.44    inference(forward_demodulation,[],[f42,f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) ) | ~spl4_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    spl4_1 <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK3,sK3,sK2)) | (spl4_2 | ~spl4_3)),
% 0.21/0.44    inference(superposition,[],[f26,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X3))) ) | ~spl4_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    spl4_3 <=> ! [X1,X3,X0,X2] : k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X3))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK1,sK1,sK3),k1_enumset1(sK0,sK0,sK2)) | spl4_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    spl4_2 <=> k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK1,sK1,sK3),k1_enumset1(sK0,sK0,sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    spl4_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f18,f29])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k2_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X3))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f13,f15,f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f14,f12,f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ~spl4_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f16,f24])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK1,sK1,sK3),k1_enumset1(sK0,sK0,sK2))),
% 0.21/0.44    inference(definition_unfolding,[],[f10,f15,f15])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2)),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.21/0.44    inference(negated_conjecture,[],[f5])).
% 0.21/0.44  fof(f5,conjecture,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    spl4_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f17,f20])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f11,f12,f12])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (31999)------------------------------
% 0.21/0.44  % (31999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (31999)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (31999)Memory used [KB]: 6140
% 0.21/0.44  % (31999)Time elapsed: 0.030 s
% 0.21/0.44  % (31999)------------------------------
% 0.21/0.44  % (31999)------------------------------
% 0.21/0.45  % (31991)Success in time 0.086 s
%------------------------------------------------------------------------------
