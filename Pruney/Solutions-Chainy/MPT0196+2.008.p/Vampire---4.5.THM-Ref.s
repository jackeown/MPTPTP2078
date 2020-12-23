%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  94 expanded)
%              Number of leaves         :   10 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 ( 105 expanded)
%              Number of equality atoms :   31 (  90 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f203,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f70,f202])).

fof(f202,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f69,f45])).

fof(f45,plain,(
    ! [X19,X17,X18,X16] : k6_enumset1(X16,X16,X16,X16,X16,X17,X19,X18) = k6_enumset1(X17,X17,X17,X17,X17,X18,X16,X19) ),
    inference(superposition,[],[f24,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X3,X2) ),
    inference(definition_unfolding,[],[f13,f20,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f16,f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f17,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X0,X3) ),
    inference(definition_unfolding,[],[f15,f20,f20])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_enumset1)).

fof(f69,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK3,sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_3
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f70,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f36,f26,f67])).

fof(f26,plain,
    ( spl4_1
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK1,sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f36,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK3,sK1)
    | spl4_1 ),
    inference(superposition,[],[f28,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f14,f20,f20])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(f28,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK1,sK3,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f29,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f21,f26])).

fof(f21,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK1,sK3,sK0) ),
    inference(definition_unfolding,[],[f12,f20,f20])).

fof(f12,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:33:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.42  % (20533)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.43  % (20533)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f203,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f29,f70,f202])).
% 0.20/0.43  fof(f202,plain,(
% 0.20/0.43    spl4_3),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f153])).
% 0.20/0.43  fof(f153,plain,(
% 0.20/0.43    $false | spl4_3),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f69,f45])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    ( ! [X19,X17,X18,X16] : (k6_enumset1(X16,X16,X16,X16,X16,X17,X19,X18) = k6_enumset1(X17,X17,X17,X17,X17,X18,X16,X19)) )),
% 0.20/0.43    inference(superposition,[],[f24,f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X3,X2)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f13,f20,f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f16,f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f17,f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X0,X3)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f15,f20,f20])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_enumset1)).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK3,sK1) | spl4_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f67])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    spl4_3 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK3,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    ~spl4_3 | spl4_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f36,f26,f67])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    spl4_1 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK1,sK3,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK3,sK1) | spl4_1),
% 0.20/0.43    inference(superposition,[],[f28,f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X3,X2,X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f14,f20,f20])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK1,sK3,sK0) | spl4_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f26])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ~spl4_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f21,f26])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK1,sK3,sK0)),
% 0.20/0.43    inference(definition_unfolding,[],[f12,f20,f20])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0)),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0)),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)),
% 0.20/0.43    inference(negated_conjecture,[],[f7])).
% 0.20/0.43  fof(f7,conjecture,(
% 0.20/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (20533)------------------------------
% 0.20/0.43  % (20533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (20533)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (20533)Memory used [KB]: 10746
% 0.20/0.43  % (20533)Time elapsed: 0.011 s
% 0.20/0.43  % (20533)------------------------------
% 0.20/0.43  % (20533)------------------------------
% 0.20/0.43  % (20515)Success in time 0.074 s
%------------------------------------------------------------------------------
