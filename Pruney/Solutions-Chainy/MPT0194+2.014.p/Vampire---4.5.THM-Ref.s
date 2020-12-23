%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 277 expanded)
%              Number of leaves         :   10 (  97 expanded)
%              Depth                    :   10
%              Number of atoms          :   49 ( 293 expanded)
%              Number of equality atoms :   33 ( 271 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f47,f91,f93])).

fof(f93,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f83,f35])).

fof(f35,plain,(
    ! [X14,X12,X15,X13] : k6_enumset1(X13,X13,X13,X13,X13,X14,X15,X12) = k6_enumset1(X13,X13,X13,X13,X13,X15,X12,X14) ),
    inference(superposition,[],[f24,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X0) ),
    inference(definition_unfolding,[],[f13,f21,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f15,f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f16,f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f6])).

% (16815)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f17,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_enumset1)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X3,X0,X2) ),
    inference(definition_unfolding,[],[f14,f21,f21])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).

fof(f83,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK3,sK1)
    | spl4_1 ),
    inference(superposition,[],[f28,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X1,X1,X1,X1,X1,X3,X0,X2) = k6_enumset1(X2,X2,X2,X2,X2,X0,X3,X1) ),
    inference(superposition,[],[f24,f24])).

fof(f28,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK3,sK2,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl4_1
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK3,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f91,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f76,f35])).

fof(f76,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK3,sK1)
    | spl4_1 ),
    inference(superposition,[],[f28,f33])).

fof(f47,plain,
    ( ~ spl4_2
    | spl4_1 ),
    inference(avatar_split_clause,[],[f32,f26,f44])).

fof(f44,plain,
    ( spl4_2
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f32,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK3,sK2)
    | spl4_1 ),
    inference(superposition,[],[f28,f23])).

fof(f29,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f22,f26])).

fof(f22,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK3,sK2,sK0) ),
    inference(definition_unfolding,[],[f12,f21,f21])).

fof(f12,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:34:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.40  % (16809)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.44  % (16805)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.45  % (16801)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.46  % (16809)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f94,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(avatar_sat_refutation,[],[f29,f47,f91,f93])).
% 0.19/0.46  fof(f93,plain,(
% 0.19/0.46    spl4_1),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f92])).
% 0.19/0.46  fof(f92,plain,(
% 0.19/0.46    $false | spl4_1),
% 0.19/0.46    inference(subsumption_resolution,[],[f83,f35])).
% 0.19/0.46  fof(f35,plain,(
% 0.19/0.46    ( ! [X14,X12,X15,X13] : (k6_enumset1(X13,X13,X13,X13,X13,X14,X15,X12) = k6_enumset1(X13,X13,X13,X13,X13,X15,X12,X14)) )),
% 0.19/0.46    inference(superposition,[],[f24,f23])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X0)) )),
% 0.19/0.46    inference(definition_unfolding,[],[f13,f21,f21])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.19/0.46    inference(definition_unfolding,[],[f15,f20])).
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.19/0.46    inference(definition_unfolding,[],[f16,f19])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.46    inference(definition_unfolding,[],[f17,f18])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f6])).
% 0.19/0.46  % (16815)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.46  fof(f6,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_enumset1)).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X3,X0,X2)) )),
% 0.19/0.46    inference(definition_unfolding,[],[f14,f21,f21])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).
% 0.19/0.46  fof(f83,plain,(
% 0.19/0.46    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK3,sK1) | spl4_1),
% 0.19/0.46    inference(superposition,[],[f28,f33])).
% 0.19/0.46  fof(f33,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X3,X0,X2) = k6_enumset1(X2,X2,X2,X2,X2,X0,X3,X1)) )),
% 0.19/0.46    inference(superposition,[],[f24,f24])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK3,sK2,sK0) | spl4_1),
% 0.19/0.46    inference(avatar_component_clause,[],[f26])).
% 0.19/0.46  fof(f26,plain,(
% 0.19/0.46    spl4_1 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK3,sK2,sK0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.46  fof(f91,plain,(
% 0.19/0.46    spl4_1),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f90])).
% 0.19/0.46  fof(f90,plain,(
% 0.19/0.46    $false | spl4_1),
% 0.19/0.46    inference(subsumption_resolution,[],[f76,f35])).
% 0.19/0.46  fof(f76,plain,(
% 0.19/0.46    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK3,sK1) | spl4_1),
% 0.19/0.46    inference(superposition,[],[f28,f33])).
% 0.19/0.46  fof(f47,plain,(
% 0.19/0.46    ~spl4_2 | spl4_1),
% 0.19/0.46    inference(avatar_split_clause,[],[f32,f26,f44])).
% 0.19/0.46  fof(f44,plain,(
% 0.19/0.46    spl4_2 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK3,sK2)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK3,sK2) | spl4_1),
% 0.19/0.46    inference(superposition,[],[f28,f23])).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    ~spl4_1),
% 0.19/0.46    inference(avatar_split_clause,[],[f22,f26])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK3,sK2,sK0)),
% 0.19/0.46    inference(definition_unfolding,[],[f12,f21,f21])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f11])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).
% 0.19/0.46  fof(f10,plain,(
% 0.19/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f9,plain,(
% 0.19/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0)),
% 0.19/0.46    inference(ennf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,negated_conjecture,(
% 0.19/0.46    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.19/0.46    inference(negated_conjecture,[],[f7])).
% 0.19/0.46  fof(f7,conjecture,(
% 0.19/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (16809)------------------------------
% 0.19/0.46  % (16809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (16809)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (16809)Memory used [KB]: 6140
% 0.19/0.46  % (16809)Time elapsed: 0.061 s
% 0.19/0.46  % (16809)------------------------------
% 0.19/0.46  % (16809)------------------------------
% 0.19/0.46  % (16813)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.47  % (16800)Success in time 0.116 s
%------------------------------------------------------------------------------
