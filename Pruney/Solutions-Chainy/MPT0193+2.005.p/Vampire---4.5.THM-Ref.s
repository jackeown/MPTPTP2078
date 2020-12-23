%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  95 expanded)
%              Number of leaves         :   11 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 ( 112 expanded)
%              Number of equality atoms :   32 (  90 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f33,f37,f57])).

fof(f57,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f28,f47])).

fof(f47,plain,
    ( ! [X10,X8,X11,X9] : k6_enumset1(X10,X10,X10,X10,X10,X8,X9,X11) = k6_enumset1(X9,X9,X9,X9,X9,X10,X11,X8)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(superposition,[],[f36,f32])).

fof(f32,plain,
    ( ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X0,X3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl4_2
  <=> ! [X1,X3,X0,X2] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f36,plain,
    ( ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl4_3
  <=> ! [X1,X3,X0,X2] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f28,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK3,sK0,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl4_1
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f37,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f24,f35])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X0) ),
    inference(definition_unfolding,[],[f14,f21,f21])).

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

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f17,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).

fof(f33,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f23,f31])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X0,X3) ),
    inference(definition_unfolding,[],[f13,f21,f21])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).

fof(f29,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f22,f26])).

fof(f22,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK3,sK0,sK2) ),
    inference(definition_unfolding,[],[f12,f21,f21])).

fof(f12,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.41  % (12119)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.42  % (12119)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f60,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f29,f33,f37,f57])).
% 0.22/0.42  fof(f57,plain,(
% 0.22/0.42    spl4_1 | ~spl4_2 | ~spl4_3),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f56])).
% 0.22/0.42  fof(f56,plain,(
% 0.22/0.42    $false | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.22/0.42    inference(subsumption_resolution,[],[f28,f47])).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    ( ! [X10,X8,X11,X9] : (k6_enumset1(X10,X10,X10,X10,X10,X8,X9,X11) = k6_enumset1(X9,X9,X9,X9,X9,X10,X11,X8)) ) | (~spl4_2 | ~spl4_3)),
% 0.22/0.42    inference(superposition,[],[f36,f32])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X0,X3)) ) | ~spl4_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f31])).
% 0.22/0.42  fof(f31,plain,(
% 0.22/0.42    spl4_2 <=> ! [X1,X3,X0,X2] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X0,X3)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X0)) ) | ~spl4_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f35])).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    spl4_3 <=> ! [X1,X3,X0,X2] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK3,sK0,sK2) | spl4_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f26])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    spl4_1 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK3,sK0,sK2)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    spl4_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f24,f35])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X0)) )),
% 0.22/0.42    inference(definition_unfolding,[],[f14,f21,f21])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.42    inference(definition_unfolding,[],[f15,f20])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.42    inference(definition_unfolding,[],[f16,f19])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.42    inference(definition_unfolding,[],[f17,f18])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).
% 0.22/0.42  fof(f33,plain,(
% 0.22/0.42    spl4_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f23,f31])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X0,X3)) )),
% 0.22/0.42    inference(definition_unfolding,[],[f13,f21,f21])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    ~spl4_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f22,f26])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK3,sK0,sK2)),
% 0.22/0.42    inference(definition_unfolding,[],[f12,f21,f21])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2)),
% 0.22/0.42    inference(ennf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.22/0.42    inference(negated_conjecture,[],[f7])).
% 0.22/0.42  fof(f7,conjecture,(
% 0.22/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (12119)------------------------------
% 0.22/0.42  % (12119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (12119)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (12119)Memory used [KB]: 6140
% 0.22/0.42  % (12119)Time elapsed: 0.005 s
% 0.22/0.42  % (12119)------------------------------
% 0.22/0.42  % (12119)------------------------------
% 0.22/0.42  % (12111)Success in time 0.063 s
%------------------------------------------------------------------------------
