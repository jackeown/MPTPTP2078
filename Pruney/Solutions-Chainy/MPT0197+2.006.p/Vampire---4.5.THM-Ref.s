%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 149 expanded)
%              Number of leaves         :   12 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 ( 166 expanded)
%              Number of equality atoms :   37 ( 144 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f49,f80,f158])).

fof(f158,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f79,f34])).

fof(f34,plain,(
    ! [X10,X8,X11,X9] : k6_enumset1(X8,X8,X8,X8,X8,X9,X11,X10) = k6_enumset1(X8,X8,X8,X8,X8,X10,X11,X9) ),
    inference(superposition,[],[f26,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X3,X2) ),
    inference(definition_unfolding,[],[f14,f23,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f17,f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f18,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X3,X1) ),
    inference(definition_unfolding,[],[f15,f23,f23])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(f79,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK3,sK2,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_4
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f80,plain,
    ( ~ spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f65,f46,f77])).

fof(f46,plain,
    ( spl4_2
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f65,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK3,sK2,sK1)
    | spl4_2 ),
    inference(superposition,[],[f48,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X3,X0,X2) ),
    inference(definition_unfolding,[],[f16,f23,f23])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

fof(f48,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK1,sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f49,plain,
    ( ~ spl4_2
    | spl4_1 ),
    inference(avatar_split_clause,[],[f39,f29,f46])).

fof(f29,plain,
    ( spl4_1
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f39,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK1,sK3)
    | spl4_1 ),
    inference(superposition,[],[f31,f26])).

fof(f31,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f32,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f24,f29])).

fof(f24,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK0,sK1) ),
    inference(definition_unfolding,[],[f13,f23,f23])).

fof(f13,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X0,X1)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X0,X1) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:05:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (31084)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.43  % (31084)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f159,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f32,f49,f80,f158])).
% 0.21/0.44  fof(f158,plain,(
% 0.21/0.44    spl4_4),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f123])).
% 0.21/0.44  fof(f123,plain,(
% 0.21/0.44    $false | spl4_4),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f79,f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X10,X8,X11,X9] : (k6_enumset1(X8,X8,X8,X8,X8,X9,X11,X10) = k6_enumset1(X8,X8,X8,X8,X8,X10,X11,X9)) )),
% 0.21/0.44    inference(superposition,[],[f26,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X3,X2)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f14,f23,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f17,f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f18,f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f19,f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X3,X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f15,f23,f23])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK3,sK2,sK1) | spl4_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f77])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    spl4_4 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK3,sK2,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    ~spl4_4 | spl4_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f65,f46,f77])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    spl4_2 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK1,sK3)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK3,sK2,sK1) | spl4_2),
% 0.21/0.44    inference(superposition,[],[f48,f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X3,X0,X2)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f16,f23,f23])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK1,sK3) | spl4_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f46])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ~spl4_2 | spl4_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f39,f29,f46])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    spl4_1 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK1,sK3) | spl4_1),
% 0.21/0.44    inference(superposition,[],[f31,f26])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK0,sK1) | spl4_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f29])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ~spl4_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f24,f29])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK0,sK1)),
% 0.21/0.44    inference(definition_unfolding,[],[f13,f23,f23])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X0,X1) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1)),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X0,X1)),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1)),
% 0.21/0.44    inference(negated_conjecture,[],[f8])).
% 0.21/0.44  fof(f8,conjecture,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_enumset1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (31084)------------------------------
% 0.21/0.44  % (31084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (31084)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (31084)Memory used [KB]: 6140
% 0.21/0.44  % (31084)Time elapsed: 0.008 s
% 0.21/0.44  % (31084)------------------------------
% 0.21/0.44  % (31084)------------------------------
% 0.21/0.44  % (31077)Success in time 0.078 s
%------------------------------------------------------------------------------
