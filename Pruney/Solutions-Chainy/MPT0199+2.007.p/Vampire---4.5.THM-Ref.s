%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  60 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  70 expanded)
%              Number of equality atoms :   24 (  55 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f58,f60])).

fof(f60,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f52,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X3,X1) ),
    inference(definition_unfolding,[],[f11,f14,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(f52,plain,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK2,sK3,sK1)
    | spl4_1 ),
    inference(superposition,[],[f22,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X2,X2,X3,X1,X0) ),
    inference(definition_unfolding,[],[f13,f14,f14])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_enumset1)).

fof(f22,plain,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK3,sK3,sK1,sK2,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl4_1
  <=> k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK3,sK3,sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f58,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f57])).

fof(f57,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f47,f43])).

fof(f43,plain,(
    ! [X10,X8,X11,X9] : k3_enumset1(X8,X8,X11,X10,X9) = k3_enumset1(X11,X11,X10,X8,X9) ),
    inference(superposition,[],[f18,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f12,f14,f14])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(f47,plain,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK2,sK2,sK0,sK1,sK3)
    | spl4_1 ),
    inference(superposition,[],[f22,f18])).

fof(f23,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f15,f20])).

fof(f15,plain,(
    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK3,sK3,sK1,sK2,sK0) ),
    inference(definition_unfolding,[],[f10,f14,f14])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK1,sK2,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X1,X2,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK1,sK2,sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X1,X2,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:46:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (28146)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (28141)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (28146)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f23,f58,f60])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    spl4_1),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f59])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    $false | spl4_1),
% 0.21/0.46    inference(subsumption_resolution,[],[f52,f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X3,X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f11,f14,f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK2,sK3,sK1) | spl4_1),
% 0.21/0.46    inference(superposition,[],[f22,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X2,X2,X3,X1,X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f13,f14,f14])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_enumset1)).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK3,sK3,sK1,sK2,sK0) | spl4_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    spl4_1 <=> k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK3,sK3,sK1,sK2,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    spl4_1),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f57])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    $false | spl4_1),
% 0.21/0.46    inference(subsumption_resolution,[],[f47,f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ( ! [X10,X8,X11,X9] : (k3_enumset1(X8,X8,X11,X10,X9) = k3_enumset1(X11,X11,X10,X8,X9)) )),
% 0.21/0.46    inference(superposition,[],[f18,f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X3,X2,X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f12,f14,f14])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK2,sK2,sK0,sK1,sK3) | spl4_1),
% 0.21/0.46    inference(superposition,[],[f22,f18])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ~spl4_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f15,f20])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK3,sK3,sK1,sK2,sK0)),
% 0.21/0.46    inference(definition_unfolding,[],[f10,f14,f14])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK1,sK2,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK1,sK2,sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X1,X2,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK1,sK2,sK0)),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X1,X2,X0)),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (28146)------------------------------
% 0.21/0.46  % (28146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (28146)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (28146)Memory used [KB]: 6140
% 0.21/0.46  % (28146)Time elapsed: 0.058 s
% 0.21/0.46  % (28146)------------------------------
% 0.21/0.46  % (28146)------------------------------
% 0.21/0.46  % (28151)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (28137)Success in time 0.112 s
%------------------------------------------------------------------------------
