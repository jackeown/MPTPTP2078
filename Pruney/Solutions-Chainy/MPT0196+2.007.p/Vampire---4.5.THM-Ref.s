%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  46 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  57 expanded)
%              Number of equality atoms :   25 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f71,f105])).

fof(f105,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f69,f25])).

fof(f25,plain,(
    ! [X10,X8,X11,X9] : k3_enumset1(X10,X10,X9,X8,X11) = k3_enumset1(X8,X8,X10,X11,X9) ),
    inference(superposition,[],[f17,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X2,X2,X1,X0,X3) ),
    inference(definition_unfolding,[],[f11,f14,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l129_enumset1)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X3,X1) ),
    inference(definition_unfolding,[],[f12,f14,f14])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(f69,plain,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK2,sK2,sK0,sK3,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_4
  <=> k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK2,sK2,sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f71,plain,
    ( ~ spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f61,f20,f67])).

fof(f20,plain,
    ( spl4_1
  <=> k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK2,sK2,sK1,sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f61,plain,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK2,sK2,sK0,sK3,sK1)
    | spl4_1 ),
    inference(superposition,[],[f22,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f13,f14,f14])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(f22,plain,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK2,sK2,sK1,sK3,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f23,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f15,f20])).

fof(f15,plain,(
    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK2,sK2,sK1,sK3,sK0) ),
    inference(definition_unfolding,[],[f10,f14,f14])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (18351)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (18349)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (18349)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f23,f71,f105])).
% 0.20/0.46  fof(f105,plain,(
% 0.20/0.46    spl4_4),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f72])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    $false | spl4_4),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f69,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X10,X8,X11,X9] : (k3_enumset1(X10,X10,X9,X8,X11) = k3_enumset1(X8,X8,X10,X11,X9)) )),
% 0.20/0.46    inference(superposition,[],[f17,f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X2,X2,X1,X0,X3)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f11,f14,f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l129_enumset1)).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X3,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f12,f14,f14])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK2,sK2,sK0,sK3,sK1) | spl4_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f67])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    spl4_4 <=> k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK2,sK2,sK0,sK3,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    ~spl4_4 | spl4_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f61,f20,f67])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    spl4_1 <=> k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK2,sK2,sK1,sK3,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK2,sK2,sK0,sK3,sK1) | spl4_1),
% 0.20/0.46    inference(superposition,[],[f22,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X3,X2,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f13,f14,f14])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK2,sK2,sK1,sK3,sK0) | spl4_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f20])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ~spl4_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f15,f20])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK2,sK2,sK1,sK3,sK0)),
% 0.20/0.46    inference(definition_unfolding,[],[f10,f14,f14])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0)),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0)),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)),
% 0.20/0.46    inference(negated_conjecture,[],[f5])).
% 0.20/0.46  fof(f5,conjecture,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (18349)------------------------------
% 0.20/0.46  % (18349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (18349)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (18349)Memory used [KB]: 6140
% 0.20/0.46  % (18349)Time elapsed: 0.060 s
% 0.20/0.46  % (18349)------------------------------
% 0.20/0.46  % (18349)------------------------------
% 0.20/0.47  % (18350)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (18357)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (18342)Success in time 0.115 s
%------------------------------------------------------------------------------
