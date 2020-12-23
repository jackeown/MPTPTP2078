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
% DateTime   : Thu Dec  3 12:34:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   18 (  19 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f15,f58])).

fof(f58,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f57])).

fof(f57,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f48,f31])).

fof(f31,plain,(
    ! [X14,X12,X15,X13] : k2_enumset1(X13,X14,X12,X15) = k2_enumset1(X12,X13,X15,X14) ),
    inference(superposition,[],[f9,f8])).

fof(f8,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).

fof(f9,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

fof(f48,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK0,sK3,sK1)
    | spl4_1 ),
    inference(superposition,[],[f14,f10])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(f14,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f12])).

fof(f12,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f15,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f7,f12])).

fof(f7,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:28:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (13546)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (13541)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.43  % (13541)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f15,f58])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    spl4_1),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f57])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    $false | spl4_1),
% 0.22/0.43    inference(subsumption_resolution,[],[f48,f31])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ( ! [X14,X12,X15,X13] : (k2_enumset1(X13,X14,X12,X15) = k2_enumset1(X12,X13,X15,X14)) )),
% 0.22/0.43    inference(superposition,[],[f9,f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK0,sK3,sK1) | spl4_1),
% 0.22/0.43    inference(superposition,[],[f14,f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) | spl4_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK1,sK0,sK3)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ~spl4_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f7,f12])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)),
% 0.22/0.43    inference(cnf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3)),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 0.22/0.43    inference(negated_conjecture,[],[f4])).
% 0.22/0.43  fof(f4,conjecture,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_enumset1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (13541)------------------------------
% 0.22/0.43  % (13541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (13541)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (13541)Memory used [KB]: 10618
% 0.22/0.43  % (13541)Time elapsed: 0.006 s
% 0.22/0.43  % (13541)------------------------------
% 0.22/0.43  % (13541)------------------------------
% 0.22/0.43  % (13545)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (13539)Success in time 0.073 s
%------------------------------------------------------------------------------
