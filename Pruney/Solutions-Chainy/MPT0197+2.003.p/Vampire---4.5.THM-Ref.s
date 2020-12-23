%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   15 (  16 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f13,f18])).

fof(f18,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f17])).

fof(f17,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f16,f8])).

fof(f8,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(f16,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1)
    | spl4_1 ),
    inference(superposition,[],[f12,f7])).

fof(f7,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).

fof(f12,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f10])).

fof(f10,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f13,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f6,f10])).

fof(f6,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X0,X1) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:51:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.43  % (24581)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.43  % (24581)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f13,f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    spl4_1),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    $false | spl4_1),
% 0.22/0.43    inference(subsumption_resolution,[],[f16,f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1) | spl4_1),
% 0.22/0.43    inference(superposition,[],[f12,f7])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1) | spl4_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK3,sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ~spl4_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f6,f10])).
% 0.22/0.43  fof(f6,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK0,sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X0,X1)),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1)),
% 0.22/0.43    inference(negated_conjecture,[],[f3])).
% 0.22/0.43  fof(f3,conjecture,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X0,X1)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_enumset1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (24581)------------------------------
% 0.22/0.43  % (24581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (24581)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (24581)Memory used [KB]: 10490
% 0.22/0.43  % (24581)Time elapsed: 0.005 s
% 0.22/0.43  % (24581)------------------------------
% 0.22/0.43  % (24581)------------------------------
% 0.22/0.43  % (24580)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.44  % (24579)Success in time 0.067 s
%------------------------------------------------------------------------------
