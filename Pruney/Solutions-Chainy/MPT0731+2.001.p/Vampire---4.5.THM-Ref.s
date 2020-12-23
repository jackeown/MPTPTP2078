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
% DateTime   : Thu Dec  3 12:55:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  17 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  25 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f14,f17])).

fof(f17,plain,(
    ~ spl1_1 ),
    inference(avatar_contradiction_clause,[],[f16])).

fof(f16,plain,
    ( $false
    | ~ spl1_1 ),
    inference(subsumption_resolution,[],[f15,f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f15,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl1_1 ),
    inference(superposition,[],[f8,f13])).

fof(f13,plain,
    ( sK0 = k1_ordinal1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f11])).

fof(f11,plain,
    ( spl1_1
  <=> sK0 = k1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f8,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f14,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f7,f11])).

fof(f7,plain,(
    sK0 = k1_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0] : k1_ordinal1(X0) = X0 ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:52:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (22792)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.43  % (22786)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (22786)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f14,f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ~spl1_1),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    $false | ~spl1_1),
% 0.21/0.43    inference(subsumption_resolution,[],[f15,f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,plain,(
% 0.21/0.43    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    r2_hidden(sK0,sK0) | ~spl1_1),
% 0.21/0.43    inference(superposition,[],[f8,f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    sK0 = k1_ordinal1(sK0) | ~spl1_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    spl1_1 <=> sK0 = k1_ordinal1(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    spl1_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f7,f11])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    sK0 = k1_ordinal1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,plain,(
% 0.21/0.43    ? [X0] : k1_ordinal1(X0) = X0),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,negated_conjecture,(
% 0.21/0.43    ~! [X0] : k1_ordinal1(X0) != X0),
% 0.21/0.43    inference(negated_conjecture,[],[f3])).
% 0.21/0.43  fof(f3,conjecture,(
% 0.21/0.43    ! [X0] : k1_ordinal1(X0) != X0),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (22786)------------------------------
% 0.21/0.43  % (22786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (22786)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (22786)Memory used [KB]: 10490
% 0.21/0.43  % (22786)Time elapsed: 0.004 s
% 0.21/0.43  % (22786)------------------------------
% 0.21/0.43  % (22786)------------------------------
% 0.21/0.43  % (22790)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.44  % (22784)Success in time 0.076 s
%------------------------------------------------------------------------------
