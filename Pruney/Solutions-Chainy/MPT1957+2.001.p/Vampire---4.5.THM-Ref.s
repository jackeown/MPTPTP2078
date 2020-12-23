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
% DateTime   : Thu Dec  3 13:22:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  18 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f17,f22])).

% (16042)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% (16027)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% (16035)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% (16039)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f22,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f18])).

fof(f18,plain,
    ( $false
    | spl1_1 ),
    inference(unit_resulting_resolution,[],[f16,f10])).

fof(f10,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f16,plain,
    ( k9_setfam_1(sK0) != u1_struct_0(k2_yellow_1(k9_setfam_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f14,plain,
    ( spl1_1
  <=> k9_setfam_1(sK0) = u1_struct_0(k2_yellow_1(k9_setfam_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f17,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f12,f14])).

fof(f12,plain,(
    k9_setfam_1(sK0) != u1_struct_0(k2_yellow_1(k9_setfam_1(sK0))) ),
    inference(definition_unfolding,[],[f8,f9])).

fof(f9,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f8,plain,(
    k9_setfam_1(sK0) != u1_struct_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f7])).

% (16040)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f7,plain,(
    k9_setfam_1(sK0) != u1_struct_0(k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).

fof(f6,plain,
    ( ? [X0] : k9_setfam_1(X0) != u1_struct_0(k3_yellow_1(X0))
   => k9_setfam_1(sK0) != u1_struct_0(k3_yellow_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] : k9_setfam_1(X0) != u1_struct_0(k3_yellow_1(X0)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_7)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:46:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (16033)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (16028)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (16033)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f17,f22])).
% 0.22/0.47  % (16042)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (16027)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (16035)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (16039)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    spl1_1),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    $false | spl1_1),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f16,f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    k9_setfam_1(sK0) != u1_struct_0(k2_yellow_1(k9_setfam_1(sK0))) | spl1_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    spl1_1 <=> k9_setfam_1(sK0) = u1_struct_0(k2_yellow_1(k9_setfam_1(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ~spl1_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f12,f14])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    k9_setfam_1(sK0) != u1_struct_0(k2_yellow_1(k9_setfam_1(sK0)))),
% 0.22/0.48    inference(definition_unfolding,[],[f8,f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    k9_setfam_1(sK0) != u1_struct_0(k3_yellow_1(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  % (16040)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    k9_setfam_1(sK0) != u1_struct_0(k3_yellow_1(sK0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ? [X0] : k9_setfam_1(X0) != u1_struct_0(k3_yellow_1(X0)) => k9_setfam_1(sK0) != u1_struct_0(k3_yellow_1(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f5,plain,(
% 0.22/0.48    ? [X0] : k9_setfam_1(X0) != u1_struct_0(k3_yellow_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,negated_conjecture,(
% 0.22/0.48    ~! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))),
% 0.22/0.48    inference(negated_conjecture,[],[f3])).
% 0.22/0.48  fof(f3,conjecture,(
% 0.22/0.48    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_7)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (16033)------------------------------
% 0.22/0.48  % (16033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (16033)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (16033)Memory used [KB]: 6012
% 0.22/0.48  % (16033)Time elapsed: 0.043 s
% 0.22/0.48  % (16033)------------------------------
% 0.22/0.48  % (16033)------------------------------
% 0.22/0.48  % (16034)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (16026)Success in time 0.115 s
%------------------------------------------------------------------------------
