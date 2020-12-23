%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  85 expanded)
%              Number of leaves         :    8 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 151 expanded)
%              Number of equality atoms :   44 (  72 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f52,f68])).

fof(f68,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | spl1_2 ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,
    ( sK0 != sK0
    | spl1_2 ),
    inference(superposition,[],[f31,f63])).

fof(f63,plain,(
    ! [X0] : u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0 ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
      | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1 ) ),
    inference(superposition,[],[f37,f35])).

fof(f35,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) ),
    inference(global_subsumption,[],[f22,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))
      | g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) ) ),
    inference(resolution,[],[f18,f23])).

fof(f23,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f15,f14])).

fof(f14,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f15,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f22,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f16,f14])).

fof(f16,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X4,X5,X3] :
      ( g1_orders_2(u1_struct_0(g1_orders_2(X3,k1_yellow_1(X3))),u1_orders_2(g1_orders_2(X3,k1_yellow_1(X3)))) != g1_orders_2(X4,X5)
      | u1_struct_0(g1_orders_2(X3,k1_yellow_1(X3))) = X4 ) ),
    inference(resolution,[],[f33,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f33,plain,(
    ! [X0] : m1_subset_1(u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))))) ),
    inference(resolution,[],[f17,f22])).

fof(f17,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f31,plain,
    ( sK0 != u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl1_2
  <=> sK0 = u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f52,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | spl1_1 ),
    inference(trivial_inequality_removal,[],[f50])).

fof(f50,plain,
    ( k1_yellow_1(sK0) != k1_yellow_1(sK0)
    | spl1_1 ),
    inference(superposition,[],[f27,f42])).

fof(f42,plain,(
    ! [X0] : k1_yellow_1(X0) = u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
      | u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = X2 ) ),
    inference(superposition,[],[f36,f35])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) != g1_orders_2(X1,X2)
      | u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = X2 ) ),
    inference(resolution,[],[f33,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,
    ( k1_yellow_1(sK0) != u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl1_1
  <=> k1_yellow_1(sK0) = u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

% (5487)Refutation not found, incomplete strategy% (5487)------------------------------
% (5487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f32,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f21,f29,f25])).

% (5487)Termination reason: Refutation not found, incomplete strategy

% (5487)Memory used [KB]: 6140
fof(f21,plain,
    ( sK0 != u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | k1_yellow_1(sK0) != u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(definition_unfolding,[],[f13,f14,f14])).

% (5487)Time elapsed: 0.119 s
% (5487)------------------------------
% (5487)------------------------------
fof(f13,plain,
    ( sK0 != u1_struct_0(k2_yellow_1(sK0))
    | k1_yellow_1(sK0) != u1_orders_2(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k1_yellow_1(X0) != u1_orders_2(k2_yellow_1(X0))
      | u1_struct_0(k2_yellow_1(X0)) != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0))
        & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0))
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:35:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.50  % (5498)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.50  % (5475)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (5482)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (5496)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (5482)Refutation not found, incomplete strategy% (5482)------------------------------
% 0.21/0.51  % (5482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5482)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5482)Memory used [KB]: 10618
% 0.21/0.51  % (5482)Time elapsed: 0.103 s
% 0.21/0.51  % (5482)------------------------------
% 0.21/0.51  % (5482)------------------------------
% 0.21/0.51  % (5473)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (5476)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (5488)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (5472)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (5490)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (5472)Refutation not found, incomplete strategy% (5472)------------------------------
% 0.21/0.51  % (5472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5472)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5472)Memory used [KB]: 1663
% 0.21/0.51  % (5472)Time elapsed: 0.118 s
% 0.21/0.51  % (5472)------------------------------
% 0.21/0.51  % (5472)------------------------------
% 0.21/0.51  % (5498)Refutation not found, incomplete strategy% (5498)------------------------------
% 0.21/0.51  % (5498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5487)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (5498)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5498)Memory used [KB]: 10618
% 0.21/0.51  % (5498)Time elapsed: 0.113 s
% 0.21/0.51  % (5498)------------------------------
% 0.21/0.51  % (5498)------------------------------
% 0.21/0.51  % (5488)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f32,f52,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl1_2),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    $false | spl1_2),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    sK0 != sK0 | spl1_2),
% 0.21/0.51    inference(superposition,[],[f31,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0] : (u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0) )),
% 0.21/0.51    inference(equality_resolution,[],[f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2) | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1) )),
% 0.21/0.51    inference(superposition,[],[f37,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0] : (g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))))) )),
% 0.21/0.51    inference(global_subsumption,[],[f22,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) | g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))))) )),
% 0.21/0.51    inference(resolution,[],[f18,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X0] : (v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f15,f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ( ! [X0] : (k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ( ! [X0] : (v1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_orders_2(X0) | ~l1_orders_2(X0) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : ((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0)) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => (v1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X0] : (l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f16,f14])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (g1_orders_2(u1_struct_0(g1_orders_2(X3,k1_yellow_1(X3))),u1_orders_2(g1_orders_2(X3,k1_yellow_1(X3)))) != g1_orders_2(X4,X5) | u1_struct_0(g1_orders_2(X3,k1_yellow_1(X3))) = X4) )),
% 0.21/0.51    inference(resolution,[],[f33,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))))) )),
% 0.21/0.51    inference(resolution,[],[f17,f22])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    sK0 != u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | spl1_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    spl1_2 <=> sK0 = u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    spl1_1),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    $false | spl1_1),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    k1_yellow_1(sK0) != k1_yellow_1(sK0) | spl1_1),
% 0.21/0.51    inference(superposition,[],[f27,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0] : (k1_yellow_1(X0) = u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 0.21/0.51    inference(equality_resolution,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2) | u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = X2) )),
% 0.21/0.51    inference(superposition,[],[f36,f35])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) != g1_orders_2(X1,X2) | u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = X2) )),
% 0.21/0.51    inference(resolution,[],[f33,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    k1_yellow_1(sK0) != u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | spl1_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    spl1_1 <=> k1_yellow_1(sK0) = u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.51  % (5487)Refutation not found, incomplete strategy% (5487)------------------------------
% 0.21/0.51  % (5487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ~spl1_1 | ~spl1_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f21,f29,f25])).
% 0.21/0.51  % (5487)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5487)Memory used [KB]: 6140
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    sK0 != u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | k1_yellow_1(sK0) != u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 0.21/0.51    inference(definition_unfolding,[],[f13,f14,f14])).
% 0.21/0.51  % (5487)Time elapsed: 0.119 s
% 0.21/0.51  % (5487)------------------------------
% 0.21/0.51  % (5487)------------------------------
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    sK0 != u1_struct_0(k2_yellow_1(sK0)) | k1_yellow_1(sK0) != u1_orders_2(k2_yellow_1(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0] : (k1_yellow_1(X0) != u1_orders_2(k2_yellow_1(X0)) | u1_struct_0(k2_yellow_1(X0)) != X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0)) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.51    inference(negated_conjecture,[],[f6])).
% 0.21/0.51  fof(f6,conjecture,(
% 0.21/0.51    ! [X0] : (k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0)) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (5488)------------------------------
% 0.21/0.51  % (5488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5488)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (5488)Memory used [KB]: 10746
% 0.21/0.51  % (5488)Time elapsed: 0.122 s
% 0.21/0.51  % (5488)------------------------------
% 0.21/0.51  % (5488)------------------------------
% 0.21/0.52  % (5471)Success in time 0.164 s
%------------------------------------------------------------------------------
