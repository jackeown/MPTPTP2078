%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 148 expanded)
%              Number of leaves         :   12 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  195 ( 427 expanded)
%              Number of equality atoms :   16 (  21 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f112,f116,f174,f178])).

% (19376)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% (19373)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% (19367)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% (19382)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% (19372)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% (19370)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% (19375)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% (19379)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% (19380)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% (19374)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% (19384)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% (19378)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% (19361)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% (19371)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% (19371)Refutation not found, incomplete strategy% (19371)------------------------------
% (19371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19371)Termination reason: Refutation not found, incomplete strategy

% (19371)Memory used [KB]: 10490
% (19371)Time elapsed: 0.111 s
% (19371)------------------------------
% (19371)------------------------------
% (19368)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% (19368)Refutation not found, incomplete strategy% (19368)------------------------------
% (19368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19368)Termination reason: Refutation not found, incomplete strategy

% (19368)Memory used [KB]: 6012
% (19368)Time elapsed: 0.116 s
% (19368)------------------------------
% (19368)------------------------------
% (19381)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
fof(f178,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f52,f141])).

fof(f141,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f56,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f56,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(resolution,[],[f43,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f43,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f41,f18])).

fof(f18,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
              & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f41,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f17,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f17,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,
    ( ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_2
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f174,plain,
    ( ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f172,f141])).

fof(f172,plain,
    ( ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f171,f107])).

fof(f107,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_5
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f171,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f167,f131])).

fof(f131,plain,
    ( ~ sP2(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f127,f18])).

fof(f127,plain,
    ( ~ sP2(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f111,f31])).

fof(f31,plain,(
    ! [X0] : sQ3_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ sQ3_eqProxy(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ sP2(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_6
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ sP2(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
        | ~ sQ3_eqProxy(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f167,plain,
    ( sP2(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f77,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_pre_topc(X0)
      | sQ3_eqProxy(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) ) ),
    inference(equality_proxy_replacement,[],[f20,f27])).

fof(f20,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f77,plain,(
    ! [X0] :
      ( ~ sQ3_eqProxy(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | sP2(X0,sK0) ) ),
    inference(resolution,[],[f44,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ sQ3_eqProxy(X0,X1)
      | sQ3_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f27])).

fof(f44,plain,(
    ! [X0] :
      ( ~ sQ3_eqProxy(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | sP2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f42,f43])).

fof(f42,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ sQ3_eqProxy(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | sP2(X0,sK0) ) ),
    inference(resolution,[],[f17,f29])).

fof(f29,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X2)
      | ~ sQ3_eqProxy(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ m1_pre_topc(X2,X0)
      | sP2(X3,X0) ) ),
    inference(equality_proxy_replacement,[],[f25,f27])).

fof(f25,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ m1_pre_topc(X2,X0)
      | sP2(X3,X0) ) ),
    inference(cnf_transformation,[],[f25_D])).

fof(f25_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( ~ l1_pre_topc(X2)
          | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
          | ~ m1_pre_topc(X2,X0) )
    <=> ~ sP2(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP2])])).

fof(f116,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f113,f56])).

fof(f113,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl4_5 ),
    inference(resolution,[],[f108,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f108,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f112,plain,
    ( ~ spl4_5
    | spl4_6
    | spl4_1 ),
    inference(avatar_split_clause,[],[f55,f46,f110,f106])).

fof(f46,plain,
    ( spl4_1
  <=> m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ sQ3_eqProxy(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ sP2(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) )
    | spl4_1 ),
    inference(subsumption_resolution,[],[f54,f18])).

fof(f54,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ sQ3_eqProxy(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ sP2(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) )
    | spl4_1 ),
    inference(resolution,[],[f48,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X3)
      | ~ sQ3_eqProxy(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | m1_pre_topc(X3,X1)
      | ~ sP2(X3,X0) ) ),
    inference(equality_proxy_replacement,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X3)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | m1_pre_topc(X3,X1)
      | ~ sP2(X3,X0) ) ),
    inference(general_splitting,[],[f21,f25_D])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X3)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X3,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).

fof(f48,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f53,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f16,f50,f46])).

fof(f16,plain,
    ( ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:36:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (19369)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.47  % (19369)Refutation not found, incomplete strategy% (19369)------------------------------
% 0.22/0.47  % (19369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (19369)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (19369)Memory used [KB]: 10490
% 0.22/0.47  % (19369)Time elapsed: 0.052 s
% 0.22/0.47  % (19369)------------------------------
% 0.22/0.47  % (19369)------------------------------
% 0.22/0.48  % (19377)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.48  % (19377)Refutation not found, incomplete strategy% (19377)------------------------------
% 0.22/0.48  % (19377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (19377)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (19377)Memory used [KB]: 1535
% 0.22/0.48  % (19377)Time elapsed: 0.055 s
% 0.22/0.48  % (19377)------------------------------
% 0.22/0.48  % (19377)------------------------------
% 0.22/0.48  % (19365)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.49  % (19383)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.50  % (19363)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.50  % (19366)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (19364)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  % (19362)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.50  % (19364)Refutation not found, incomplete strategy% (19364)------------------------------
% 0.22/0.50  % (19364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (19364)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (19364)Memory used [KB]: 10490
% 0.22/0.50  % (19364)Time elapsed: 0.084 s
% 0.22/0.50  % (19364)------------------------------
% 0.22/0.50  % (19364)------------------------------
% 0.22/0.50  % (19366)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f53,f112,f116,f174,f178])).
% 0.22/0.50  % (19376)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.50  % (19373)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.51  % (19367)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (19382)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (19372)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.51  % (19370)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.51  % (19375)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.51  % (19379)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (19380)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.52  % (19374)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (19384)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.52  % (19378)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.52  % (19361)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.52  % (19371)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.52  % (19371)Refutation not found, incomplete strategy% (19371)------------------------------
% 0.22/0.52  % (19371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19371)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19371)Memory used [KB]: 10490
% 0.22/0.52  % (19371)Time elapsed: 0.111 s
% 0.22/0.52  % (19371)------------------------------
% 0.22/0.52  % (19371)------------------------------
% 0.22/0.53  % (19368)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (19368)Refutation not found, incomplete strategy% (19368)------------------------------
% 0.22/0.53  % (19368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (19368)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (19368)Memory used [KB]: 6012
% 0.22/0.53  % (19368)Time elapsed: 0.116 s
% 0.22/0.53  % (19368)------------------------------
% 0.22/0.53  % (19368)------------------------------
% 0.22/0.53  % (19381)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    spl4_2),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f177])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    $false | spl4_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f52,f141])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.53    inference(resolution,[],[f56,f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | v1_pre_topc(g1_pre_topc(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.22/0.53    inference(resolution,[],[f43,f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    l1_pre_topc(sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f41,f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f6])).
% 0.22/0.53  fof(f6,conjecture,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 0.22/0.53    inference(resolution,[],[f17,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    m1_pre_topc(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ~v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    spl4_2 <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    ~spl4_5 | ~spl4_6),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f173])).
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    $false | (~spl4_5 | ~spl4_6)),
% 0.22/0.53    inference(subsumption_resolution,[],[f172,f141])).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    ~v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_5 | ~spl4_6)),
% 0.22/0.53    inference(subsumption_resolution,[],[f171,f107])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f106])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    spl4_5 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_6),
% 0.22/0.53    inference(subsumption_resolution,[],[f167,f131])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    ~sP2(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | ~spl4_6),
% 0.22/0.53    inference(subsumption_resolution,[],[f127,f18])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    ~sP2(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | ~l1_pre_topc(sK0) | ~spl4_6),
% 0.22/0.53    inference(resolution,[],[f111,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0] : (sQ3_eqProxy(X0,X0)) )),
% 0.22/0.53    inference(equality_proxy_axiom,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.53    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X0] : (~sQ3_eqProxy(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~sP2(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) | ~l1_pre_topc(X0)) ) | ~spl4_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f110])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    spl4_6 <=> ! [X0] : (~l1_pre_topc(X0) | ~sP2(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) | ~sQ3_eqProxy(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    sP2(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.53    inference(resolution,[],[f77,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | ~v1_pre_topc(X0) | sQ3_eqProxy(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0)) )),
% 0.22/0.53    inference(equality_proxy_replacement,[],[f20,f27])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | ~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0] : (~sQ3_eqProxy(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | sP2(X0,sK0)) )),
% 0.22/0.53    inference(resolution,[],[f44,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~sQ3_eqProxy(X0,X1) | sQ3_eqProxy(X1,X0)) )),
% 0.22/0.53    inference(equality_proxy_axiom,[],[f27])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0] : (~sQ3_eqProxy(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | sP2(X0,sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f42,f43])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(sK1) | ~sQ3_eqProxy(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | sP2(X0,sK0)) )),
% 0.22/0.53    inference(resolution,[],[f17,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X2,X0,X3] : (~l1_pre_topc(X2) | ~sQ3_eqProxy(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))) | ~m1_pre_topc(X2,X0) | sP2(X3,X0)) )),
% 0.22/0.53    inference(equality_proxy_replacement,[],[f25,f27])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X2,X0,X3] : (~l1_pre_topc(X2) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~m1_pre_topc(X2,X0) | sP2(X3,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25_D])).
% 0.22/0.53  fof(f25_D,plain,(
% 0.22/0.53    ( ! [X0,X3] : (( ! [X2] : (~l1_pre_topc(X2) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~m1_pre_topc(X2,X0)) ) <=> ~sP2(X3,X0)) )),
% 0.22/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    spl4_5),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f115])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    $false | spl4_5),
% 0.22/0.53    inference(subsumption_resolution,[],[f113,f56])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | spl4_5),
% 0.22/0.53    inference(resolution,[],[f108,f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f106])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ~spl4_5 | spl4_6 | spl4_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f55,f46,f110,f106])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    spl4_1 <=> m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~sQ3_eqProxy(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~sP2(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)) ) | spl4_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f54,f18])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~sQ3_eqProxy(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~sP2(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)) ) | spl4_1),
% 0.22/0.53    inference(resolution,[],[f48,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X3) | ~sQ3_eqProxy(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | m1_pre_topc(X3,X1) | ~sP2(X3,X0)) )),
% 0.22/0.53    inference(equality_proxy_replacement,[],[f26,f27])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X3) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | m1_pre_topc(X3,X1) | ~sP2(X3,X0)) )),
% 0.22/0.53    inference(general_splitting,[],[f21,f25_D])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | ~l1_pre_topc(X3) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X3,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(X3,X1) | (~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ~m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f46])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ~spl4_1 | ~spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f16,f50,f46])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ~v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (19366)------------------------------
% 0.22/0.53  % (19366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (19366)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (19366)Memory used [KB]: 6140
% 0.22/0.53  % (19366)Time elapsed: 0.087 s
% 0.22/0.53  % (19366)------------------------------
% 0.22/0.53  % (19366)------------------------------
% 0.22/0.53  % (19360)Success in time 0.166 s
%------------------------------------------------------------------------------
