%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:21 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 156 expanded)
%              Number of leaves         :   19 (  68 expanded)
%              Depth                    :    9
%              Number of atoms          :  286 ( 617 expanded)
%              Number of equality atoms :   69 ( 163 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f44,f48,f52,f56,f66,f71,f95,f100,f113,f115,f130])).

fof(f130,plain,
    ( spl2_6
    | ~ spl2_5
    | ~ spl2_4
    | ~ spl2_3
    | spl2_14 ),
    inference(avatar_split_clause,[],[f127,f110,f42,f46,f50,f54])).

fof(f54,plain,
    ( spl2_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f50,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f46,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f42,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f110,plain,
    ( spl2_14
  <=> l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f127,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl2_14 ),
    inference(resolution,[],[f111,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f111,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | spl2_14 ),
    inference(avatar_component_clause,[],[f110])).

fof(f115,plain,
    ( ~ spl2_14
    | spl2_1
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f107,f98,f69,f35,f110])).

fof(f35,plain,
    ( spl2_1
  <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

% (21358)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (21361)Termination reason: Refutation not found, incomplete strategy

% (21361)Memory used [KB]: 10618
% (21361)Time elapsed: 0.127 s
% (21361)------------------------------
% (21361)------------------------------
% (21363)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (21367)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (21367)Refutation not found, incomplete strategy% (21367)------------------------------
% (21367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21367)Termination reason: Refutation not found, incomplete strategy

% (21367)Memory used [KB]: 10618
% (21367)Time elapsed: 0.136 s
% (21367)------------------------------
% (21367)------------------------------
% (21370)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (21378)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (21376)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (21374)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (21359)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (21371)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (21359)Refutation not found, incomplete strategy% (21359)------------------------------
% (21359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21359)Termination reason: Refutation not found, incomplete strategy

% (21359)Memory used [KB]: 10746
% (21359)Time elapsed: 0.140 s
% (21359)------------------------------
% (21359)------------------------------
% (21362)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f69,plain,
    ( spl2_8
  <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f98,plain,
    ( spl2_13
  <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f107,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(trivial_inequality_removal,[],[f102])).

fof(f102,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(superposition,[],[f87,f99])).

fof(f99,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f98])).

fof(f87,plain,
    ( ! [X0] :
        ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(sK0,sK1)
        | u1_struct_0(X0) = u1_struct_0(sK0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_8 ),
    inference(resolution,[],[f74,f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f74,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X4)))
        | u1_struct_0(sK0) = X4
        | k6_tmap_1(sK0,sK1) != g1_pre_topc(X4,X5) )
    | ~ spl2_8 ),
    inference(superposition,[],[f29,f70])).

fof(f70,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f113,plain,
    ( ~ spl2_14
    | spl2_2
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f108,f98,f69,f38,f110])).

fof(f38,plain,
    ( spl2_2
  <=> k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f108,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(trivial_inequality_removal,[],[f101])).

fof(f101,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1)
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(superposition,[],[f88,f99])).

fof(f88,plain,
    ( ! [X0] :
        ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(sK0,sK1)
        | u1_pre_topc(X0) = k5_tmap_1(sK0,sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_8 ),
    inference(resolution,[],[f72,f26])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k5_tmap_1(sK0,sK1) = X1
        | g1_pre_topc(X0,X1) != k6_tmap_1(sK0,sK1) )
    | ~ spl2_8 ),
    inference(superposition,[],[f30,f70])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f100,plain,
    ( spl2_13
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f96,f93,f42,f98])).

fof(f93,plain,
    ( spl2_12
  <=> ! [X0] :
        ( k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f96,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(resolution,[],[f94,f43])).

fof(f43,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f93])).

fof(f95,plain,
    ( spl2_12
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f91,f54,f50,f46,f93])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl2_6 ),
    inference(resolution,[],[f90,f55])).

fof(f55,plain,
    ( ~ v2_struct_0(sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(X0,X1)),u1_pre_topc(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(X0,X1)),u1_pre_topc(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f59,f33])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(k6_tmap_1(X1,X0))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | k6_tmap_1(X1,X0) = g1_pre_topc(u1_struct_0(k6_tmap_1(X1,X0)),u1_pre_topc(k6_tmap_1(X1,X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f31,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f67,f64,f42,f69])).

fof(f64,plain,
    ( spl2_7
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f67,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f65,f43])).

fof(f65,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f66,plain,
    ( ~ spl2_5
    | ~ spl2_4
    | spl2_7
    | spl2_6 ),
    inference(avatar_split_clause,[],[f60,f54,f64,f46,f50])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) )
    | spl2_6 ),
    inference(resolution,[],[f28,f55])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

fof(f56,plain,(
    ~ spl2_6 ),
    inference(avatar_split_clause,[],[f21,f54])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1))
      | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1))
              | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k5_tmap_1(sK0,X1) != u1_pre_topc(k6_tmap_1(sK0,X1))
            | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ( k5_tmap_1(sK0,X1) != u1_pre_topc(k6_tmap_1(sK0,X1))
          | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1))
        | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1))
            | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1))
            | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
              & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f52,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f24,f42])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f25,f38,f35])).

fof(f25,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1))
    | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:24:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.24/0.53  % (21354)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.24/0.53  % (21352)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.53  % (21351)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.24/0.53  % (21377)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.24/0.53  % (21372)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.24/0.53  % (21364)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.24/0.54  % (21360)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.24/0.54  % (21355)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.24/0.54  % (21357)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.24/0.54  % (21360)Refutation not found, incomplete strategy% (21360)------------------------------
% 1.24/0.54  % (21360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (21360)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (21360)Memory used [KB]: 10618
% 1.24/0.54  % (21360)Time elapsed: 0.128 s
% 1.24/0.54  % (21360)------------------------------
% 1.24/0.54  % (21360)------------------------------
% 1.24/0.54  % (21372)Refutation not found, incomplete strategy% (21372)------------------------------
% 1.24/0.54  % (21372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (21372)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (21372)Memory used [KB]: 10746
% 1.24/0.54  % (21372)Time elapsed: 0.080 s
% 1.24/0.54  % (21372)------------------------------
% 1.24/0.54  % (21372)------------------------------
% 1.24/0.54  % (21361)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.24/0.54  % (21353)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.54  % (21366)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.24/0.54  % (21356)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.24/0.54  % (21361)Refutation not found, incomplete strategy% (21361)------------------------------
% 1.24/0.54  % (21361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (21369)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.24/0.54  % (21368)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.24/0.54  % (21369)Refutation found. Thanks to Tanya!
% 1.24/0.54  % SZS status Theorem for theBenchmark
% 1.24/0.54  % SZS output start Proof for theBenchmark
% 1.24/0.54  fof(f131,plain,(
% 1.24/0.54    $false),
% 1.24/0.54    inference(avatar_sat_refutation,[],[f40,f44,f48,f52,f56,f66,f71,f95,f100,f113,f115,f130])).
% 1.24/0.54  fof(f130,plain,(
% 1.24/0.54    spl2_6 | ~spl2_5 | ~spl2_4 | ~spl2_3 | spl2_14),
% 1.24/0.54    inference(avatar_split_clause,[],[f127,f110,f42,f46,f50,f54])).
% 1.24/0.54  fof(f54,plain,(
% 1.24/0.54    spl2_6 <=> v2_struct_0(sK0)),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.24/0.54  fof(f50,plain,(
% 1.24/0.54    spl2_5 <=> v2_pre_topc(sK0)),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.24/0.54  fof(f46,plain,(
% 1.24/0.54    spl2_4 <=> l1_pre_topc(sK0)),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.24/0.54  fof(f42,plain,(
% 1.24/0.54    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.24/0.54  fof(f110,plain,(
% 1.24/0.54    spl2_14 <=> l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 1.24/0.54  fof(f127,plain,(
% 1.24/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl2_14),
% 1.24/0.54    inference(resolution,[],[f111,f33])).
% 1.24/0.54  fof(f33,plain,(
% 1.24/0.54    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f17])).
% 1.24/0.54  fof(f17,plain,(
% 1.24/0.54    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.24/0.54    inference(flattening,[],[f16])).
% 1.24/0.54  fof(f16,plain,(
% 1.24/0.54    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.24/0.54    inference(ennf_transformation,[],[f5])).
% 1.24/0.54  fof(f5,axiom,(
% 1.24/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 1.24/0.54  fof(f111,plain,(
% 1.24/0.54    ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | spl2_14),
% 1.24/0.54    inference(avatar_component_clause,[],[f110])).
% 1.24/0.54  fof(f115,plain,(
% 1.24/0.54    ~spl2_14 | spl2_1 | ~spl2_8 | ~spl2_13),
% 1.24/0.54    inference(avatar_split_clause,[],[f107,f98,f69,f35,f110])).
% 1.24/0.54  fof(f35,plain,(
% 1.24/0.54    spl2_1 <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.24/0.54  % (21358)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.24/0.54  % (21361)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (21361)Memory used [KB]: 10618
% 1.47/0.55  % (21361)Time elapsed: 0.127 s
% 1.47/0.55  % (21361)------------------------------
% 1.47/0.55  % (21361)------------------------------
% 1.47/0.55  % (21363)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.47/0.55  % (21367)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.47/0.55  % (21367)Refutation not found, incomplete strategy% (21367)------------------------------
% 1.47/0.55  % (21367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (21367)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (21367)Memory used [KB]: 10618
% 1.47/0.55  % (21367)Time elapsed: 0.136 s
% 1.47/0.55  % (21367)------------------------------
% 1.47/0.55  % (21367)------------------------------
% 1.47/0.55  % (21370)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.47/0.55  % (21378)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.47/0.55  % (21376)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.47/0.55  % (21374)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.47/0.55  % (21359)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.47/0.55  % (21371)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.47/0.56  % (21359)Refutation not found, incomplete strategy% (21359)------------------------------
% 1.47/0.56  % (21359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (21359)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (21359)Memory used [KB]: 10746
% 1.47/0.56  % (21359)Time elapsed: 0.140 s
% 1.47/0.56  % (21359)------------------------------
% 1.47/0.56  % (21359)------------------------------
% 1.47/0.56  % (21362)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.47/0.56  fof(f69,plain,(
% 1.47/0.56    spl2_8 <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.47/0.56  fof(f98,plain,(
% 1.47/0.56    spl2_13 <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1)))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.47/0.56  fof(f107,plain,(
% 1.47/0.56    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | (~spl2_8 | ~spl2_13)),
% 1.47/0.56    inference(trivial_inequality_removal,[],[f102])).
% 1.47/0.56  fof(f102,plain,(
% 1.47/0.56    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | (~spl2_8 | ~spl2_13)),
% 1.47/0.56    inference(superposition,[],[f87,f99])).
% 1.47/0.56  fof(f99,plain,(
% 1.47/0.56    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) | ~spl2_13),
% 1.47/0.56    inference(avatar_component_clause,[],[f98])).
% 1.47/0.56  fof(f87,plain,(
% 1.47/0.56    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(sK0,sK1) | u1_struct_0(X0) = u1_struct_0(sK0) | ~l1_pre_topc(X0)) ) | ~spl2_8),
% 1.47/0.56    inference(resolution,[],[f74,f26])).
% 1.47/0.56  fof(f26,plain,(
% 1.47/0.56    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f10])).
% 1.47/0.56  fof(f10,plain,(
% 1.47/0.56    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.47/0.56    inference(ennf_transformation,[],[f2])).
% 1.47/0.56  fof(f2,axiom,(
% 1.47/0.56    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.47/0.56  fof(f74,plain,(
% 1.47/0.56    ( ! [X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X4))) | u1_struct_0(sK0) = X4 | k6_tmap_1(sK0,sK1) != g1_pre_topc(X4,X5)) ) | ~spl2_8),
% 1.47/0.56    inference(superposition,[],[f29,f70])).
% 1.47/0.56  fof(f70,plain,(
% 1.47/0.56    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) | ~spl2_8),
% 1.47/0.56    inference(avatar_component_clause,[],[f69])).
% 1.47/0.56  fof(f29,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f15])).
% 1.47/0.56  fof(f15,plain,(
% 1.47/0.56    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.47/0.56    inference(ennf_transformation,[],[f3])).
% 1.47/0.56  fof(f3,axiom,(
% 1.47/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.47/0.56  fof(f113,plain,(
% 1.47/0.56    ~spl2_14 | spl2_2 | ~spl2_8 | ~spl2_13),
% 1.47/0.56    inference(avatar_split_clause,[],[f108,f98,f69,f38,f110])).
% 1.47/0.56  fof(f38,plain,(
% 1.47/0.56    spl2_2 <=> k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.47/0.56  fof(f108,plain,(
% 1.47/0.56    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | (~spl2_8 | ~spl2_13)),
% 1.47/0.56    inference(trivial_inequality_removal,[],[f101])).
% 1.47/0.56  fof(f101,plain,(
% 1.47/0.56    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1) | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | (~spl2_8 | ~spl2_13)),
% 1.47/0.56    inference(superposition,[],[f88,f99])).
% 1.47/0.56  fof(f88,plain,(
% 1.47/0.56    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(sK0,sK1) | u1_pre_topc(X0) = k5_tmap_1(sK0,sK1) | ~l1_pre_topc(X0)) ) | ~spl2_8),
% 1.47/0.56    inference(resolution,[],[f72,f26])).
% 1.47/0.56  fof(f72,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k5_tmap_1(sK0,sK1) = X1 | g1_pre_topc(X0,X1) != k6_tmap_1(sK0,sK1)) ) | ~spl2_8),
% 1.47/0.56    inference(superposition,[],[f30,f70])).
% 1.47/0.56  fof(f30,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f15])).
% 1.47/0.56  fof(f100,plain,(
% 1.47/0.56    spl2_13 | ~spl2_3 | ~spl2_12),
% 1.47/0.56    inference(avatar_split_clause,[],[f96,f93,f42,f98])).
% 1.47/0.56  fof(f93,plain,(
% 1.47/0.56    spl2_12 <=> ! [X0] : (k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.47/0.56  fof(f96,plain,(
% 1.47/0.56    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) | (~spl2_3 | ~spl2_12)),
% 1.47/0.56    inference(resolution,[],[f94,f43])).
% 1.47/0.56  fof(f43,plain,(
% 1.47/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.47/0.56    inference(avatar_component_clause,[],[f42])).
% 1.47/0.56  fof(f94,plain,(
% 1.47/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0)))) ) | ~spl2_12),
% 1.47/0.56    inference(avatar_component_clause,[],[f93])).
% 1.47/0.56  fof(f95,plain,(
% 1.47/0.56    spl2_12 | ~spl2_4 | ~spl2_5 | spl2_6),
% 1.47/0.56    inference(avatar_split_clause,[],[f91,f54,f50,f46,f93])).
% 1.47/0.56  fof(f91,plain,(
% 1.47/0.56    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | spl2_6),
% 1.47/0.56    inference(resolution,[],[f90,f55])).
% 1.47/0.56  fof(f55,plain,(
% 1.47/0.56    ~v2_struct_0(sK0) | spl2_6),
% 1.47/0.56    inference(avatar_component_clause,[],[f54])).
% 1.47/0.56  fof(f90,plain,(
% 1.47/0.56    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(X0,X1)),u1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.47/0.56    inference(duplicate_literal_removal,[],[f89])).
% 1.47/0.56  fof(f89,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(X0,X1)),u1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.56    inference(resolution,[],[f59,f33])).
% 1.47/0.56  fof(f59,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~l1_pre_topc(k6_tmap_1(X1,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | k6_tmap_1(X1,X0) = g1_pre_topc(u1_struct_0(k6_tmap_1(X1,X0)),u1_pre_topc(k6_tmap_1(X1,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 1.47/0.56    inference(resolution,[],[f31,f27])).
% 1.47/0.56  fof(f27,plain,(
% 1.47/0.56    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f12,plain,(
% 1.47/0.56    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.47/0.56    inference(flattening,[],[f11])).
% 1.47/0.56  fof(f11,plain,(
% 1.47/0.56    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 1.47/0.56    inference(ennf_transformation,[],[f1])).
% 1.47/0.56  fof(f1,axiom,(
% 1.47/0.56    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 1.47/0.56  fof(f31,plain,(
% 1.47/0.56    ( ! [X0,X1] : (v1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f17])).
% 1.47/0.56  fof(f71,plain,(
% 1.47/0.56    spl2_8 | ~spl2_3 | ~spl2_7),
% 1.47/0.56    inference(avatar_split_clause,[],[f67,f64,f42,f69])).
% 1.47/0.56  fof(f64,plain,(
% 1.47/0.56    spl2_7 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.47/0.56  fof(f67,plain,(
% 1.47/0.56    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) | (~spl2_3 | ~spl2_7)),
% 1.47/0.56    inference(resolution,[],[f65,f43])).
% 1.47/0.56  fof(f65,plain,(
% 1.47/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0))) ) | ~spl2_7),
% 1.47/0.56    inference(avatar_component_clause,[],[f64])).
% 1.47/0.56  fof(f66,plain,(
% 1.47/0.56    ~spl2_5 | ~spl2_4 | spl2_7 | spl2_6),
% 1.47/0.56    inference(avatar_split_clause,[],[f60,f54,f64,f46,f50])).
% 1.47/0.56  fof(f60,plain,(
% 1.47/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0))) ) | spl2_6),
% 1.47/0.56    inference(resolution,[],[f28,f55])).
% 1.47/0.56  fof(f28,plain,(
% 1.47/0.56    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f14])).
% 1.47/0.56  fof(f14,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.56    inference(flattening,[],[f13])).
% 1.47/0.56  fof(f13,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.56    inference(ennf_transformation,[],[f4])).
% 1.47/0.56  fof(f4,axiom,(
% 1.47/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).
% 1.47/0.56  fof(f56,plain,(
% 1.47/0.56    ~spl2_6),
% 1.47/0.56    inference(avatar_split_clause,[],[f21,f54])).
% 1.47/0.56  fof(f21,plain,(
% 1.47/0.56    ~v2_struct_0(sK0)),
% 1.47/0.56    inference(cnf_transformation,[],[f20])).
% 1.47/0.56  fof(f20,plain,(
% 1.47/0.56    ((k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1)) | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f19,f18])).
% 1.47/0.56  fof(f18,plain,(
% 1.47/0.56    ? [X0] : (? [X1] : ((k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1)) | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((k5_tmap_1(sK0,X1) != u1_pre_topc(k6_tmap_1(sK0,X1)) | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f19,plain,(
% 1.47/0.56    ? [X1] : ((k5_tmap_1(sK0,X1) != u1_pre_topc(k6_tmap_1(sK0,X1)) | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1)) | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f9,plain,(
% 1.47/0.56    ? [X0] : (? [X1] : ((k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1)) | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.47/0.56    inference(flattening,[],[f8])).
% 1.47/0.56  fof(f8,plain,(
% 1.47/0.56    ? [X0] : (? [X1] : ((k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1)) | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.47/0.56    inference(ennf_transformation,[],[f7])).
% 1.47/0.56  fof(f7,negated_conjecture,(
% 1.47/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 1.47/0.56    inference(negated_conjecture,[],[f6])).
% 1.47/0.56  fof(f6,conjecture,(
% 1.47/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).
% 1.47/0.56  fof(f52,plain,(
% 1.47/0.56    spl2_5),
% 1.47/0.56    inference(avatar_split_clause,[],[f22,f50])).
% 1.47/0.56  fof(f22,plain,(
% 1.47/0.56    v2_pre_topc(sK0)),
% 1.47/0.56    inference(cnf_transformation,[],[f20])).
% 1.47/0.56  fof(f48,plain,(
% 1.47/0.56    spl2_4),
% 1.47/0.56    inference(avatar_split_clause,[],[f23,f46])).
% 1.47/0.56  fof(f23,plain,(
% 1.47/0.56    l1_pre_topc(sK0)),
% 1.47/0.56    inference(cnf_transformation,[],[f20])).
% 1.47/0.56  fof(f44,plain,(
% 1.47/0.56    spl2_3),
% 1.47/0.56    inference(avatar_split_clause,[],[f24,f42])).
% 1.47/0.56  fof(f24,plain,(
% 1.47/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.56    inference(cnf_transformation,[],[f20])).
% 1.47/0.56  fof(f40,plain,(
% 1.47/0.56    ~spl2_1 | ~spl2_2),
% 1.47/0.56    inference(avatar_split_clause,[],[f25,f38,f35])).
% 1.47/0.56  fof(f25,plain,(
% 1.47/0.56    k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1)) | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1))),
% 1.47/0.56    inference(cnf_transformation,[],[f20])).
% 1.47/0.56  % SZS output end Proof for theBenchmark
% 1.47/0.56  % (21369)------------------------------
% 1.47/0.56  % (21369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (21369)Termination reason: Refutation
% 1.47/0.56  
% 1.47/0.56  % (21369)Memory used [KB]: 10746
% 1.47/0.56  % (21369)Time elapsed: 0.138 s
% 1.47/0.56  % (21369)------------------------------
% 1.47/0.56  % (21369)------------------------------
% 1.47/0.56  % (21375)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.47/0.56  % (21349)Success in time 0.194 s
%------------------------------------------------------------------------------
