%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 250 expanded)
%              Number of leaves         :   20 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          :  573 (1063 expanded)
%              Number of equality atoms :   40 (  74 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f255,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f55,f59,f63,f93,f97,f101,f105,f109,f113,f151,f179,f201,f220,f254])).

fof(f254,plain,
    ( ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | spl4_11
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | spl4_11
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f252,f112])).

fof(f112,plain,
    ( ~ v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_11
  <=> v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f252,plain,
    ( v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f251,f219])).

% (8277)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f219,plain,
    ( v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl4_20
  <=> v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f251,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f250,f100])).

fof(f100,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_8
  <=> v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f250,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f249,f96])).

fof(f96,plain,
    ( m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_7
  <=> m1_pre_topc(sK2,k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f249,plain,
    ( ~ m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f247,f108])).

fof(f108,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_10
  <=> l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f247,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(resolution,[],[f141,f178])).

fof(f178,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1))))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl4_15
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f141,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(sK2,X5)
        | ~ v2_pre_topc(X5)
        | ~ v3_pre_topc(u1_struct_0(sK1),X5)
        | v1_tsep_1(sK2,X5) )
    | ~ spl4_9 ),
    inference(superposition,[],[f38,f104])).

fof(f104,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_9
  <=> u1_struct_0(sK1) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f220,plain,
    ( spl4_20
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f213,f199,f177,f149,f57,f53,f49,f218])).

fof(f49,plain,
    ( spl4_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f53,plain,
    ( spl4_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f57,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f149,plain,
    ( spl4_12
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f199,plain,
    ( spl4_18
  <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f213,plain,
    ( v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f212,f50])).

fof(f50,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f212,plain,
    ( v2_struct_0(sK0)
    | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f211,f150])).

fof(f150,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f149])).

fof(f211,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f210,f58])).

fof(f58,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f210,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f209,f54])).

fof(f54,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f209,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f208,f178])).

fof(f208,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ spl4_18 ),
    inference(superposition,[],[f40,f200])).

fof(f200,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f199])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | v3_pre_topc(X2,k6_tmap_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | X1 != X2
      | v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).

fof(f201,plain,
    ( spl4_18
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f161,f149,f107,f99,f91,f61,f57,f53,f49,f199])).

fof(f61,plain,
    ( spl4_5
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f91,plain,
    ( spl4_6
  <=> v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f161,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f160,f50])).

fof(f160,plain,
    ( v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f159,f108])).

fof(f159,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f158,f100])).

fof(f158,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f157,f92])).

fof(f92,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f157,plain,
    ( ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f156,f62])).

fof(f62,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f156,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f155,f58])).

fof(f155,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f152,f54])).

fof(f152,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_12 ),
    inference(resolution,[],[f150,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X3
      | k6_tmap_1(X0,X3) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f179,plain,
    ( spl4_15
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f129,f107,f103,f95,f177])).

fof(f129,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1))))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f128,f104])).

fof(f128,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1))))
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f117,f108])).

fof(f117,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1))))
    | ~ spl4_7 ),
    inference(resolution,[],[f96,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f151,plain,
    ( spl4_12
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f80,f61,f57,f149])).

fof(f80,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f67,f58])).

fof(f67,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5 ),
    inference(resolution,[],[f62,f34])).

fof(f113,plain,(
    ~ spl4_11 ),
    inference(avatar_split_clause,[],[f43,f111])).

fof(f43,plain,(
    ~ v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f19,f20])).

fof(f20,plain,(
    m1_pre_topc(sK2,k8_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,k8_tmap_1(X0,X1))
                | ~ v1_tsep_1(X2,k8_tmap_1(X0,X1)) )
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_pre_topc(X2,k8_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,k8_tmap_1(X0,X1))
                | ~ v1_tsep_1(X2,k8_tmap_1(X0,X1)) )
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_pre_topc(X2,k8_tmap_1(X0,X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
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
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
               => ( u1_struct_0(X1) = u1_struct_0(X2)
                 => ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
                    & v1_tsep_1(X2,k8_tmap_1(X0,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => ( m1_pre_topc(X2,k8_tmap_1(X0,X1))
                  & v1_tsep_1(X2,k8_tmap_1(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_tmap_1)).

fof(f19,plain,
    ( ~ v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK2,k8_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f109,plain,
    ( spl4_10
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f89,f61,f57,f53,f49,f107])).

fof(f89,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f88,f50])).

fof(f88,plain,
    ( v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f87,f58])).

fof(f87,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f70,f54])).

fof(f70,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(resolution,[],[f62,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f105,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f21,f103])).

fof(f21,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f101,plain,
    ( spl4_8
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f86,f61,f57,f53,f49,f99])).

fof(f86,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f85,f50])).

fof(f85,plain,
    ( v2_struct_0(sK0)
    | v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f84,f58])).

fof(f84,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f69,f54])).

fof(f69,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(resolution,[],[f62,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f97,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f20,f95])).

fof(f93,plain,
    ( spl4_6
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f83,f61,f57,f53,f49,f91])).

fof(f83,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f82,f50])).

fof(f82,plain,
    ( v2_struct_0(sK0)
    | v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f81,f58])).

fof(f81,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f68,f54])).

fof(f68,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(resolution,[],[f62,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f23,f61])).

fof(f23,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f26,f57])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f25,f53])).

fof(f25,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f51,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:44:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (8284)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.44  % (8284)Refutation not found, incomplete strategy% (8284)------------------------------
% 0.22/0.44  % (8284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (8284)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.44  
% 0.22/0.44  % (8284)Memory used [KB]: 1663
% 0.22/0.44  % (8284)Time elapsed: 0.006 s
% 0.22/0.44  % (8284)------------------------------
% 0.22/0.44  % (8284)------------------------------
% 0.22/0.48  % (8278)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (8285)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (8276)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (8286)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (8271)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (8283)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (8283)Refutation not found, incomplete strategy% (8283)------------------------------
% 0.22/0.52  % (8283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8271)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f255,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f51,f55,f59,f63,f93,f97,f101,f105,f109,f113,f151,f179,f201,f220,f254])).
% 0.22/0.53  fof(f254,plain,(
% 0.22/0.53    ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | spl4_11 | ~spl4_15 | ~spl4_20),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f253])).
% 0.22/0.53  fof(f253,plain,(
% 0.22/0.53    $false | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | spl4_11 | ~spl4_15 | ~spl4_20)),
% 0.22/0.53    inference(subsumption_resolution,[],[f252,f112])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ~v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) | spl4_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    spl4_11 <=> v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.53  fof(f252,plain,(
% 0.22/0.53    v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_15 | ~spl4_20)),
% 0.22/0.53    inference(subsumption_resolution,[],[f251,f219])).
% 0.22/0.53  % (8277)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.53  fof(f219,plain,(
% 0.22/0.53    v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) | ~spl4_20),
% 0.22/0.53    inference(avatar_component_clause,[],[f218])).
% 0.22/0.53  fof(f218,plain,(
% 0.22/0.53    spl4_20 <=> v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.53  fof(f251,plain,(
% 0.22/0.53    ~v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) | v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_15)),
% 0.22/0.53    inference(subsumption_resolution,[],[f250,f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl4_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    spl4_8 <=> v2_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.53  fof(f250,plain,(
% 0.22/0.53    ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) | v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_15)),
% 0.22/0.53    inference(subsumption_resolution,[],[f249,f96])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    m1_pre_topc(sK2,k8_tmap_1(sK0,sK1)) | ~spl4_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f95])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    spl4_7 <=> m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.53  fof(f249,plain,(
% 0.22/0.53    ~m1_pre_topc(sK2,k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) | v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) | (~spl4_9 | ~spl4_10 | ~spl4_15)),
% 0.22/0.53    inference(subsumption_resolution,[],[f247,f108])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl4_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f107])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    spl4_10 <=> l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.53  fof(f247,plain,(
% 0.22/0.53    ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK2,k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) | v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) | (~spl4_9 | ~spl4_15)),
% 0.22/0.53    inference(resolution,[],[f141,f178])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1)))) | ~spl4_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f177])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    spl4_15 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    ( ! [X5] : (~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X5))) | ~l1_pre_topc(X5) | ~m1_pre_topc(sK2,X5) | ~v2_pre_topc(X5) | ~v3_pre_topc(u1_struct_0(sK1),X5) | v1_tsep_1(sK2,X5)) ) | ~spl4_9),
% 0.22/0.53    inference(superposition,[],[f38,f104])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    u1_struct_0(sK1) = u1_struct_0(sK2) | ~spl4_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f103])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    spl4_9 <=> u1_struct_0(sK1) = u1_struct_0(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    spl4_20 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_18),
% 0.22/0.53    inference(avatar_split_clause,[],[f213,f199,f177,f149,f57,f53,f49,f218])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    spl4_2 <=> v2_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    spl4_3 <=> v2_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    spl4_4 <=> l1_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    spl4_12 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    spl4_18 <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.53  fof(f213,plain,(
% 0.22/0.53    v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_18)),
% 0.22/0.53    inference(subsumption_resolution,[],[f212,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ~v2_struct_0(sK0) | spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f49])).
% 0.22/0.53  fof(f212,plain,(
% 0.22/0.53    v2_struct_0(sK0) | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_18)),
% 0.22/0.53    inference(subsumption_resolution,[],[f211,f150])).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f149])).
% 0.22/0.53  fof(f211,plain,(
% 0.22/0.53    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_15 | ~spl4_18)),
% 0.22/0.53    inference(subsumption_resolution,[],[f210,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    l1_pre_topc(sK0) | ~spl4_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f57])).
% 0.22/0.53  fof(f210,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_15 | ~spl4_18)),
% 0.22/0.53    inference(subsumption_resolution,[],[f209,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    v2_pre_topc(sK0) | ~spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f53])).
% 0.22/0.53  fof(f209,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) | (~spl4_15 | ~spl4_18)),
% 0.22/0.53    inference(subsumption_resolution,[],[f208,f178])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1)))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) | ~spl4_18),
% 0.22/0.53    inference(superposition,[],[f40,f200])).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~spl4_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f199])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | v3_pre_topc(X2,k6_tmap_1(X0,X2))) )),
% 0.22/0.53    inference(equality_resolution,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) | X1 != X2 | v3_pre_topc(X2,k6_tmap_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    spl4_18 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_10 | ~spl4_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f161,f149,f107,f99,f91,f61,f57,f53,f49,f199])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    spl4_5 <=> m1_pre_topc(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    spl4_6 <=> v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_10 | ~spl4_12)),
% 0.22/0.53    inference(subsumption_resolution,[],[f160,f50])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    v2_struct_0(sK0) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_10 | ~spl4_12)),
% 0.22/0.53    inference(subsumption_resolution,[],[f159,f108])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_12)),
% 0.22/0.53    inference(subsumption_resolution,[],[f158,f100])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_12)),
% 0.22/0.53    inference(subsumption_resolution,[],[f157,f92])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl4_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f91])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_12)),
% 0.22/0.53    inference(subsumption_resolution,[],[f156,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    m1_pre_topc(sK1,sK0) | ~spl4_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f61])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    ~m1_pre_topc(sK1,sK0) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_12)),
% 0.22/0.53    inference(subsumption_resolution,[],[f155,f58])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_3 | ~spl4_12)),
% 0.22/0.53    inference(subsumption_resolution,[],[f152,f54])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~spl4_12),
% 0.22/0.53    inference(resolution,[],[f150,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | v2_struct_0(X0) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) )),
% 0.22/0.53    inference(equality_resolution,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k6_tmap_1(X0,u1_struct_0(X1)) = X2 | k8_tmap_1(X0,X1) != X2) )),
% 0.22/0.53    inference(equality_resolution,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X3 | k6_tmap_1(X0,X3) = X2 | k8_tmap_1(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    spl4_15 | ~spl4_7 | ~spl4_9 | ~spl4_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f129,f107,f103,f95,f177])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1)))) | (~spl4_7 | ~spl4_9 | ~spl4_10)),
% 0.22/0.53    inference(forward_demodulation,[],[f128,f104])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1)))) | (~spl4_7 | ~spl4_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f117,f108])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1)))) | ~spl4_7),
% 0.22/0.53    inference(resolution,[],[f96,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    spl4_12 | ~spl4_4 | ~spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f80,f61,f57,f149])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f67,f58])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_5),
% 0.22/0.53    inference(resolution,[],[f62,f34])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ~spl4_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f43,f111])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ~v1_tsep_1(sK2,k8_tmap_1(sK0,sK1))),
% 0.22/0.53    inference(subsumption_resolution,[],[f19,f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,k8_tmap_1(X0,X1)) | ~v1_tsep_1(X2,k8_tmap_1(X0,X1))) & u1_struct_0(X1) = u1_struct_0(X2) & m1_pre_topc(X2,k8_tmap_1(X0,X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (((~m1_pre_topc(X2,k8_tmap_1(X0,X1)) | ~v1_tsep_1(X2,k8_tmap_1(X0,X1))) & u1_struct_0(X1) = u1_struct_0(X2)) & m1_pre_topc(X2,k8_tmap_1(X0,X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,k8_tmap_1(X0,X1)) => (u1_struct_0(X1) = u1_struct_0(X2) => (m1_pre_topc(X2,k8_tmap_1(X0,X1)) & v1_tsep_1(X2,k8_tmap_1(X0,X1)))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f6])).
% 0.22/0.53  fof(f6,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,k8_tmap_1(X0,X1)) => (u1_struct_0(X1) = u1_struct_0(X2) => (m1_pre_topc(X2,k8_tmap_1(X0,X1)) & v1_tsep_1(X2,k8_tmap_1(X0,X1)))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_tmap_1)).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ~v1_tsep_1(sK2,k8_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK2,k8_tmap_1(sK0,sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    spl4_10 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f89,f61,f57,f53,f49,f107])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    l1_pre_topc(k8_tmap_1(sK0,sK1)) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f88,f50])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f87,f58])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f70,f54])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl4_5),
% 0.22/0.53    inference(resolution,[],[f62,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | l1_pre_topc(k8_tmap_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    spl4_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f21,f103])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    u1_struct_0(sK1) = u1_struct_0(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    spl4_8 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f86,f61,f57,f53,f49,f99])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    v2_pre_topc(k8_tmap_1(sK0,sK1)) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f85,f50])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    v2_struct_0(sK0) | v2_pre_topc(k8_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f84,f58])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_pre_topc(k8_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f69,f54])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl4_5),
% 0.22/0.53    inference(resolution,[],[f62,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_pre_topc(k8_tmap_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    spl4_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f20,f95])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    spl4_6 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f83,f61,f57,f53,f49,f91])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    v1_pre_topc(k8_tmap_1(sK0,sK1)) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f82,f50])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    v2_struct_0(sK0) | v1_pre_topc(k8_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f81,f58])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_pre_topc(k8_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f68,f54])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl4_5),
% 0.22/0.53    inference(resolution,[],[f62,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_pre_topc(k8_tmap_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f23,f61])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    m1_pre_topc(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f26,f57])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    spl4_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f25,f53])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ~spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f24,f49])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (8271)------------------------------
% 0.22/0.53  % (8271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8271)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (8271)Memory used [KB]: 6268
% 0.22/0.53  % (8271)Time elapsed: 0.099 s
% 0.22/0.53  % (8271)------------------------------
% 0.22/0.53  % (8271)------------------------------
% 0.22/0.54  % (8270)Success in time 0.176 s
%------------------------------------------------------------------------------
