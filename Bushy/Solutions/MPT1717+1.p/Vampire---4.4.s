%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t26_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:12 EDT 2019

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 347 expanded)
%              Number of leaves         :   36 ( 138 expanded)
%              Depth                    :   14
%              Number of atoms          :  789 (1379 expanded)
%              Number of equality atoms :   58 ( 124 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f554,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f95,f102,f109,f116,f123,f130,f137,f152,f196,f219,f237,f247,f280,f333,f340,f347,f360,f368,f384,f471,f500,f553])).

fof(f553,plain,
    ( spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_44 ),
    inference(avatar_contradiction_clause,[],[f552])).

fof(f552,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f551,f108])).

fof(f108,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f551,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f550,f101])).

fof(f101,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f550,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f546,f94])).

fof(f94,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_3
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f546,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_8
    | ~ spl4_44 ),
    inference(resolution,[],[f470,f115])).

fof(f115,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_8
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f470,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f469])).

fof(f469,plain,
    ( spl4_44
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f500,plain,
    ( ~ spl4_16
    | spl4_43 ),
    inference(avatar_contradiction_clause,[],[f499])).

fof(f499,plain,
    ( $false
    | ~ spl4_16
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f498,f151])).

fof(f151,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl4_16
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f498,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl4_43 ),
    inference(resolution,[],[f467,f79])).

fof(f79,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t26_tmap_1.p',t2_tsep_1)).

fof(f467,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f466])).

fof(f466,plain,
    ( spl4_43
  <=> ~ m1_pre_topc(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f471,plain,
    ( ~ spl4_43
    | spl4_44
    | spl4_1
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f302,f278,f86,f469,f466])).

fof(f86,plain,
    ( spl4_1
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f278,plain,
    ( spl4_28
  <=> r1_tsep_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f302,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK1,sK1)
        | v2_struct_0(X0) )
    | ~ spl4_1
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f301,f87])).

fof(f87,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f301,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK1,sK1)
        | v2_struct_0(X0) )
    | ~ spl4_28 ),
    inference(duplicate_literal_removal,[],[f298])).

fof(f298,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK1,sK1)
        | v2_struct_0(X0) )
    | ~ spl4_28 ),
    inference(resolution,[],[f279,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X2,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t26_tmap_1.p',t22_tmap_1)).

fof(f279,plain,
    ( r1_tsep_1(sK1,sK1)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f278])).

fof(f384,plain,
    ( spl4_40
    | ~ spl4_16
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f313,f217,f150,f382])).

fof(f382,plain,
    ( spl4_40
  <=> l1_pre_topc(k2_tsep_1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f217,plain,
    ( spl4_24
  <=> k2_tsep_1(sK0,sK0,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f313,plain,
    ( l1_pre_topc(k2_tsep_1(sK0,sK0,sK1))
    | ~ spl4_16
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f305,f151])).

fof(f305,plain,
    ( l1_pre_topc(k2_tsep_1(sK0,sK0,sK1))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_24 ),
    inference(superposition,[],[f144,f218])).

fof(f218,plain,
    ( k2_tsep_1(sK0,sK0,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f217])).

fof(f144,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f71,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t26_tmap_1.p',dt_g1_pre_topc)).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t26_tmap_1.p',dt_u1_pre_topc)).

fof(f368,plain,
    ( spl4_1
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_18
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_18
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f366,f94])).

fof(f366,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_18
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f365,f209])).

fof(f209,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl4_22
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f365,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f364,f101])).

fof(f364,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f361,f108])).

fof(f361,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(resolution,[],[f352,f115])).

fof(f352,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK0,X0)
        | v2_struct_0(X0) )
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f351,f115])).

fof(f351,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(X0) )
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f350,f94])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(X0) )
    | ~ spl4_1
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f348,f87])).

fof(f348,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(X0) )
    | ~ spl4_18 ),
    inference(resolution,[],[f192,f76])).

fof(f192,plain,
    ( r1_tsep_1(sK0,sK1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl4_18
  <=> r1_tsep_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f360,plain,
    ( spl4_1
    | spl4_3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_22
    | spl4_39 ),
    inference(avatar_contradiction_clause,[],[f359])).

fof(f359,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_22
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f358,f115])).

fof(f358,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_22
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f357,f87])).

fof(f357,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_22
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f356,f209])).

fof(f356,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f355,f94])).

fof(f355,plain,
    ( v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_6
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f354,f108])).

fof(f354,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_39 ),
    inference(duplicate_literal_removal,[],[f353])).

fof(f353,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl4_39 ),
    inference(resolution,[],[f343,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t26_tmap_1.p',dt_k2_tsep_1)).

fof(f343,plain,
    ( ~ v1_pre_topc(k2_tsep_1(sK0,sK0,sK1))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl4_39
  <=> ~ v1_pre_topc(k2_tsep_1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f347,plain,
    ( spl4_38
    | ~ spl4_16
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f311,f217,f150,f345])).

fof(f345,plain,
    ( spl4_38
  <=> v1_pre_topc(k2_tsep_1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f311,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK0,sK1))
    | ~ spl4_16
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f303,f151])).

fof(f303,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK0,sK1))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_24 ),
    inference(superposition,[],[f145,f218])).

fof(f145,plain,(
    ! [X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f71,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f340,plain,
    ( spl4_36
    | ~ spl4_33
    | ~ spl4_31
    | spl4_1
    | spl4_3
    | ~ spl4_16
    | spl4_19 ),
    inference(avatar_split_clause,[],[f267,f188,f150,f93,f86,f319,f325,f338])).

fof(f338,plain,
    ( spl4_36
  <=> k2_tsep_1(sK1,sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f325,plain,
    ( spl4_33
  <=> ~ v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f319,plain,
    ( spl4_31
  <=> ~ m1_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f188,plain,
    ( spl4_19
  <=> ~ r1_tsep_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f267,plain,
    ( ~ m1_pre_topc(sK0,sK1)
    | ~ v2_pre_topc(sK1)
    | k2_tsep_1(sK1,sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f266,f87])).

fof(f266,plain,
    ( ~ m1_pre_topc(sK0,sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | k2_tsep_1(sK1,sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f265,f94])).

fof(f265,plain,
    ( v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | k2_tsep_1(sK1,sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl4_16
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f260,f151])).

fof(f260,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | k2_tsep_1(sK1,sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl4_19 ),
    inference(resolution,[],[f175,f189])).

fof(f189,plain,
    ( ~ r1_tsep_1(sK0,sK1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f188])).

fof(f175,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | k2_tsep_1(X0,X1,X0) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | v2_struct_0(X0)
      | r1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | k2_tsep_1(X0,X1,X0) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f65,f79])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | v2_struct_0(X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X1,X2)
      | k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ( ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => m1_pre_topc(X2,X1) )
                  & ( m1_pre_topc(X2,X1)
                   => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                  & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                   => m1_pre_topc(X1,X2) )
                  & ( m1_pre_topc(X1,X2)
                   => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t26_tmap_1.p',t31_tsep_1)).

fof(f333,plain,
    ( ~ spl4_31
    | ~ spl4_33
    | spl4_34
    | spl4_1
    | ~ spl4_16
    | ~ spl4_20
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f238,f217,f194,f150,f86,f331,f325,f319])).

fof(f331,plain,
    ( spl4_34
  <=> k2_tsep_1(sK0,sK0,sK1) = k2_tsep_1(sK1,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f194,plain,
    ( spl4_20
  <=> ! [X6] :
        ( ~ v2_pre_topc(X6)
        | k2_tsep_1(X6,sK0,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(sK1,X6)
        | ~ m1_pre_topc(sK0,X6)
        | ~ l1_pre_topc(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f238,plain,
    ( k2_tsep_1(sK0,sK0,sK1) = k2_tsep_1(sK1,sK0,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_pre_topc(sK0,sK1)
    | ~ spl4_1
    | ~ spl4_16
    | ~ spl4_20
    | ~ spl4_24 ),
    inference(backward_demodulation,[],[f218,f206])).

fof(f206,plain,
    ( k2_tsep_1(sK1,sK0,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ m1_pre_topc(sK0,sK1)
    | ~ spl4_1
    | ~ spl4_16
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f205,f151])).

fof(f205,plain,
    ( k2_tsep_1(sK1,sK0,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ m1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f201,f87])).

fof(f201,plain,
    ( k2_tsep_1(sK1,sK0,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl4_20 ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,
    ( k2_tsep_1(sK1,sK0,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl4_20 ),
    inference(resolution,[],[f195,f79])).

fof(f195,plain,
    ( ! [X6] :
        ( ~ m1_pre_topc(sK1,X6)
        | k2_tsep_1(X6,sK0,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ m1_pre_topc(sK0,X6)
        | ~ l1_pre_topc(X6) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f194])).

fof(f280,plain,
    ( spl4_28
    | spl4_1
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | spl4_13 ),
    inference(avatar_split_clause,[],[f234,f128,f114,f107,f100,f93,f86,f278])).

fof(f128,plain,
    ( spl4_13
  <=> k2_tsep_1(sK0,sK1,sK1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f234,plain,
    ( r1_tsep_1(sK1,sK1)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f233,f129])).

fof(f129,plain,
    ( k2_tsep_1(sK0,sK1,sK1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f128])).

fof(f233,plain,
    ( r1_tsep_1(sK1,sK1)
    | k2_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f232,f94])).

fof(f232,plain,
    ( r1_tsep_1(sK1,sK1)
    | v2_struct_0(sK0)
    | k2_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f231,f101])).

fof(f231,plain,
    ( ~ v2_pre_topc(sK0)
    | r1_tsep_1(sK1,sK1)
    | v2_struct_0(sK0)
    | k2_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f230,f87])).

fof(f230,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | r1_tsep_1(sK1,sK1)
    | v2_struct_0(sK0)
    | k2_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f224,f108])).

fof(f224,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | r1_tsep_1(sK1,sK1)
    | v2_struct_0(sK0)
    | k2_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl4_8 ),
    inference(resolution,[],[f164,f115])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X0)
      | r1_tsep_1(X1,X1)
      | v2_struct_0(X0)
      | k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(subsumption_resolution,[],[f163,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t26_tmap_1.p',dt_m1_pre_topc)).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | r1_tsep_1(X1,X1)
      | v2_struct_0(X0)
      | k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | r1_tsep_1(X1,X1)
      | v2_struct_0(X0)
      | k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f63,f79])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f247,plain,
    ( ~ spl4_27
    | spl4_13
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f240,f217,f128,f245])).

fof(f245,plain,
    ( spl4_27
  <=> k2_tsep_1(sK0,sK0,sK1) != k2_tsep_1(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f240,plain,
    ( k2_tsep_1(sK0,sK0,sK1) != k2_tsep_1(sK0,sK1,sK1)
    | ~ spl4_13
    | ~ spl4_24 ),
    inference(backward_demodulation,[],[f218,f129])).

fof(f237,plain,
    ( ~ spl4_6
    | spl4_23 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f235,f108])).

fof(f235,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_23 ),
    inference(resolution,[],[f212,f79])).

fof(f212,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl4_23
  <=> ~ m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f219,plain,
    ( ~ spl4_23
    | spl4_24
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f204,f194,f114,f107,f100,f93,f217,f211])).

fof(f204,plain,
    ( k2_tsep_1(sK0,sK0,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f203,f108])).

fof(f203,plain,
    ( k2_tsep_1(sK0,sK0,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f202,f101])).

fof(f202,plain,
    ( k2_tsep_1(sK0,sK0,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f199,f94])).

fof(f199,plain,
    ( k2_tsep_1(sK0,sK0,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_8
    | ~ spl4_20 ),
    inference(resolution,[],[f195,f115])).

fof(f196,plain,
    ( spl4_18
    | spl4_20
    | spl4_1
    | spl4_3
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f167,f114,f93,f86,f194,f191])).

fof(f167,plain,
    ( ! [X6] :
        ( ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(sK0,X6)
        | ~ m1_pre_topc(sK1,X6)
        | r1_tsep_1(sK0,sK1)
        | v2_struct_0(X6)
        | k2_tsep_1(X6,sK0,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) )
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f166,f87])).

fof(f166,plain,
    ( ! [X6] :
        ( ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(sK0,X6)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,X6)
        | r1_tsep_1(sK0,sK1)
        | v2_struct_0(X6)
        | k2_tsep_1(X6,sK0,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) )
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f160,f94])).

fof(f160,plain,
    ( ! [X6] :
        ( ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X6)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,X6)
        | r1_tsep_1(sK0,sK1)
        | v2_struct_0(X6)
        | k2_tsep_1(X6,sK0,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) )
    | ~ spl4_8 ),
    inference(resolution,[],[f63,f115])).

fof(f152,plain,
    ( spl4_16
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f143,f114,f107,f150])).

fof(f143,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f138,f108])).

fof(f138,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f78,f115])).

fof(f137,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f68,f135])).

fof(f135,plain,
    ( spl4_14
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f68,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t26_tmap_1.p',d2_xboole_0)).

fof(f130,plain,(
    ~ spl4_13 ),
    inference(avatar_split_clause,[],[f55,f128])).

fof(f55,plain,(
    k2_tsep_1(sK0,sK1,sK1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tsep_1(X0,X1,X1) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tsep_1(X0,X1,X1) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t26_tmap_1.p',t26_tmap_1)).

fof(f123,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f80,f121])).

fof(f121,plain,
    ( spl4_10
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f80,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t26_tmap_1.p',existence_l1_pre_topc)).

fof(f116,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f54,f114])).

fof(f54,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f109,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f58,f107])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f102,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f57,f100])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f95,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f56,f93])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f53,f86])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
