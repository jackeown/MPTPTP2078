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
% DateTime   : Thu Dec  3 13:19:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  236 ( 718 expanded)
%              Number of leaves         :   32 ( 240 expanded)
%              Depth                    :   33
%              Number of atoms          : 2299 (6110 expanded)
%              Number of equality atoms :   66 ( 440 expanded)
%              Maximal formula depth    :   30 (  10 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f312,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f79,f84,f89,f94,f99,f104,f109,f114,f126,f131,f136,f148,f153,f158,f163,f168,f173,f184,f190,f268,f270,f292,f297,f303,f311])).

fof(f311,plain,
    ( spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_23
    | ~ spl8_24
    | spl8_25 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_23
    | ~ spl8_24
    | spl8_25 ),
    inference(subsumption_resolution,[],[f309,f179])).

fof(f179,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl8_24
  <=> r1_tmap_1(sK0,sK1,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f309,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_23
    | spl8_25 ),
    inference(subsumption_resolution,[],[f308,f167])).

fof(f167,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl8_22
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f308,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | spl8_25 ),
    inference(subsumption_resolution,[],[f307,f135])).

fof(f135,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl8_16
  <=> m1_subset_1(sK5,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f307,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | spl8_25 ),
    inference(subsumption_resolution,[],[f306,f162])).

fof(f162,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl8_21
  <=> m1_subset_1(sK5,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f306,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_23
    | spl8_25 ),
    inference(resolution,[],[f182,f260])).

fof(f260,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK0,sK1,sK2,X0) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f259,f113])).

fof(f113,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl8_13
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f259,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK0,sK1,sK2,X0)
        | ~ m1_pre_topc(sK3,sK0) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(superposition,[],[f253,f224])).

fof(f224,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f223,f88])).

fof(f88,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl8_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f223,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f222,f172])).

fof(f172,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl8_23
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f222,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f221,f157])).

fof(f157,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl8_20
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f221,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f220,f83])).

fof(f83,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl8_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f220,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f219,f78])).

fof(f78,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl8_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f219,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f218,f73])).

fof(f73,plain,
    ( v2_pre_topc(sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl8_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f218,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f217,f68])).

fof(f68,plain,
    ( ~ v2_struct_0(sK1)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl8_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f217,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f216,f93])).

fof(f93,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl8_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f216,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X1,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(superposition,[],[f204,f115])).

fof(f115,plain,
    ( ! [X2,X0,X1] :
        ( k2_tmap_1(X0,X1,sK2,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ m1_pre_topc(X2,X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_3 ),
    inference(resolution,[],[f63,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f63,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl8_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f204,plain,
    ( ! [X0] :
        ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f203,f88])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f202,f83])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f201,f93])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(resolution,[],[f199,f147])).

fof(f147,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl8_18
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f199,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X1,sK0)
        | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1)) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f198,f157])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X1,sK0)
        | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1)) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f197,f78])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK0,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X1,sK0)
        | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1)) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f196,f73])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK0,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X1,sK0)
        | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1)) )
    | ~ spl8_3
    | spl8_4
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f195,f68])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK0,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X1,sK0)
        | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1)) )
    | ~ spl8_3
    | ~ spl8_23 ),
    inference(resolution,[],[f119,f172])).

fof(f119,plain,
    ( ! [X21,X19,X20,X18] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X19))))
        | ~ l1_pre_topc(X18)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_pre_topc(X20,X18)
        | ~ m1_pre_topc(X21,X18)
        | v2_struct_0(X18)
        | ~ v1_funct_2(sK2,u1_struct_0(X20),u1_struct_0(X19))
        | ~ v2_pre_topc(X18)
        | ~ m1_pre_topc(X21,X20)
        | k3_tmap_1(X18,X19,X20,X21,sK2) = k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),sK2,u1_struct_0(X21)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f63,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f253,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK0,sK1,sK2,X0) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f252,f157])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0)
        | ~ r1_tmap_1(sK0,sK1,sK2,X0) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f251,f78])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0)
        | ~ r1_tmap_1(sK0,sK1,sK2,X0) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f250,f73])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0)
        | ~ r1_tmap_1(sK0,sK1,sK2,X0) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f249,f68])).

fof(f249,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0)
        | ~ r1_tmap_1(sK0,sK1,sK2,X0) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | ~ spl8_23 ),
    inference(resolution,[],[f212,f172])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1)
        | ~ r1_tmap_1(sK0,X0,sK2,X1) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f211,f88])).

fof(f211,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1)
        | ~ r1_tmap_1(sK0,X0,sK2,X1) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_7
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f210,f83])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1)
        | ~ r1_tmap_1(sK0,X0,sK2,X1) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f209,f108])).

fof(f108,plain,
    ( m1_pre_topc(sK4,sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl8_12
  <=> m1_pre_topc(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1)
        | ~ r1_tmap_1(sK0,X0,sK2,X1) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f208,f53])).

fof(f53,plain,
    ( ~ v2_struct_0(sK4)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl8_1
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1)
        | ~ r1_tmap_1(sK0,X0,sK2,X1) )
    | spl8_2
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f207,f113])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1)
        | ~ r1_tmap_1(sK0,X0,sK2,X1) )
    | spl8_2
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f206,f58])).

fof(f58,plain,
    ( ~ v2_struct_0(sK3)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl8_2
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1)
        | ~ r1_tmap_1(sK0,X0,sK2,X1) )
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f205,f93])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1)
        | ~ r1_tmap_1(sK0,X0,sK2,X1) )
    | ~ spl8_3
    | ~ spl8_19 ),
    inference(superposition,[],[f116,f152])).

fof(f152,plain,
    ( sK0 = k1_tsep_1(sK0,sK3,sK4)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl8_19
  <=> sK0 = k1_tsep_1(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f116,plain,
    ( ! [X6,X4,X7,X5,X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X5,X6)),u1_struct_0(X4))))
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X3)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X3)
        | v2_struct_0(X3)
        | ~ v1_funct_2(sK2,u1_struct_0(k1_tsep_1(X3,X5,X6)),u1_struct_0(X4))
        | ~ v2_pre_topc(X3)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X5,X6)))
        | r1_tmap_1(X5,X4,k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X5,sK2),X7)
        | ~ r1_tmap_1(k1_tsep_1(X3,X5,X6),X4,sK2,X7) )
    | ~ spl8_3 ),
    inference(resolution,[],[f63,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | X6 != X7
      | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | X5 != X7
      | X6 != X7
      | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
                                  <=> ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
                                      & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) ) )
                                  | X6 != X7
                                  | X5 != X7
                                  | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
                                  <=> ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
                                      & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) ) )
                                  | X6 != X7
                                  | X5 != X7
                                  | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
                                 => ( ( X6 = X7
                                      & X5 = X7 )
                                   => ( r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)
                                    <=> ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
                                        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_tmap_1)).

fof(f182,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | spl8_25 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl8_25
  <=> r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f303,plain,
    ( ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_25
    | spl8_28 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_25
    | spl8_28 ),
    inference(subsumption_resolution,[],[f301,f113])).

fof(f301,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_25
    | spl8_28 ),
    inference(subsumption_resolution,[],[f300,f183])).

fof(f183,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f181])).

fof(f300,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23
    | spl8_28 ),
    inference(superposition,[],[f291,f224])).

fof(f291,plain,
    ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5)
    | spl8_28 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl8_28
  <=> r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f297,plain,
    ( ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_26
    | spl8_27 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_26
    | spl8_27 ),
    inference(subsumption_resolution,[],[f295,f108])).

fof(f295,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_26
    | spl8_27 ),
    inference(subsumption_resolution,[],[f294,f189])).

fof(f189,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl8_26
  <=> r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f294,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_23
    | spl8_27 ),
    inference(superposition,[],[f287,f224])).

fof(f287,plain,
    ( ~ r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5)
    | spl8_27 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl8_27
  <=> r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f292,plain,
    ( ~ spl8_27
    | ~ spl8_28
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_23
    | spl8_24 ),
    inference(avatar_split_clause,[],[f283,f177,f170,f165,f160,f155,f150,f133,f111,f106,f91,f86,f81,f76,f71,f66,f61,f56,f51,f289,f285])).

fof(f283,plain,
    ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5)
    | ~ r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5)
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_23
    | spl8_24 ),
    inference(subsumption_resolution,[],[f282,f172])).

fof(f282,plain,
    ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5)
    | ~ r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | spl8_24 ),
    inference(subsumption_resolution,[],[f281,f135])).

fof(f281,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5)
    | ~ r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | spl8_24 ),
    inference(subsumption_resolution,[],[f280,f162])).

fof(f280,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5)
    | ~ r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_22
    | spl8_24 ),
    inference(subsumption_resolution,[],[f279,f167])).

fof(f279,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5)
    | ~ r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | ~ spl8_20
    | spl8_24 ),
    inference(subsumption_resolution,[],[f278,f157])).

fof(f278,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5)
    | ~ r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | spl8_24 ),
    inference(subsumption_resolution,[],[f277,f78])).

fof(f277,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5)
    | ~ r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | spl8_24 ),
    inference(subsumption_resolution,[],[f276,f73])).

fof(f276,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5)
    | ~ r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | spl8_24 ),
    inference(subsumption_resolution,[],[f275,f68])).

fof(f275,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5)
    | ~ r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | spl8_24 ),
    inference(resolution,[],[f178,f248])).

fof(f248,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(sK0,X0,sK2,X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1)
        | ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f247,f88])).

fof(f247,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1)
        | ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1)
        | r1_tmap_1(sK0,X0,sK2,X1) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_7
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f246,f83])).

fof(f246,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1)
        | ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1)
        | r1_tmap_1(sK0,X0,sK2,X1) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f245,f108])).

fof(f245,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1)
        | ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1)
        | r1_tmap_1(sK0,X0,sK2,X1) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f244,f53])).

fof(f244,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1)
        | ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1)
        | r1_tmap_1(sK0,X0,sK2,X1) )
    | spl8_2
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f243,f113])).

fof(f243,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1)
        | ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1)
        | r1_tmap_1(sK0,X0,sK2,X1) )
    | spl8_2
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f242,f58])).

fof(f242,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1)
        | ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1)
        | r1_tmap_1(sK0,X0,sK2,X1) )
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f241,f93])).

fof(f241,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1)
        | ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1)
        | r1_tmap_1(sK0,X0,sK2,X1) )
    | ~ spl8_3
    | ~ spl8_19 ),
    inference(superposition,[],[f118,f152])).

fof(f118,plain,
    ( ! [X14,X17,X15,X13,X16] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X13,X15,X16)),u1_struct_0(X14))))
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X13)
        | v2_struct_0(X13)
        | ~ v1_funct_2(sK2,u1_struct_0(k1_tsep_1(X13,X15,X16)),u1_struct_0(X14))
        | ~ v2_pre_topc(X13)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(k1_tsep_1(X13,X15,X16)))
        | ~ r1_tmap_1(X15,X14,k3_tmap_1(X13,X14,k1_tsep_1(X13,X15,X16),X15,sK2),X17)
        | ~ r1_tmap_1(X16,X14,k3_tmap_1(X13,X14,k1_tsep_1(X13,X15,X16),X16,sK2),X17)
        | r1_tmap_1(k1_tsep_1(X13,X15,X16),X14,sK2,X17) )
    | ~ spl8_3 ),
    inference(resolution,[],[f63,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7)
      | r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | X6 != X7
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
      | r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | X5 != X7
      | X6 != X7
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5)
      | ~ r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
      | r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f178,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | spl8_24 ),
    inference(avatar_component_clause,[],[f177])).

fof(f270,plain,
    ( ~ spl8_10
    | ~ spl8_11
    | ~ spl8_24
    | ~ spl8_25
    | ~ spl8_26 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_24
    | ~ spl8_25
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f194,f189])).

fof(f194,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f193,f103])).

fof(f103,plain,
    ( sK5 = sK7
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl8_11
  <=> sK5 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f193,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ spl8_10
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f192,f183])).

fof(f192,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ spl8_10
    | ~ spl8_24 ),
    inference(forward_demodulation,[],[f191,f98])).

fof(f98,plain,
    ( sK5 = sK6
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl8_10
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f191,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f16,f179])).

fof(f16,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X0,X1,X2,X5)
                                  <~> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X0,X1,X2,X5)
                                  <~> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( k1_tsep_1(X0,X3,X4) = X0
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X4))
                                     => ( ( X5 = X7
                                          & X5 = X6 )
                                       => ( r1_tmap_1(X0,X1,X2,X5)
                                        <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                            & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( k1_tsep_1(X0,X3,X4) = X0
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X4))
                                   => ( ( X5 = X7
                                        & X5 = X6 )
                                     => ( r1_tmap_1(X0,X1,X2,X5)
                                      <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                          & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_tmap_1)).

fof(f268,plain,
    ( spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_23
    | ~ spl8_24
    | spl8_26 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_23
    | ~ spl8_24
    | spl8_26 ),
    inference(subsumption_resolution,[],[f266,f179])).

fof(f266,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_23
    | spl8_26 ),
    inference(subsumption_resolution,[],[f265,f167])).

fof(f265,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | spl8_26 ),
    inference(subsumption_resolution,[],[f264,f135])).

fof(f264,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | spl8_26 ),
    inference(subsumption_resolution,[],[f263,f162])).

fof(f263,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_23
    | spl8_26 ),
    inference(resolution,[],[f262,f188])).

fof(f188,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | spl8_26 ),
    inference(avatar_component_clause,[],[f187])).

fof(f262,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK0,sK1,sK2,X0) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f261,f108])).

fof(f261,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK0,sK1,sK2,X0)
        | ~ m1_pre_topc(sK4,sK0) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(superposition,[],[f258,f224])).

fof(f258,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK0,sK1,sK2,X0) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f257,f157])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0)
        | ~ r1_tmap_1(sK0,sK1,sK2,X0) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f256,f78])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0)
        | ~ r1_tmap_1(sK0,sK1,sK2,X0) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f255,f73])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0)
        | ~ r1_tmap_1(sK0,sK1,sK2,X0) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_4
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f254,f68])).

fof(f254,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0)
        | ~ r1_tmap_1(sK0,sK1,sK2,X0) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | ~ spl8_23 ),
    inference(resolution,[],[f240,f172])).

fof(f240,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1)
        | ~ r1_tmap_1(sK0,X0,sK2,X1) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f239,f88])).

fof(f239,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1)
        | ~ r1_tmap_1(sK0,X0,sK2,X1) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | spl8_7
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f238,f83])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1)
        | ~ r1_tmap_1(sK0,X0,sK2,X1) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f237,f108])).

fof(f237,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1)
        | ~ r1_tmap_1(sK0,X0,sK2,X1) )
    | spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f236,f53])).

fof(f236,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1)
        | ~ r1_tmap_1(sK0,X0,sK2,X1) )
    | spl8_2
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f235,f113])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1)
        | ~ r1_tmap_1(sK0,X0,sK2,X1) )
    | spl8_2
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f234,f58])).

fof(f234,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1)
        | ~ r1_tmap_1(sK0,X0,sK2,X1) )
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f233,f93])).

fof(f233,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1)
        | ~ r1_tmap_1(sK0,X0,sK2,X1) )
    | ~ spl8_3
    | ~ spl8_19 ),
    inference(superposition,[],[f117,f152])).

fof(f117,plain,
    ( ! [X12,X10,X8,X11,X9] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X8,X10,X11)),u1_struct_0(X9))))
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X8)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X8)
        | v2_struct_0(X8)
        | ~ v1_funct_2(sK2,u1_struct_0(k1_tsep_1(X8,X10,X11)),u1_struct_0(X9))
        | ~ v2_pre_topc(X8)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ m1_subset_1(X12,u1_struct_0(k1_tsep_1(X8,X10,X11)))
        | r1_tmap_1(X11,X9,k3_tmap_1(X8,X9,k1_tsep_1(X8,X10,X11),X11,sK2),X12)
        | ~ r1_tmap_1(k1_tsep_1(X8,X10,X11),X9,sK2,X12) )
    | ~ spl8_3 ),
    inference(resolution,[],[f63,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | X6 != X7
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))
      | X5 != X7
      | X6 != X7
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6)
      | ~ r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f190,plain,
    ( spl8_26
    | ~ spl8_11
    | spl8_24 ),
    inference(avatar_split_clause,[],[f185,f177,f101,f187])).

fof(f185,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | ~ spl8_11
    | spl8_24 ),
    inference(subsumption_resolution,[],[f175,f178])).

fof(f175,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f18,f103])).

fof(f18,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f8])).

fof(f184,plain,
    ( spl8_24
    | spl8_25
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f174,f96,f181,f177])).

fof(f174,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f17,f98])).

fof(f17,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f8])).

fof(f173,plain,(
    spl8_23 ),
    inference(avatar_split_clause,[],[f31,f170])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f168,plain,
    ( spl8_22
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f143,f128,f96,f165])).

fof(f128,plain,
    ( spl8_15
  <=> m1_subset_1(sK6,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f143,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f130,f98])).

fof(f130,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f128])).

fof(f163,plain,
    ( spl8_21
    | ~ spl8_11
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f137,f123,f101,f160])).

fof(f123,plain,
    ( spl8_14
  <=> m1_subset_1(sK7,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f137,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ spl8_11
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f125,f103])).

fof(f125,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f123])).

fof(f158,plain,(
    spl8_20 ),
    inference(avatar_split_clause,[],[f30,f155])).

fof(f30,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f153,plain,(
    spl8_19 ),
    inference(avatar_split_clause,[],[f26,f150])).

fof(f26,plain,(
    sK0 = k1_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f8])).

fof(f148,plain,
    ( spl8_18
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f121,f91,f145])).

fof(f121,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl8_9 ),
    inference(resolution,[],[f93,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f136,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f23,f133])).

fof(f23,plain,(
    m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f131,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f22,f128])).

fof(f22,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f126,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f19,f123])).

fof(f19,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f8])).

fof(f114,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f28,f111])).

fof(f28,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f109,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f25,f106])).

fof(f25,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f104,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f21,f101])).

fof(f21,plain,(
    sK5 = sK7 ),
    inference(cnf_transformation,[],[f8])).

fof(f99,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f20,f96])).

fof(f20,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f8])).

fof(f94,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f37,f91])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f89,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f36,f86])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f84,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f35,f81])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f79,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f34,f76])).

fof(f34,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f74,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f33,f71])).

fof(f33,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f69,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f32,f66])).

fof(f32,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f64,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f29,f61])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

% (30962)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f59,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f27,f56])).

fof(f27,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (30964)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.44  % (30980)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.45  % (30964)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f312,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f79,f84,f89,f94,f99,f104,f109,f114,f126,f131,f136,f148,f153,f158,f163,f168,f173,f184,f190,f268,f270,f292,f297,f303,f311])).
% 0.21/0.45  fof(f311,plain,(
% 0.21/0.45    spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_16 | ~spl8_18 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_22 | ~spl8_23 | ~spl8_24 | spl8_25),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f310])).
% 0.21/0.45  fof(f310,plain,(
% 0.21/0.45    $false | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_16 | ~spl8_18 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_22 | ~spl8_23 | ~spl8_24 | spl8_25)),
% 0.21/0.45    inference(subsumption_resolution,[],[f309,f179])).
% 0.21/0.45  fof(f179,plain,(
% 0.21/0.45    r1_tmap_1(sK0,sK1,sK2,sK5) | ~spl8_24),
% 0.21/0.45    inference(avatar_component_clause,[],[f177])).
% 0.21/0.45  fof(f177,plain,(
% 0.21/0.45    spl8_24 <=> r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.21/0.45  fof(f309,plain,(
% 0.21/0.45    ~r1_tmap_1(sK0,sK1,sK2,sK5) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_16 | ~spl8_18 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_22 | ~spl8_23 | spl8_25)),
% 0.21/0.45    inference(subsumption_resolution,[],[f308,f167])).
% 0.21/0.45  fof(f167,plain,(
% 0.21/0.45    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl8_22),
% 0.21/0.45    inference(avatar_component_clause,[],[f165])).
% 0.21/0.45  fof(f165,plain,(
% 0.21/0.45    spl8_22 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.21/0.45  fof(f308,plain,(
% 0.21/0.45    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_16 | ~spl8_18 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_23 | spl8_25)),
% 0.21/0.45    inference(subsumption_resolution,[],[f307,f135])).
% 0.21/0.45  fof(f135,plain,(
% 0.21/0.45    m1_subset_1(sK5,u1_struct_0(sK0)) | ~spl8_16),
% 0.21/0.45    inference(avatar_component_clause,[],[f133])).
% 0.21/0.45  fof(f133,plain,(
% 0.21/0.45    spl8_16 <=> m1_subset_1(sK5,u1_struct_0(sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.45  fof(f307,plain,(
% 0.21/0.45    ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_18 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_23 | spl8_25)),
% 0.21/0.45    inference(subsumption_resolution,[],[f306,f162])).
% 0.21/0.45  fof(f162,plain,(
% 0.21/0.45    m1_subset_1(sK5,u1_struct_0(sK4)) | ~spl8_21),
% 0.21/0.45    inference(avatar_component_clause,[],[f160])).
% 0.21/0.45  fof(f160,plain,(
% 0.21/0.45    spl8_21 <=> m1_subset_1(sK5,u1_struct_0(sK4))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.45  fof(f306,plain,(
% 0.21/0.45    ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_18 | ~spl8_19 | ~spl8_20 | ~spl8_23 | spl8_25)),
% 0.21/0.45    inference(resolution,[],[f182,f260])).
% 0.21/0.45  fof(f260,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK0,sK1,sK2,X0)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_18 | ~spl8_19 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f259,f113])).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    m1_pre_topc(sK3,sK0) | ~spl8_13),
% 0.21/0.45    inference(avatar_component_clause,[],[f111])).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    spl8_13 <=> m1_pre_topc(sK3,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.45  fof(f259,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK0,sK1,sK2,X0) | ~m1_pre_topc(sK3,sK0)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_18 | ~spl8_19 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(superposition,[],[f253,f224])).
% 0.21/0.45  fof(f224,plain,(
% 0.21/0.45    ( ! [X1] : (k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2) | ~m1_pre_topc(X1,sK0)) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f223,f88])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    v2_pre_topc(sK0) | ~spl8_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f86])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    spl8_8 <=> v2_pre_topc(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.45  fof(f223,plain,(
% 0.21/0.45    ( ! [X1] : (k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2) | ~m1_pre_topc(X1,sK0) | ~v2_pre_topc(sK0)) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f222,f172])).
% 0.21/0.45  fof(f172,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl8_23),
% 0.21/0.45    inference(avatar_component_clause,[],[f170])).
% 0.21/0.45  fof(f170,plain,(
% 0.21/0.45    spl8_23 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.45  fof(f222,plain,(
% 0.21/0.45    ( ! [X1] : (k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2) | ~m1_pre_topc(X1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0)) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f221,f157])).
% 0.21/0.45  fof(f157,plain,(
% 0.21/0.45    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl8_20),
% 0.21/0.45    inference(avatar_component_clause,[],[f155])).
% 0.21/0.45  fof(f155,plain,(
% 0.21/0.45    spl8_20 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.45  fof(f221,plain,(
% 0.21/0.45    ( ! [X1] : (k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2) | ~m1_pre_topc(X1,sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0)) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f220,f83])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    ~v2_struct_0(sK0) | spl8_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f81])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    spl8_7 <=> v2_struct_0(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.45  fof(f220,plain,(
% 0.21/0.45    ( ! [X1] : (k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0)) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f219,f78])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    l1_pre_topc(sK1) | ~spl8_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f76])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    spl8_6 <=> l1_pre_topc(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.45  fof(f219,plain,(
% 0.21/0.45    ( ! [X1] : (k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0)) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f218,f73])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    v2_pre_topc(sK1) | ~spl8_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f71])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    spl8_5 <=> v2_pre_topc(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.45  fof(f218,plain,(
% 0.21/0.45    ( ! [X1] : (k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2) | ~m1_pre_topc(X1,sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0)) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f217,f68])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    ~v2_struct_0(sK1) | spl8_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f66])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    spl8_4 <=> v2_struct_0(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.45  fof(f217,plain,(
% 0.21/0.45    ( ! [X1] : (k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2) | ~m1_pre_topc(X1,sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0)) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f216,f93])).
% 0.21/0.45  fof(f93,plain,(
% 0.21/0.45    l1_pre_topc(sK0) | ~spl8_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f91])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    spl8_9 <=> l1_pre_topc(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.45  fof(f216,plain,(
% 0.21/0.45    ( ! [X1] : (k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0)) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f213])).
% 0.21/0.45  fof(f213,plain,(
% 0.21/0.45    ( ! [X1] : (k2_tmap_1(sK0,sK1,sK2,X1) = k3_tmap_1(sK0,sK1,sK0,X1,sK2) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK0) | ~v2_pre_topc(sK0)) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(superposition,[],[f204,f115])).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k2_tmap_1(X0,X1,sK2,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK2,u1_struct_0(X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X0) | ~v2_pre_topc(X0)) ) | ~spl8_3),
% 0.21/0.45    inference(resolution,[],[f63,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    v1_funct_1(sK2) | ~spl8_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f61])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    spl8_3 <=> v1_funct_1(sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.45  fof(f204,plain,(
% 0.21/0.45    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2) | ~m1_pre_topc(X0,sK0)) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f203,f88])).
% 0.21/0.45  fof(f203,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~v2_pre_topc(sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_9 | ~spl8_18 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f202,f83])).
% 0.21/0.45  fof(f202,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_9 | ~spl8_18 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f201,f93])).
% 0.21/0.45  fof(f201,plain,(
% 0.21/0.45    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_18 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f200])).
% 0.21/0.45  fof(f200,plain,(
% 0.21/0.45    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK0,X0,sK2)) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_18 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(resolution,[],[f199,f147])).
% 0.21/0.45  fof(f147,plain,(
% 0.21/0.45    m1_pre_topc(sK0,sK0) | ~spl8_18),
% 0.21/0.45    inference(avatar_component_clause,[],[f145])).
% 0.21/0.45  fof(f145,plain,(
% 0.21/0.45    spl8_18 <=> m1_pre_topc(sK0,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.45  fof(f199,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1))) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f198,f157])).
% 0.21/0.45  fof(f198,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1))) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f197,f78])).
% 0.21/0.45  fof(f197,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1))) ) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f196,f73])).
% 0.21/0.45  fof(f196,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1))) ) | (~spl8_3 | spl8_4 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f195,f68])).
% 0.21/0.45  fof(f195,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(X0,sK1,sK0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X1))) ) | (~spl8_3 | ~spl8_23)),
% 0.21/0.45    inference(resolution,[],[f119,f172])).
% 0.21/0.45  fof(f119,plain,(
% 0.21/0.45    ( ! [X21,X19,X20,X18] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X19)))) | ~l1_pre_topc(X18) | v2_struct_0(X19) | ~v2_pre_topc(X19) | ~l1_pre_topc(X19) | ~m1_pre_topc(X20,X18) | ~m1_pre_topc(X21,X18) | v2_struct_0(X18) | ~v1_funct_2(sK2,u1_struct_0(X20),u1_struct_0(X19)) | ~v2_pre_topc(X18) | ~m1_pre_topc(X21,X20) | k3_tmap_1(X18,X19,X20,X21,sK2) = k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),sK2,u1_struct_0(X21))) ) | ~spl8_3),
% 0.21/0.45    inference(resolution,[],[f63,f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.21/0.45  fof(f253,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK0,sK1,sK2,X0)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19 | ~spl8_20 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f252,f157])).
% 0.21/0.45  fof(f252,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0) | ~r1_tmap_1(sK0,sK1,sK2,X0)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f251,f78])).
% 0.21/0.45  fof(f251,plain,(
% 0.21/0.45    ( ! [X0] : (~l1_pre_topc(sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0) | ~r1_tmap_1(sK0,sK1,sK2,X0)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f250,f73])).
% 0.21/0.45  fof(f250,plain,(
% 0.21/0.45    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0) | ~r1_tmap_1(sK0,sK1,sK2,X0)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19 | ~spl8_23)),
% 0.21/0.45    inference(subsumption_resolution,[],[f249,f68])).
% 0.21/0.45  fof(f249,plain,(
% 0.21/0.45    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),X0) | ~r1_tmap_1(sK0,sK1,sK2,X0)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19 | ~spl8_23)),
% 0.21/0.45    inference(resolution,[],[f212,f172])).
% 0.21/0.45  fof(f212,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1) | ~r1_tmap_1(sK0,X0,sK2,X1)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19)),
% 0.21/0.45    inference(subsumption_resolution,[],[f211,f88])).
% 0.21/0.45  fof(f211,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1) | ~r1_tmap_1(sK0,X0,sK2,X1)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_7 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19)),
% 0.21/0.45    inference(subsumption_resolution,[],[f210,f83])).
% 0.21/0.45  fof(f210,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1) | ~r1_tmap_1(sK0,X0,sK2,X1)) ) | (spl8_1 | spl8_2 | ~spl8_3 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19)),
% 0.21/0.45    inference(subsumption_resolution,[],[f209,f108])).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    m1_pre_topc(sK4,sK0) | ~spl8_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f106])).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    spl8_12 <=> m1_pre_topc(sK4,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.45  fof(f209,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1) | ~r1_tmap_1(sK0,X0,sK2,X1)) ) | (spl8_1 | spl8_2 | ~spl8_3 | ~spl8_9 | ~spl8_13 | ~spl8_19)),
% 0.21/0.45    inference(subsumption_resolution,[],[f208,f53])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    ~v2_struct_0(sK4) | spl8_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f51])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    spl8_1 <=> v2_struct_0(sK4)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.45  fof(f208,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1) | ~r1_tmap_1(sK0,X0,sK2,X1)) ) | (spl8_2 | ~spl8_3 | ~spl8_9 | ~spl8_13 | ~spl8_19)),
% 0.21/0.45    inference(subsumption_resolution,[],[f207,f113])).
% 0.21/0.45  fof(f207,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1) | ~r1_tmap_1(sK0,X0,sK2,X1)) ) | (spl8_2 | ~spl8_3 | ~spl8_9 | ~spl8_19)),
% 0.21/0.45    inference(subsumption_resolution,[],[f206,f58])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    ~v2_struct_0(sK3) | spl8_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f56])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    spl8_2 <=> v2_struct_0(sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.45  fof(f206,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1) | ~r1_tmap_1(sK0,X0,sK2,X1)) ) | (~spl8_3 | ~spl8_9 | ~spl8_19)),
% 0.21/0.45    inference(subsumption_resolution,[],[f205,f93])).
% 0.21/0.45  fof(f205,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1) | ~r1_tmap_1(sK0,X0,sK2,X1)) ) | (~spl8_3 | ~spl8_19)),
% 0.21/0.45    inference(superposition,[],[f116,f152])).
% 0.21/0.45  fof(f152,plain,(
% 0.21/0.45    sK0 = k1_tsep_1(sK0,sK3,sK4) | ~spl8_19),
% 0.21/0.45    inference(avatar_component_clause,[],[f150])).
% 0.21/0.45  fof(f150,plain,(
% 0.21/0.45    spl8_19 <=> sK0 = k1_tsep_1(sK0,sK3,sK4)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.45  fof(f116,plain,(
% 0.21/0.45    ( ! [X6,X4,X7,X5,X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X5,X6)),u1_struct_0(X4)))) | ~l1_pre_topc(X3) | v2_struct_0(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,X3) | v2_struct_0(X6) | ~m1_pre_topc(X6,X3) | v2_struct_0(X3) | ~v1_funct_2(sK2,u1_struct_0(k1_tsep_1(X3,X5,X6)),u1_struct_0(X4)) | ~v2_pre_topc(X3) | ~m1_subset_1(X7,u1_struct_0(X5)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X5,X6))) | r1_tmap_1(X5,X4,k3_tmap_1(X3,X4,k1_tsep_1(X3,X5,X6),X5,sK2),X7) | ~r1_tmap_1(k1_tsep_1(X3,X5,X6),X4,sK2,X7)) ) | ~spl8_3),
% 0.21/0.45    inference(resolution,[],[f63,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X7,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)) )),
% 0.21/0.46    inference(equality_resolution,[],[f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X6,X4,X2,X0,X7,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | X6 != X7 | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)) )),
% 0.21/0.46    inference(equality_resolution,[],[f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | X5 != X7 | X6 != X7 | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) <=> (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5))) | X6 != X7 | X5 != X7 | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) <=> (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5))) | (X6 != X7 | X5 != X7)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) => ((X6 = X7 & X5 = X7) => (r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7) <=> (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5))))))))))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_tmap_1)).
% 0.21/0.46  fof(f182,plain,(
% 0.21/0.46    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | spl8_25),
% 0.21/0.46    inference(avatar_component_clause,[],[f181])).
% 0.21/0.46  fof(f181,plain,(
% 0.21/0.46    spl8_25 <=> r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.46  fof(f303,plain,(
% 0.21/0.46    ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_13 | ~spl8_18 | ~spl8_20 | ~spl8_23 | ~spl8_25 | spl8_28),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f302])).
% 0.21/0.46  fof(f302,plain,(
% 0.21/0.46    $false | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_13 | ~spl8_18 | ~spl8_20 | ~spl8_23 | ~spl8_25 | spl8_28)),
% 0.21/0.46    inference(subsumption_resolution,[],[f301,f113])).
% 0.21/0.46  fof(f301,plain,(
% 0.21/0.46    ~m1_pre_topc(sK3,sK0) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_20 | ~spl8_23 | ~spl8_25 | spl8_28)),
% 0.21/0.46    inference(subsumption_resolution,[],[f300,f183])).
% 0.21/0.46  fof(f183,plain,(
% 0.21/0.46    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~spl8_25),
% 0.21/0.46    inference(avatar_component_clause,[],[f181])).
% 0.21/0.46  fof(f300,plain,(
% 0.21/0.46    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~m1_pre_topc(sK3,sK0) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_20 | ~spl8_23 | spl8_28)),
% 0.21/0.46    inference(superposition,[],[f291,f224])).
% 0.21/0.46  fof(f291,plain,(
% 0.21/0.46    ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5) | spl8_28),
% 0.21/0.46    inference(avatar_component_clause,[],[f289])).
% 0.21/0.46  fof(f289,plain,(
% 0.21/0.46    spl8_28 <=> r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.21/0.46  fof(f297,plain,(
% 0.21/0.46    ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_18 | ~spl8_20 | ~spl8_23 | ~spl8_26 | spl8_27),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f296])).
% 0.21/0.46  fof(f296,plain,(
% 0.21/0.46    $false | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_18 | ~spl8_20 | ~spl8_23 | ~spl8_26 | spl8_27)),
% 0.21/0.46    inference(subsumption_resolution,[],[f295,f108])).
% 0.21/0.46  fof(f295,plain,(
% 0.21/0.46    ~m1_pre_topc(sK4,sK0) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_20 | ~spl8_23 | ~spl8_26 | spl8_27)),
% 0.21/0.46    inference(subsumption_resolution,[],[f294,f189])).
% 0.21/0.46  fof(f189,plain,(
% 0.21/0.46    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | ~spl8_26),
% 0.21/0.46    inference(avatar_component_clause,[],[f187])).
% 0.21/0.46  fof(f187,plain,(
% 0.21/0.46    spl8_26 <=> r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.21/0.46  fof(f294,plain,(
% 0.21/0.46    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | ~m1_pre_topc(sK4,sK0) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_20 | ~spl8_23 | spl8_27)),
% 0.21/0.46    inference(superposition,[],[f287,f224])).
% 0.21/0.46  fof(f287,plain,(
% 0.21/0.46    ~r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5) | spl8_27),
% 0.21/0.46    inference(avatar_component_clause,[],[f285])).
% 0.21/0.46  fof(f285,plain,(
% 0.21/0.46    spl8_27 <=> r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.21/0.46  fof(f292,plain,(
% 0.21/0.46    ~spl8_27 | ~spl8_28 | spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_16 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_22 | ~spl8_23 | spl8_24),
% 0.21/0.46    inference(avatar_split_clause,[],[f283,f177,f170,f165,f160,f155,f150,f133,f111,f106,f91,f86,f81,f76,f71,f66,f61,f56,f51,f289,f285])).
% 0.21/0.46  fof(f283,plain,(
% 0.21/0.46    ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5) | ~r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_16 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_22 | ~spl8_23 | spl8_24)),
% 0.21/0.46    inference(subsumption_resolution,[],[f282,f172])).
% 0.21/0.46  fof(f282,plain,(
% 0.21/0.46    ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5) | ~r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_16 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_22 | spl8_24)),
% 0.21/0.46    inference(subsumption_resolution,[],[f281,f135])).
% 0.21/0.46  fof(f281,plain,(
% 0.21/0.46    ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5) | ~r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_22 | spl8_24)),
% 0.21/0.46    inference(subsumption_resolution,[],[f280,f162])).
% 0.21/0.46  fof(f280,plain,(
% 0.21/0.46    ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5) | ~r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19 | ~spl8_20 | ~spl8_22 | spl8_24)),
% 0.21/0.46    inference(subsumption_resolution,[],[f279,f167])).
% 0.21/0.46  fof(f279,plain,(
% 0.21/0.46    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5) | ~r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19 | ~spl8_20 | spl8_24)),
% 0.21/0.46    inference(subsumption_resolution,[],[f278,f157])).
% 0.21/0.46  fof(f278,plain,(
% 0.21/0.46    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5) | ~r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19 | spl8_24)),
% 0.21/0.46    inference(subsumption_resolution,[],[f277,f78])).
% 0.21/0.46  fof(f277,plain,(
% 0.21/0.46    ~l1_pre_topc(sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5) | ~r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19 | spl8_24)),
% 0.21/0.46    inference(subsumption_resolution,[],[f276,f73])).
% 0.21/0.46  fof(f276,plain,(
% 0.21/0.46    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5) | ~r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19 | spl8_24)),
% 0.21/0.46    inference(subsumption_resolution,[],[f275,f68])).
% 0.21/0.46  fof(f275,plain,(
% 0.21/0.46    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK5) | ~r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),sK5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19 | spl8_24)),
% 0.21/0.46    inference(resolution,[],[f178,f248])).
% 0.21/0.46  fof(f248,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tmap_1(sK0,X0,sK2,X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1) | ~r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f247,f88])).
% 0.21/0.46  fof(f247,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1) | ~r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1) | r1_tmap_1(sK0,X0,sK2,X1)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_7 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f246,f83])).
% 0.21/0.46  fof(f246,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1) | ~r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1) | r1_tmap_1(sK0,X0,sK2,X1)) ) | (spl8_1 | spl8_2 | ~spl8_3 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f245,f108])).
% 0.21/0.46  fof(f245,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1) | ~r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1) | r1_tmap_1(sK0,X0,sK2,X1)) ) | (spl8_1 | spl8_2 | ~spl8_3 | ~spl8_9 | ~spl8_13 | ~spl8_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f244,f53])).
% 0.21/0.46  fof(f244,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1) | ~r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1) | r1_tmap_1(sK0,X0,sK2,X1)) ) | (spl8_2 | ~spl8_3 | ~spl8_9 | ~spl8_13 | ~spl8_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f243,f113])).
% 0.21/0.46  fof(f243,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1) | ~r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1) | r1_tmap_1(sK0,X0,sK2,X1)) ) | (spl8_2 | ~spl8_3 | ~spl8_9 | ~spl8_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f242,f58])).
% 0.21/0.46  fof(f242,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1) | ~r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1) | r1_tmap_1(sK0,X0,sK2,X1)) ) | (~spl8_3 | ~spl8_9 | ~spl8_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f241,f93])).
% 0.21/0.46  fof(f241,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_tmap_1(sK3,X0,k3_tmap_1(sK0,X0,sK0,sK3,sK2),X1) | ~r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1) | r1_tmap_1(sK0,X0,sK2,X1)) ) | (~spl8_3 | ~spl8_19)),
% 0.21/0.46    inference(superposition,[],[f118,f152])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    ( ! [X14,X17,X15,X13,X16] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X13,X15,X16)),u1_struct_0(X14)))) | ~l1_pre_topc(X13) | v2_struct_0(X14) | ~v2_pre_topc(X14) | ~l1_pre_topc(X14) | v2_struct_0(X15) | ~m1_pre_topc(X15,X13) | v2_struct_0(X16) | ~m1_pre_topc(X16,X13) | v2_struct_0(X13) | ~v1_funct_2(sK2,u1_struct_0(k1_tsep_1(X13,X15,X16)),u1_struct_0(X14)) | ~v2_pre_topc(X13) | ~m1_subset_1(X17,u1_struct_0(X15)) | ~m1_subset_1(X17,u1_struct_0(X16)) | ~m1_subset_1(X17,u1_struct_0(k1_tsep_1(X13,X15,X16))) | ~r1_tmap_1(X15,X14,k3_tmap_1(X13,X14,k1_tsep_1(X13,X15,X16),X15,sK2),X17) | ~r1_tmap_1(X16,X14,k3_tmap_1(X13,X14,k1_tsep_1(X13,X15,X16),X16,sK2),X17) | r1_tmap_1(k1_tsep_1(X13,X15,X16),X14,sK2,X17)) ) | ~spl8_3),
% 0.21/0.46    inference(resolution,[],[f63,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X7,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7) | ~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7) | r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)) )),
% 0.21/0.46    inference(equality_resolution,[],[f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X6,X4,X2,X0,X7,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | X6 != X7 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X7) | ~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) | r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)) )),
% 0.21/0.46    inference(equality_resolution,[],[f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | X5 != X7 | X6 != X7 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X5) | ~r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) | r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f178,plain,(
% 0.21/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | spl8_24),
% 0.21/0.46    inference(avatar_component_clause,[],[f177])).
% 0.21/0.46  fof(f270,plain,(
% 0.21/0.46    ~spl8_10 | ~spl8_11 | ~spl8_24 | ~spl8_25 | ~spl8_26),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f269])).
% 0.21/0.46  fof(f269,plain,(
% 0.21/0.46    $false | (~spl8_10 | ~spl8_11 | ~spl8_24 | ~spl8_25 | ~spl8_26)),
% 0.21/0.46    inference(subsumption_resolution,[],[f194,f189])).
% 0.21/0.46  fof(f194,plain,(
% 0.21/0.46    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | (~spl8_10 | ~spl8_11 | ~spl8_24 | ~spl8_25)),
% 0.21/0.46    inference(forward_demodulation,[],[f193,f103])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    sK5 = sK7 | ~spl8_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f101])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl8_11 <=> sK5 = sK7),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.46  fof(f193,plain,(
% 0.21/0.46    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | (~spl8_10 | ~spl8_24 | ~spl8_25)),
% 0.21/0.46    inference(subsumption_resolution,[],[f192,f183])).
% 0.21/0.46  fof(f192,plain,(
% 0.21/0.46    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | (~spl8_10 | ~spl8_24)),
% 0.21/0.46    inference(forward_demodulation,[],[f191,f98])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    sK5 = sK6 | ~spl8_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f96])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    spl8_10 <=> sK5 = sK6),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.46  fof(f191,plain,(
% 0.21/0.46    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~spl8_24),
% 0.21/0.46    inference(subsumption_resolution,[],[f16,f179])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & (X5 = X7 & X5 = X6)) & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_tmap_1)).
% 0.21/0.46  fof(f268,plain,(
% 0.21/0.46    spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_16 | ~spl8_18 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_22 | ~spl8_23 | ~spl8_24 | spl8_26),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f267])).
% 0.21/0.46  fof(f267,plain,(
% 0.21/0.46    $false | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_16 | ~spl8_18 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_22 | ~spl8_23 | ~spl8_24 | spl8_26)),
% 0.21/0.46    inference(subsumption_resolution,[],[f266,f179])).
% 0.21/0.46  fof(f266,plain,(
% 0.21/0.46    ~r1_tmap_1(sK0,sK1,sK2,sK5) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_16 | ~spl8_18 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_22 | ~spl8_23 | spl8_26)),
% 0.21/0.46    inference(subsumption_resolution,[],[f265,f167])).
% 0.21/0.46  fof(f265,plain,(
% 0.21/0.46    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_16 | ~spl8_18 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_23 | spl8_26)),
% 0.21/0.46    inference(subsumption_resolution,[],[f264,f135])).
% 0.21/0.46  fof(f264,plain,(
% 0.21/0.46    ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_18 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_23 | spl8_26)),
% 0.21/0.46    inference(subsumption_resolution,[],[f263,f162])).
% 0.21/0.46  fof(f263,plain,(
% 0.21/0.46    ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK0)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tmap_1(sK0,sK1,sK2,sK5) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_18 | ~spl8_19 | ~spl8_20 | ~spl8_23 | spl8_26)),
% 0.21/0.46    inference(resolution,[],[f262,f188])).
% 0.21/0.46  fof(f188,plain,(
% 0.21/0.46    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | spl8_26),
% 0.21/0.46    inference(avatar_component_clause,[],[f187])).
% 0.21/0.46  fof(f262,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK0,sK1,sK2,X0)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_18 | ~spl8_19 | ~spl8_20 | ~spl8_23)),
% 0.21/0.46    inference(subsumption_resolution,[],[f261,f108])).
% 0.21/0.46  fof(f261,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK0,sK1,sK2,X0) | ~m1_pre_topc(sK4,sK0)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_18 | ~spl8_19 | ~spl8_20 | ~spl8_23)),
% 0.21/0.46    inference(superposition,[],[f258,f224])).
% 0.21/0.46  fof(f258,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK0,sK1,sK2,X0)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19 | ~spl8_20 | ~spl8_23)),
% 0.21/0.46    inference(subsumption_resolution,[],[f257,f157])).
% 0.21/0.46  fof(f257,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0) | ~r1_tmap_1(sK0,sK1,sK2,X0)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19 | ~spl8_23)),
% 0.21/0.46    inference(subsumption_resolution,[],[f256,f78])).
% 0.21/0.46  fof(f256,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_pre_topc(sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0) | ~r1_tmap_1(sK0,sK1,sK2,X0)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19 | ~spl8_23)),
% 0.21/0.46    inference(subsumption_resolution,[],[f255,f73])).
% 0.21/0.46  fof(f255,plain,(
% 0.21/0.46    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0) | ~r1_tmap_1(sK0,sK1,sK2,X0)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_4 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19 | ~spl8_23)),
% 0.21/0.46    inference(subsumption_resolution,[],[f254,f68])).
% 0.21/0.46  fof(f254,plain,(
% 0.21/0.46    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK4,sK1,k3_tmap_1(sK0,sK1,sK0,sK4,sK2),X0) | ~r1_tmap_1(sK0,sK1,sK2,X0)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19 | ~spl8_23)),
% 0.21/0.46    inference(resolution,[],[f240,f172])).
% 0.21/0.46  fof(f240,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1) | ~r1_tmap_1(sK0,X0,sK2,X1)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f239,f88])).
% 0.21/0.46  fof(f239,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1) | ~r1_tmap_1(sK0,X0,sK2,X1)) ) | (spl8_1 | spl8_2 | ~spl8_3 | spl8_7 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f238,f83])).
% 0.21/0.46  fof(f238,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1) | ~r1_tmap_1(sK0,X0,sK2,X1)) ) | (spl8_1 | spl8_2 | ~spl8_3 | ~spl8_9 | ~spl8_12 | ~spl8_13 | ~spl8_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f237,f108])).
% 0.21/0.46  fof(f237,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1) | ~r1_tmap_1(sK0,X0,sK2,X1)) ) | (spl8_1 | spl8_2 | ~spl8_3 | ~spl8_9 | ~spl8_13 | ~spl8_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f236,f53])).
% 0.21/0.46  fof(f236,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1) | ~r1_tmap_1(sK0,X0,sK2,X1)) ) | (spl8_2 | ~spl8_3 | ~spl8_9 | ~spl8_13 | ~spl8_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f235,f113])).
% 0.21/0.46  fof(f235,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1) | ~r1_tmap_1(sK0,X0,sK2,X1)) ) | (spl8_2 | ~spl8_3 | ~spl8_9 | ~spl8_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f234,f58])).
% 0.21/0.46  fof(f234,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1) | ~r1_tmap_1(sK0,X0,sK2,X1)) ) | (~spl8_3 | ~spl8_9 | ~spl8_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f233,f93])).
% 0.21/0.46  fof(f233,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tmap_1(sK4,X0,k3_tmap_1(sK0,X0,sK0,sK4,sK2),X1) | ~r1_tmap_1(sK0,X0,sK2,X1)) ) | (~spl8_3 | ~spl8_19)),
% 0.21/0.46    inference(superposition,[],[f117,f152])).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    ( ! [X12,X10,X8,X11,X9] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X8,X10,X11)),u1_struct_0(X9)))) | ~l1_pre_topc(X8) | v2_struct_0(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X9) | v2_struct_0(X10) | ~m1_pre_topc(X10,X8) | v2_struct_0(X11) | ~m1_pre_topc(X11,X8) | v2_struct_0(X8) | ~v1_funct_2(sK2,u1_struct_0(k1_tsep_1(X8,X10,X11)),u1_struct_0(X9)) | ~v2_pre_topc(X8) | ~m1_subset_1(X12,u1_struct_0(X10)) | ~m1_subset_1(X12,u1_struct_0(X11)) | ~m1_subset_1(X12,u1_struct_0(k1_tsep_1(X8,X10,X11))) | r1_tmap_1(X11,X9,k3_tmap_1(X8,X9,k1_tsep_1(X8,X10,X11),X11,sK2),X12) | ~r1_tmap_1(k1_tsep_1(X8,X10,X11),X9,sK2,X12)) ) | ~spl8_3),
% 0.21/0.46    inference(resolution,[],[f63,f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X7,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)) )),
% 0.21/0.46    inference(equality_resolution,[],[f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ( ! [X6,X4,X2,X0,X7,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | X6 != X7 | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)) )),
% 0.21/0.46    inference(equality_resolution,[],[f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X2,X3))) | X5 != X7 | X6 != X7 | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X6) | ~r1_tmap_1(k1_tsep_1(X0,X2,X3),X1,X4,X7)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f190,plain,(
% 0.21/0.46    spl8_26 | ~spl8_11 | spl8_24),
% 0.21/0.46    inference(avatar_split_clause,[],[f185,f177,f101,f187])).
% 0.21/0.46  fof(f185,plain,(
% 0.21/0.46    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | (~spl8_11 | spl8_24)),
% 0.21/0.46    inference(subsumption_resolution,[],[f175,f178])).
% 0.21/0.46  fof(f175,plain,(
% 0.21/0.46    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | r1_tmap_1(sK0,sK1,sK2,sK5) | ~spl8_11),
% 0.21/0.46    inference(forward_demodulation,[],[f18,f103])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f184,plain,(
% 0.21/0.46    spl8_24 | spl8_25 | ~spl8_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f174,f96,f181,f177])).
% 0.21/0.46  fof(f174,plain,(
% 0.21/0.46    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | r1_tmap_1(sK0,sK1,sK2,sK5) | ~spl8_10),
% 0.21/0.46    inference(forward_demodulation,[],[f17,f98])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f173,plain,(
% 0.21/0.46    spl8_23),
% 0.21/0.46    inference(avatar_split_clause,[],[f31,f170])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f168,plain,(
% 0.21/0.46    spl8_22 | ~spl8_10 | ~spl8_15),
% 0.21/0.46    inference(avatar_split_clause,[],[f143,f128,f96,f165])).
% 0.21/0.46  fof(f128,plain,(
% 0.21/0.46    spl8_15 <=> m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.46  fof(f143,plain,(
% 0.21/0.46    m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl8_10 | ~spl8_15)),
% 0.21/0.46    inference(forward_demodulation,[],[f130,f98])).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    m1_subset_1(sK6,u1_struct_0(sK3)) | ~spl8_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f128])).
% 0.21/0.46  fof(f163,plain,(
% 0.21/0.46    spl8_21 | ~spl8_11 | ~spl8_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f137,f123,f101,f160])).
% 0.21/0.46  fof(f123,plain,(
% 0.21/0.46    spl8_14 <=> m1_subset_1(sK7,u1_struct_0(sK4))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.46  fof(f137,plain,(
% 0.21/0.46    m1_subset_1(sK5,u1_struct_0(sK4)) | (~spl8_11 | ~spl8_14)),
% 0.21/0.46    inference(forward_demodulation,[],[f125,f103])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    m1_subset_1(sK7,u1_struct_0(sK4)) | ~spl8_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f123])).
% 0.21/0.46  fof(f158,plain,(
% 0.21/0.46    spl8_20),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f155])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f153,plain,(
% 0.21/0.46    spl8_19),
% 0.21/0.46    inference(avatar_split_clause,[],[f26,f150])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    sK0 = k1_tsep_1(sK0,sK3,sK4)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f148,plain,(
% 0.21/0.46    spl8_18 | ~spl8_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f121,f91,f145])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    m1_pre_topc(sK0,sK0) | ~spl8_9),
% 0.21/0.46    inference(resolution,[],[f93,f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.46  fof(f136,plain,(
% 0.21/0.46    spl8_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f23,f133])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    m1_subset_1(sK5,u1_struct_0(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    spl8_15),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f128])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    spl8_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f19,f123])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    m1_subset_1(sK7,u1_struct_0(sK4))),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f114,plain,(
% 0.21/0.46    spl8_13),
% 0.21/0.46    inference(avatar_split_clause,[],[f28,f111])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    m1_pre_topc(sK3,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    spl8_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f106])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    m1_pre_topc(sK4,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    spl8_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f21,f101])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    sK5 = sK7),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    spl8_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f20,f96])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    sK5 = sK6),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    spl8_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f37,f91])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    l1_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    spl8_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f36,f86])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    v2_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    ~spl8_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f35,f81])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ~v2_struct_0(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    spl8_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f34,f76])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    l1_pre_topc(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    spl8_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f33,f71])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    v2_pre_topc(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    ~spl8_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f32,f66])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ~v2_struct_0(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    spl8_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f29,f61])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    v1_funct_1(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  % (30962)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ~spl8_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f56])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ~v2_struct_0(sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ~spl8_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f51])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ~v2_struct_0(sK4)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (30964)------------------------------
% 0.21/0.47  % (30964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (30964)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (30964)Memory used [KB]: 10874
% 0.21/0.47  % (30964)Time elapsed: 0.061 s
% 0.21/0.47  % (30964)------------------------------
% 0.21/0.47  % (30964)------------------------------
% 0.21/0.47  % (30960)Success in time 0.114 s
%------------------------------------------------------------------------------
