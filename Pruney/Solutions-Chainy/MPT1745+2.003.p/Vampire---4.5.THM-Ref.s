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
% DateTime   : Thu Dec  3 13:18:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 349 expanded)
%              Number of leaves         :   29 ( 132 expanded)
%              Depth                    :   29
%              Number of atoms          : 1097 (2743 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   29 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f280,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f72,f77,f82,f87,f92,f97,f102,f136,f141,f146,f151,f156,f161,f172,f177,f189,f200,f270,f276,f279])).

fof(f279,plain,
    ( ~ spl8_2
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_20
    | spl8_23
    | spl8_27 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_20
    | spl8_23
    | spl8_27 ),
    inference(subsumption_resolution,[],[f277,f135])).

fof(f135,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl8_12
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f277,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_20
    | spl8_23
    | spl8_27 ),
    inference(resolution,[],[f275,f245])).

fof(f245,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_20
    | spl8_23 ),
    inference(subsumption_resolution,[],[f202,f199])).

fof(f199,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl8_23 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl8_23
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f202,plain,
    ( ! [X0] :
        ( v1_xboole_0(u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0),u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f201,f155])).

fof(f155,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl8_16
  <=> v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0),u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_20 ),
    inference(resolution,[],[f104,f176])).

fof(f176,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl8_20
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f104,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK3,X0,X1)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X2,X0)
        | m1_subset_1(k3_funct_2(X0,X1,sK3,X2),X1) )
    | ~ spl8_2 ),
    inference(resolution,[],[f56,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f56,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl8_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f275,plain,
    ( ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | spl8_27 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl8_27
  <=> m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f276,plain,
    ( ~ spl8_27
    | ~ spl8_1
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_19
    | spl8_26 ),
    inference(avatar_split_clause,[],[f271,f267,f169,f148,f138,f99,f94,f89,f84,f79,f74,f49,f273])).

fof(f49,plain,
    ( spl8_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f74,plain,
    ( spl8_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f79,plain,
    ( spl8_7
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f84,plain,
    ( spl8_8
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f89,plain,
    ( spl8_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f94,plain,
    ( spl8_10
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f99,plain,
    ( spl8_11
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f138,plain,
    ( spl8_13
  <=> v5_pre_topc(sK4,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f148,plain,
    ( spl8_15
  <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f169,plain,
    ( spl8_19
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f267,plain,
    ( spl8_26
  <=> r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f271,plain,
    ( ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ spl8_1
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_19
    | spl8_26 ),
    inference(resolution,[],[f269,f220])).

fof(f220,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK0,sK1,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_1
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f219,f140])).

fof(f140,plain,
    ( v5_pre_topc(sK4,sK0,sK1)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f138])).

fof(f219,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | ~ spl8_1
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f218,f171])).

fof(f171,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f169])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | ~ spl8_1
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f217,f91])).

fof(f91,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f217,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | ~ spl8_1
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f216,f51])).

fof(f51,plain,
    ( v1_funct_1(sK4)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f215,f101])).

fof(f101,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f214,f96])).

fof(f96,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_15 ),
    inference(resolution,[],[f120,f150])).

fof(f150,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f148])).

fof(f120,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r1_tmap_1(X0,sK1,X1,X2)
        | ~ v5_pre_topc(X1,X0,sK1) )
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f119,f76])).

fof(f76,plain,
    ( ~ v2_struct_0(sK1)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f119,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r1_tmap_1(X0,sK1,X1,X2)
        | ~ v5_pre_topc(X1,X0,sK1) )
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f115,f81])).

fof(f81,plain,
    ( v2_pre_topc(sK1)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f115,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r1_tmap_1(X0,sK1,X1,X2)
        | ~ v5_pre_topc(X1,X0,sK1) )
    | ~ spl8_8 ),
    inference(resolution,[],[f86,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r1_tmap_1(X1,X0,X2,X3)
      | ~ v5_pre_topc(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).

fof(f86,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f269,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | spl8_26 ),
    inference(avatar_component_clause,[],[f267])).

fof(f270,plain,
    ( ~ spl8_26
    | ~ spl8_1
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_20
    | spl8_22
    | spl8_23 ),
    inference(avatar_split_clause,[],[f265,f197,f186,f174,f169,f153,f148,f143,f133,f99,f94,f89,f84,f79,f74,f69,f64,f59,f54,f49,f267])).

fof(f59,plain,
    ( spl8_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f64,plain,
    ( spl8_4
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f69,plain,
    ( spl8_5
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f143,plain,
    ( spl8_14
  <=> r1_tmap_1(sK2,sK0,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f186,plain,
    ( spl8_22
  <=> r1_tmap_1(sK2,sK1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f265,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | ~ spl8_1
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_20
    | spl8_22
    | spl8_23 ),
    inference(subsumption_resolution,[],[f264,f81])).

fof(f264,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | ~ v2_pre_topc(sK1)
    | ~ spl8_1
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_20
    | spl8_22
    | spl8_23 ),
    inference(subsumption_resolution,[],[f263,f76])).

fof(f263,plain,
    ( v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | ~ v2_pre_topc(sK1)
    | ~ spl8_1
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_20
    | spl8_22
    | spl8_23 ),
    inference(subsumption_resolution,[],[f262,f171])).

fof(f262,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | ~ v2_pre_topc(sK1)
    | ~ spl8_1
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_20
    | spl8_22
    | spl8_23 ),
    inference(subsumption_resolution,[],[f261,f150])).

fof(f261,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | ~ v2_pre_topc(sK1)
    | ~ spl8_1
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | spl8_22
    | spl8_23 ),
    inference(subsumption_resolution,[],[f260,f51])).

fof(f260,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | ~ v2_pre_topc(sK1)
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | spl8_22
    | spl8_23 ),
    inference(subsumption_resolution,[],[f259,f86])).

fof(f259,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | ~ v2_pre_topc(sK1)
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | spl8_22
    | spl8_23 ),
    inference(resolution,[],[f258,f188])).

fof(f188,plain,
    ( ~ r1_tmap_1(sK2,sK1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),sK5)
    | spl8_22 ),
    inference(avatar_component_clause,[],[f186])).

fof(f258,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X0),sK3,X1),sK5)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ r1_tmap_1(sK0,X0,X1,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
        | ~ v2_pre_topc(X0) )
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | spl8_23 ),
    inference(subsumption_resolution,[],[f257,f135])).

fof(f257,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK0,X0,X1,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
        | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X0),sK3,X1),sK5) )
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | spl8_23 ),
    inference(resolution,[],[f256,f145])).

fof(f145,plain,
    ( r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f143])).

fof(f256,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tmap_1(sK2,sK0,sK3,X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | v2_struct_0(X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0))
        | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0) )
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20
    | spl8_23 ),
    inference(subsumption_resolution,[],[f255,f176])).

fof(f255,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK2,sK0,sK3,X0)
        | ~ r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0))
        | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0) )
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20
    | spl8_23 ),
    inference(subsumption_resolution,[],[f254,f155])).

fof(f254,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK2,sK0,sK3,X0)
        | ~ r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0))
        | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0) )
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20
    | spl8_23 ),
    inference(subsumption_resolution,[],[f253,f56])).

fof(f253,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK2,sK0,sK3,X0)
        | ~ r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0))
        | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0) )
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20
    | spl8_23 ),
    inference(subsumption_resolution,[],[f252,f101])).

fof(f252,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK2,sK0,sK3,X0)
        | ~ r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0))
        | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0) )
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_9
    | ~ spl8_10
    | ~ spl8_16
    | ~ spl8_20
    | spl8_23 ),
    inference(subsumption_resolution,[],[f251,f96])).

fof(f251,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK2,sK0,sK3,X0)
        | ~ r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0))
        | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0) )
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_9
    | ~ spl8_16
    | ~ spl8_20
    | spl8_23 ),
    inference(subsumption_resolution,[],[f250,f91])).

fof(f250,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK2,sK0,sK3,X0)
        | ~ r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0))
        | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0) )
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_16
    | ~ spl8_20
    | spl8_23 ),
    inference(subsumption_resolution,[],[f249,f71])).

fof(f71,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f249,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK2,sK0,sK3,X0)
        | ~ r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0))
        | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0) )
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_16
    | ~ spl8_20
    | spl8_23 ),
    inference(subsumption_resolution,[],[f248,f66])).

fof(f66,plain,
    ( v2_pre_topc(sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f248,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK2,sK0,sK3,X0)
        | ~ r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0))
        | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0) )
    | ~ spl8_2
    | spl8_3
    | ~ spl8_16
    | ~ spl8_20
    | spl8_23 ),
    inference(subsumption_resolution,[],[f247,f61])).

fof(f61,plain,
    ( ~ v2_struct_0(sK2)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f247,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK2,sK0,sK3,X0)
        | ~ r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0))
        | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0) )
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_20
    | spl8_23 ),
    inference(duplicate_literal_removal,[],[f246])).

fof(f246,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK2,sK0,sK3,X0)
        | ~ r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0))
        | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0) )
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_20
    | spl8_23 ),
    inference(resolution,[],[f245,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ r1_tmap_1(X1,X2,X3,X5)
      | ~ r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5))
      | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
      | ~ r1_tmap_1(X1,X2,X3,X5)
      | ~ r1_tmap_1(X2,X0,X4,X6)
      | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
                              | ~ r1_tmap_1(X2,X0,X4,X6)
                              | ~ r1_tmap_1(X1,X2,X3,X5)
                              | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
                              | ~ r1_tmap_1(X2,X0,X4,X6)
                              | ~ r1_tmap_1(X1,X2,X3,X5)
                              | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( ( r1_tmap_1(X2,X0,X4,X6)
                                  & r1_tmap_1(X1,X2,X3,X5)
                                  & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6 )
                               => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tmap_1)).

fof(f200,plain,
    ( ~ spl8_23
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_17 ),
    inference(avatar_split_clause,[],[f193,f158,f69,f64,f59,f197])).

fof(f158,plain,
    ( spl8_17
  <=> v1_xboole_0(sK7(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f193,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_17 ),
    inference(subsumption_resolution,[],[f192,f61])).

fof(f192,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ spl8_4
    | ~ spl8_5
    | spl8_17 ),
    inference(subsumption_resolution,[],[f191,f71])).

fof(f191,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f190,f66])).

fof(f190,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl8_17 ),
    inference(resolution,[],[f162,f43])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(f162,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7(sK2),k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) )
    | spl8_17 ),
    inference(resolution,[],[f160,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f160,plain,
    ( ~ v1_xboole_0(sK7(sK2))
    | spl8_17 ),
    inference(avatar_component_clause,[],[f158])).

fof(f189,plain,(
    ~ spl8_22 ),
    inference(avatar_split_clause,[],[f22,f186])).

fof(f22,plain,(
    ~ r1_tmap_1(sK2,sK1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
                          & v5_pre_topc(X4,X0,X1)
                          & r1_tmap_1(X2,X0,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
                          & v5_pre_topc(X4,X0,X1)
                          & r1_tmap_1(X2,X0,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
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
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ( ( v5_pre_topc(X4,X0,X1)
                                & r1_tmap_1(X2,X0,X3,X5) )
                             => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ( ( v5_pre_topc(X4,X0,X1)
                              & r1_tmap_1(X2,X0,X3,X5) )
                           => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tmap_1)).

fof(f177,plain,(
    spl8_20 ),
    inference(avatar_split_clause,[],[f28,f174])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f172,plain,(
    spl8_19 ),
    inference(avatar_split_clause,[],[f25,f169])).

fof(f25,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f161,plain,
    ( ~ spl8_17
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f109,f69,f64,f59,f158])).

fof(f109,plain,
    ( ~ v1_xboole_0(sK7(sK2))
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f108,f61])).

fof(f108,plain,
    ( v2_struct_0(sK2)
    | ~ v1_xboole_0(sK7(sK2))
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f105,f66])).

fof(f105,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ v1_xboole_0(sK7(sK2))
    | ~ spl8_5 ),
    inference(resolution,[],[f71,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(sK7(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f156,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f27,f153])).

fof(f27,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f151,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f24,f148])).

fof(f24,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f146,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f20,f143])).

fof(f20,plain,(
    r1_tmap_1(sK2,sK0,sK3,sK5) ),
    inference(cnf_transformation,[],[f9])).

fof(f141,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f21,f138])).

fof(f21,plain,(
    v5_pre_topc(sK4,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f136,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f19,f133])).

fof(f19,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f102,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f37,f99])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f97,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f36,f94])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f92,plain,(
    ~ spl8_9 ),
    inference(avatar_split_clause,[],[f35,f89])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f87,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f34,f84])).

fof(f34,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f82,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f33,f79])).

fof(f33,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f77,plain,(
    ~ spl8_6 ),
    inference(avatar_split_clause,[],[f32,f74])).

fof(f32,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f72,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f31,f69])).

fof(f31,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f67,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f30,f64])).

fof(f30,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:13:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (2849)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (2852)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (2849)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (2860)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (2857)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f280,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f72,f77,f82,f87,f92,f97,f102,f136,f141,f146,f151,f156,f161,f172,f177,f189,f200,f270,f276,f279])).
% 0.21/0.48  fof(f279,plain,(
% 0.21/0.48    ~spl8_2 | ~spl8_12 | ~spl8_16 | ~spl8_20 | spl8_23 | spl8_27),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f278])).
% 0.21/0.48  fof(f278,plain,(
% 0.21/0.48    $false | (~spl8_2 | ~spl8_12 | ~spl8_16 | ~spl8_20 | spl8_23 | spl8_27)),
% 0.21/0.48    inference(subsumption_resolution,[],[f277,f135])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl8_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f133])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    spl8_12 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    ~m1_subset_1(sK5,u1_struct_0(sK2)) | (~spl8_2 | ~spl8_16 | ~spl8_20 | spl8_23 | spl8_27)),
% 0.21/0.48    inference(resolution,[],[f275,f245])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK2))) ) | (~spl8_2 | ~spl8_16 | ~spl8_20 | spl8_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f202,f199])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    ~v1_xboole_0(u1_struct_0(sK2)) | spl8_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f197])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    spl8_23 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    ( ! [X0] : (v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0),u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_16 | ~spl8_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f201,f155])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) | ~spl8_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f153])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    spl8_16 <=> v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0),u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_20)),
% 0.21/0.48    inference(resolution,[],[f104,f176])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~spl8_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f174])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    spl8_20 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X2,X0) | m1_subset_1(k3_funct_2(X0,X1,sK3,X2),X1)) ) | ~spl8_2),
% 0.21/0.48    inference(resolution,[],[f56,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    v1_funct_1(sK3) | ~spl8_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl8_2 <=> v1_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.48  fof(f275,plain,(
% 0.21/0.48    ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0)) | spl8_27),
% 0.21/0.48    inference(avatar_component_clause,[],[f273])).
% 0.21/0.48  fof(f273,plain,(
% 0.21/0.48    spl8_27 <=> m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.21/0.48  fof(f276,plain,(
% 0.21/0.48    ~spl8_27 | ~spl8_1 | spl8_6 | ~spl8_7 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_15 | ~spl8_19 | spl8_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f271,f267,f169,f148,f138,f99,f94,f89,f84,f79,f74,f49,f273])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl8_1 <=> v1_funct_1(sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl8_6 <=> v2_struct_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl8_7 <=> v2_pre_topc(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl8_8 <=> l1_pre_topc(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl8_9 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl8_10 <=> v2_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl8_11 <=> l1_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    spl8_13 <=> v5_pre_topc(sK4,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    spl8_15 <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    spl8_19 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.48  fof(f267,plain,(
% 0.21/0.48    spl8_26 <=> r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.21/0.48  fof(f271,plain,(
% 0.21/0.48    ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0)) | (~spl8_1 | spl8_6 | ~spl8_7 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_15 | ~spl8_19 | spl8_26)),
% 0.21/0.48    inference(resolution,[],[f269,f220])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tmap_1(sK0,sK1,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_1 | spl8_6 | ~spl8_7 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_15 | ~spl8_19)),
% 0.21/0.48    inference(subsumption_resolution,[],[f219,f140])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    v5_pre_topc(sK4,sK0,sK1) | ~spl8_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f138])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK4,X0) | ~v5_pre_topc(sK4,sK0,sK1)) ) | (~spl8_1 | spl8_6 | ~spl8_7 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_15 | ~spl8_19)),
% 0.21/0.48    inference(subsumption_resolution,[],[f218,f171])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl8_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f169])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK4,X0) | ~v5_pre_topc(sK4,sK0,sK1)) ) | (~spl8_1 | spl8_6 | ~spl8_7 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f217,f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ~v2_struct_0(sK0) | spl8_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f89])).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK4,X0) | ~v5_pre_topc(sK4,sK0,sK1)) ) | (~spl8_1 | spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_10 | ~spl8_11 | ~spl8_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f216,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    v1_funct_1(sK4) | ~spl8_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f49])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(sK4) | v2_struct_0(sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK4,X0) | ~v5_pre_topc(sK4,sK0,sK1)) ) | (spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_10 | ~spl8_11 | ~spl8_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f215,f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    l1_pre_topc(sK0) | ~spl8_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f99])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | v2_struct_0(sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK4,X0) | ~v5_pre_topc(sK4,sK0,sK1)) ) | (spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_10 | ~spl8_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f214,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    v2_pre_topc(sK0) | ~spl8_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f94])).
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | v2_struct_0(sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK4,X0) | ~v5_pre_topc(sK4,sK0,sK1)) ) | (spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_15)),
% 0.21/0.48    inference(resolution,[],[f120,f150])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl8_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f148])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_tmap_1(X0,sK1,X1,X2) | ~v5_pre_topc(X1,X0,sK1)) ) | (spl8_6 | ~spl8_7 | ~spl8_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f119,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ~v2_struct_0(sK1) | spl8_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v2_struct_0(sK1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_tmap_1(X0,sK1,X1,X2) | ~v5_pre_topc(X1,X0,sK1)) ) | (~spl8_7 | ~spl8_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f115,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    v2_pre_topc(sK1) | ~spl8_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(sK1) | v2_struct_0(sK1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_tmap_1(X0,sK1,X1,X2) | ~v5_pre_topc(X1,X0,sK1)) ) | ~spl8_8),
% 0.21/0.48    inference(resolution,[],[f86,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X1)) | r1_tmap_1(X1,X0,X2,X3) | ~v5_pre_topc(X2,X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    l1_pre_topc(sK1) | ~spl8_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f84])).
% 0.21/0.48  fof(f269,plain,(
% 0.21/0.48    ~r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5)) | spl8_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f267])).
% 0.21/0.48  fof(f270,plain,(
% 0.21/0.48    ~spl8_26 | ~spl8_1 | ~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_7 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_12 | ~spl8_14 | ~spl8_15 | ~spl8_16 | ~spl8_19 | ~spl8_20 | spl8_22 | spl8_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f265,f197,f186,f174,f169,f153,f148,f143,f133,f99,f94,f89,f84,f79,f74,f69,f64,f59,f54,f49,f267])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl8_3 <=> v2_struct_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl8_4 <=> v2_pre_topc(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl8_5 <=> l1_pre_topc(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    spl8_14 <=> r1_tmap_1(sK2,sK0,sK3,sK5)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    spl8_22 <=> r1_tmap_1(sK2,sK1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),sK5)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    ~r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5)) | (~spl8_1 | ~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_7 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_12 | ~spl8_14 | ~spl8_15 | ~spl8_16 | ~spl8_19 | ~spl8_20 | spl8_22 | spl8_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f264,f81])).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    ~r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5)) | ~v2_pre_topc(sK1) | (~spl8_1 | ~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_12 | ~spl8_14 | ~spl8_15 | ~spl8_16 | ~spl8_19 | ~spl8_20 | spl8_22 | spl8_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f263,f76])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    v2_struct_0(sK1) | ~r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5)) | ~v2_pre_topc(sK1) | (~spl8_1 | ~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_12 | ~spl8_14 | ~spl8_15 | ~spl8_16 | ~spl8_19 | ~spl8_20 | spl8_22 | spl8_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f262,f171])).
% 0.21/0.48  fof(f262,plain,(
% 0.21/0.48    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5)) | ~v2_pre_topc(sK1) | (~spl8_1 | ~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_12 | ~spl8_14 | ~spl8_15 | ~spl8_16 | ~spl8_20 | spl8_22 | spl8_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f261,f150])).
% 0.21/0.48  fof(f261,plain,(
% 0.21/0.48    ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5)) | ~v2_pre_topc(sK1) | (~spl8_1 | ~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_12 | ~spl8_14 | ~spl8_16 | ~spl8_20 | spl8_22 | spl8_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f260,f51])).
% 0.21/0.48  fof(f260,plain,(
% 0.21/0.48    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5)) | ~v2_pre_topc(sK1) | (~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_12 | ~spl8_14 | ~spl8_16 | ~spl8_20 | spl8_22 | spl8_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f259,f86])).
% 0.21/0.48  fof(f259,plain,(
% 0.21/0.48    ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5)) | ~v2_pre_topc(sK1) | (~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_12 | ~spl8_14 | ~spl8_16 | ~spl8_20 | spl8_22 | spl8_23)),
% 0.21/0.48    inference(resolution,[],[f258,f188])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ~r1_tmap_1(sK2,sK1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),sK5) | spl8_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f186])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X0),sK3,X1),sK5) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~r1_tmap_1(sK0,X0,X1,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5)) | ~v2_pre_topc(X0)) ) | (~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_12 | ~spl8_14 | ~spl8_16 | ~spl8_20 | spl8_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f257,f135])).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~r1_tmap_1(sK0,X0,X1,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5)) | r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X0),sK3,X1),sK5)) ) | (~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_14 | ~spl8_16 | ~spl8_20 | spl8_23)),
% 0.21/0.48    inference(resolution,[],[f256,f145])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    r1_tmap_1(sK2,sK0,sK3,sK5) | ~spl8_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f143])).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tmap_1(sK2,sK0,sK3,X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0)) | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0)) ) | (~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_16 | ~spl8_20 | spl8_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f255,f176])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~r1_tmap_1(sK2,sK0,sK3,X0) | ~r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0)) | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0)) ) | (~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_16 | ~spl8_20 | spl8_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f254,f155])).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~r1_tmap_1(sK2,sK0,sK3,X0) | ~r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0)) | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0)) ) | (~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_16 | ~spl8_20 | spl8_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f253,f56])).
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~r1_tmap_1(sK2,sK0,sK3,X0) | ~r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0)) | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0)) ) | (~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_16 | ~spl8_20 | spl8_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f252,f101])).
% 0.21/0.48  fof(f252,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~r1_tmap_1(sK2,sK0,sK3,X0) | ~r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0)) | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0)) ) | (~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | spl8_9 | ~spl8_10 | ~spl8_16 | ~spl8_20 | spl8_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f251,f96])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~r1_tmap_1(sK2,sK0,sK3,X0) | ~r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0)) | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0)) ) | (~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | spl8_9 | ~spl8_16 | ~spl8_20 | spl8_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f250,f91])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~r1_tmap_1(sK2,sK0,sK3,X0) | ~r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0)) | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0)) ) | (~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_16 | ~spl8_20 | spl8_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f249,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    l1_pre_topc(sK2) | ~spl8_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f69])).
% 0.21/0.48  fof(f249,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK2) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~r1_tmap_1(sK2,sK0,sK3,X0) | ~r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0)) | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0)) ) | (~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_16 | ~spl8_20 | spl8_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f248,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    v2_pre_topc(sK2) | ~spl8_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~r1_tmap_1(sK2,sK0,sK3,X0) | ~r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0)) | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0)) ) | (~spl8_2 | spl8_3 | ~spl8_16 | ~spl8_20 | spl8_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f247,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ~v2_struct_0(sK2) | spl8_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f59])).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~r1_tmap_1(sK2,sK0,sK3,X0) | ~r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0)) | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0)) ) | (~spl8_2 | ~spl8_16 | ~spl8_20 | spl8_23)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f246])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | v2_struct_0(X1) | ~r1_tmap_1(sK2,sK0,sK3,X0) | ~r1_tmap_1(sK0,X1,X2,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0)) | r1_tmap_1(sK2,X1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),sK3,X2),X0)) ) | (~spl8_2 | ~spl8_16 | ~spl8_20 | spl8_23)),
% 0.21/0.48    inference(resolution,[],[f245,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~m1_subset_1(X5,u1_struct_0(X1)) | v2_struct_0(X0) | ~r1_tmap_1(X1,X2,X3,X5) | ~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)) )),
% 0.21/0.48    inference(equality_resolution,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X2)) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~r1_tmap_1(X1,X2,X3,X5) | ~r1_tmap_1(X2,X0,X4,X6) | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | (~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6)) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X0,X4,X6) & r1_tmap_1(X1,X2,X3,X5) & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6) => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)))))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tmap_1)).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    ~spl8_23 | spl8_3 | ~spl8_4 | ~spl8_5 | spl8_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f193,f158,f69,f64,f59,f197])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    spl8_17 <=> v1_xboole_0(sK7(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    ~v1_xboole_0(u1_struct_0(sK2)) | (spl8_3 | ~spl8_4 | ~spl8_5 | spl8_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f192,f61])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    ~v1_xboole_0(u1_struct_0(sK2)) | v2_struct_0(sK2) | (~spl8_4 | ~spl8_5 | spl8_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f191,f71])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ~v1_xboole_0(u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | (~spl8_4 | spl8_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f190,f66])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    ~v1_xboole_0(u1_struct_0(sK2)) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | spl8_17),
% 0.21/0.48    inference(resolution,[],[f162,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK7(sK2),k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) ) | spl8_17),
% 0.21/0.48    inference(resolution,[],[f160,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    ~v1_xboole_0(sK7(sK2)) | spl8_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f158])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ~spl8_22),
% 0.21/0.48    inference(avatar_split_clause,[],[f22,f186])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ~r1_tmap_1(sK2,sK1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),sK5)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & (v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5))) & m1_subset_1(X5,u1_struct_0(X2))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3))) & (l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5)) => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5))))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5)) => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5))))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tmap_1)).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    spl8_20),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f174])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    spl8_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f169])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    ~spl8_17 | spl8_3 | ~spl8_4 | ~spl8_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f109,f69,f64,f59,f158])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ~v1_xboole_0(sK7(sK2)) | (spl8_3 | ~spl8_4 | ~spl8_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f108,f61])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    v2_struct_0(sK2) | ~v1_xboole_0(sK7(sK2)) | (~spl8_4 | ~spl8_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f105,f66])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~v1_xboole_0(sK7(sK2)) | ~spl8_5),
% 0.21/0.48    inference(resolution,[],[f71,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_xboole_0(sK7(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    spl8_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f153])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    spl8_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f148])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    spl8_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f143])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    r1_tmap_1(sK2,sK0,sK3,sK5)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    spl8_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f138])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    v5_pre_topc(sK4,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    spl8_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f133])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    spl8_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f37,f99])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl8_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f94])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ~spl8_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f89])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl8_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f84])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    l1_pre_topc(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl8_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f79])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    v2_pre_topc(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ~spl8_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f74])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ~v2_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl8_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f69])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    l1_pre_topc(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl8_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f64])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v2_pre_topc(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ~spl8_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f59])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ~v2_struct_0(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl8_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f54])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    v1_funct_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl8_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f49])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    v1_funct_1(sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (2849)------------------------------
% 0.21/0.48  % (2849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2849)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (2849)Memory used [KB]: 10874
% 0.21/0.48  % (2849)Time elapsed: 0.056 s
% 0.21/0.48  % (2849)------------------------------
% 0.21/0.48  % (2849)------------------------------
% 0.21/0.49  % (2844)Success in time 0.122 s
%------------------------------------------------------------------------------
