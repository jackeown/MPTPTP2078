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
% DateTime   : Thu Dec  3 13:19:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 432 expanded)
%              Number of leaves         :   54 ( 242 expanded)
%              Depth                    :    7
%              Number of atoms          :  892 (4651 expanded)
%              Number of equality atoms :   45 (  82 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f545,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f92,f96,f100,f104,f108,f112,f116,f120,f124,f128,f132,f136,f140,f144,f148,f152,f170,f177,f182,f188,f206,f210,f214,f217,f254,f286,f311,f380,f502,f522,f534,f535,f540,f543,f544])).

fof(f544,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) != k2_tmap_1(sK2,sK1,sK4,sK3)
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f543,plain,
    ( spl5_13
    | ~ spl5_21
    | ~ spl5_22
    | spl5_16
    | ~ spl5_15
    | ~ spl5_14
    | ~ spl5_9
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_6
    | spl5_11
    | ~ spl5_5
    | spl5_87 ),
    inference(avatar_split_clause,[],[f541,f538,f90,f114,f94,f98,f102,f106,f126,f130,f134,f160,f157,f122])).

fof(f122,plain,
    ( spl5_13
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f157,plain,
    ( spl5_21
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f160,plain,
    ( spl5_22
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f134,plain,
    ( spl5_16
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f130,plain,
    ( spl5_15
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f126,plain,
    ( spl5_14
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f106,plain,
    ( spl5_9
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f102,plain,
    ( spl5_8
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f98,plain,
    ( spl5_7
  <=> v5_pre_topc(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f94,plain,
    ( spl5_6
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f114,plain,
    ( spl5_11
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f90,plain,
    ( spl5_5
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f538,plain,
    ( spl5_87
  <=> v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f541,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl5_87 ),
    inference(resolution,[],[f539,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(X2,X0,X1)
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tmap_1)).

fof(f539,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1)
    | spl5_87 ),
    inference(avatar_component_clause,[],[f538])).

fof(f540,plain,
    ( ~ spl5_87
    | spl5_3
    | ~ spl5_83 ),
    inference(avatar_split_clause,[],[f536,f520,f83,f538])).

fof(f83,plain,
    ( spl5_3
  <=> v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f520,plain,
    ( spl5_83
  <=> k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f536,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1)
    | spl5_3
    | ~ spl5_83 ),
    inference(forward_demodulation,[],[f84,f521])).

fof(f521,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | ~ spl5_83 ),
    inference(avatar_component_clause,[],[f520])).

fof(f84,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f535,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) != k2_tmap_1(sK2,sK1,sK4,sK3)
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f534,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) != k2_tmap_1(sK2,sK1,sK4,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f522,plain,
    ( ~ spl5_9
    | ~ spl5_8
    | spl5_83
    | ~ spl5_6
    | ~ spl5_24
    | ~ spl5_79 ),
    inference(avatar_split_clause,[],[f518,f500,f186,f94,f520,f102,f106])).

fof(f186,plain,
    ( spl5_24
  <=> k2_tmap_1(sK2,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f500,plain,
    ( spl5_79
  <=> ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | k3_tmap_1(sK0,sK1,sK2,sK3,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f518,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ spl5_6
    | ~ spl5_24
    | ~ spl5_79 ),
    inference(forward_demodulation,[],[f515,f187])).

fof(f187,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f186])).

fof(f515,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ spl5_6
    | ~ spl5_79 ),
    inference(resolution,[],[f501,f95])).

fof(f95,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f501,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | k3_tmap_1(sK0,sK1,sK2,sK3,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3))
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl5_79 ),
    inference(avatar_component_clause,[],[f500])).

fof(f502,plain,
    ( ~ spl5_12
    | spl5_79
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_57 ),
    inference(avatar_split_clause,[],[f495,f378,f110,f90,f500,f118])).

fof(f118,plain,
    ( spl5_12
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f110,plain,
    ( spl5_10
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f378,plain,
    ( spl5_57
  <=> ! [X3,X5,X4] :
        ( ~ m1_pre_topc(X3,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v1_funct_1(X5)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X4,sK0)
        | k3_tmap_1(sK0,sK1,X4,X3,X5) = k2_partfun1(u1_struct_0(X4),u1_struct_0(sK1),X5,u1_struct_0(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f495,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK0)
        | k3_tmap_1(sK0,sK1,sK2,sK3,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3)) )
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_57 ),
    inference(resolution,[],[f488,f91])).

fof(f91,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f488,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X1,sK0)
        | k3_tmap_1(sK0,sK1,X1,sK3,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X0,u1_struct_0(sK3)) )
    | ~ spl5_10
    | ~ spl5_57 ),
    inference(resolution,[],[f379,f111])).

fof(f111,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f379,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_pre_topc(X3,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v1_funct_1(X5)
        | ~ m1_pre_topc(X3,X4)
        | ~ m1_pre_topc(X4,sK0)
        | k3_tmap_1(sK0,sK1,X4,X3,X5) = k2_partfun1(u1_struct_0(X4),u1_struct_0(sK1),X5,u1_struct_0(X3)) )
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f378])).

fof(f380,plain,
    ( spl5_57
    | ~ spl5_18
    | spl5_19
    | ~ spl5_17
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f371,f309,f138,f146,f142,f378])).

fof(f142,plain,
    ( spl5_18
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f146,plain,
    ( spl5_19
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f138,plain,
    ( spl5_17
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f309,plain,
    ( spl5_44
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | k3_tmap_1(X3,sK1,X1,X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X2,u1_struct_0(X0))
        | ~ m1_pre_topc(X1,X3)
        | ~ m1_pre_topc(X0,X3)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f371,plain,
    ( ! [X4,X5,X3] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X3,X4)
        | k3_tmap_1(sK0,sK1,X4,X3,X5) = k2_partfun1(u1_struct_0(X4),u1_struct_0(sK1),X5,u1_struct_0(X3))
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_pre_topc(X3,sK0)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) )
    | ~ spl5_17
    | ~ spl5_44 ),
    inference(resolution,[],[f310,f139])).

fof(f139,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f138])).

fof(f310,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ m1_pre_topc(X0,X1)
        | k3_tmap_1(X3,sK1,X1,X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X2,u1_struct_0(X0))
        | ~ m1_pre_topc(X1,X3)
        | ~ m1_pre_topc(X0,X3)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) )
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f309])).

fof(f311,plain,
    ( spl5_16
    | ~ spl5_15
    | spl5_44
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f305,f126,f309,f130,f134])).

fof(f305,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(X0,X3)
        | ~ m1_pre_topc(X1,X3)
        | k3_tmap_1(X3,sK1,X1,X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X2,u1_struct_0(X0))
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_14 ),
    inference(resolution,[],[f60,f127])).

fof(f127,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f286,plain,
    ( ~ spl5_14
    | spl5_37 ),
    inference(avatar_split_clause,[],[f285,f251,f126])).

fof(f251,plain,
    ( spl5_37
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f285,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_37 ),
    inference(resolution,[],[f252,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f252,plain,
    ( ~ l1_struct_0(sK1)
    | spl5_37 ),
    inference(avatar_component_clause,[],[f251])).

fof(f254,plain,
    ( spl5_16
    | ~ spl5_37
    | ~ spl5_20
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f228,f201,f150,f251,f134])).

fof(f150,plain,
    ( spl5_20
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f201,plain,
    ( spl5_27
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f228,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_27 ),
    inference(superposition,[],[f59,f202])).

fof(f202,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f201])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f217,plain,
    ( ~ spl5_22
    | ~ spl5_5
    | spl5_26 ),
    inference(avatar_split_clause,[],[f215,f198,f90,f160])).

fof(f198,plain,
    ( spl5_26
  <=> r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f215,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | spl5_26 ),
    inference(resolution,[],[f199,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f199,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f198])).

fof(f214,plain,
    ( ~ spl5_9
    | ~ spl5_8
    | ~ spl5_6
    | ~ spl5_26
    | spl5_27
    | spl5_30
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f195,f186,f212,f201,f198,f94,f102,f106])).

fof(f212,plain,
    ( spl5_30
  <=> v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f195,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ spl5_24 ),
    inference(superposition,[],[f67,f187])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X3,X2))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f210,plain,
    ( ~ spl5_9
    | ~ spl5_8
    | ~ spl5_6
    | ~ spl5_26
    | spl5_27
    | spl5_29
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f194,f186,f208,f201,f198,f94,f102,f106])).

fof(f208,plain,
    ( spl5_29
  <=> v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f194,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ spl5_24 ),
    inference(superposition,[],[f69,f187])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

% (31278)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f206,plain,
    ( ~ spl5_9
    | ~ spl5_8
    | ~ spl5_6
    | ~ spl5_26
    | spl5_27
    | spl5_28
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f193,f186,f204,f201,f198,f94,f102,f106])).

fof(f204,plain,
    ( spl5_28
  <=> m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f193,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ spl5_24 ),
    inference(superposition,[],[f71,f187])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f188,plain,
    ( spl5_24
    | ~ spl5_5
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f183,f168,f90,f186])).

fof(f168,plain,
    ( spl5_23
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f183,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ spl5_5
    | ~ spl5_23 ),
    inference(resolution,[],[f169,f91])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f168])).

fof(f182,plain,
    ( ~ spl5_17
    | ~ spl5_12
    | spl5_22 ),
    inference(avatar_split_clause,[],[f179,f160,f118,f138])).

fof(f179,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_12
    | spl5_22 ),
    inference(resolution,[],[f178,f119])).

fof(f119,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | spl5_22 ),
    inference(resolution,[],[f161,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f161,plain,
    ( ~ l1_pre_topc(sK2)
    | spl5_22 ),
    inference(avatar_component_clause,[],[f160])).

fof(f177,plain,
    ( ~ spl5_18
    | ~ spl5_17
    | ~ spl5_12
    | spl5_21 ),
    inference(avatar_split_clause,[],[f172,f157,f118,f138,f142])).

fof(f172,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_12
    | spl5_21 ),
    inference(resolution,[],[f171,f119])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl5_21 ),
    inference(resolution,[],[f158,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f158,plain,
    ( ~ v2_pre_topc(sK2)
    | spl5_21 ),
    inference(avatar_component_clause,[],[f157])).

fof(f170,plain,
    ( spl5_13
    | ~ spl5_21
    | ~ spl5_22
    | spl5_16
    | ~ spl5_15
    | ~ spl5_14
    | ~ spl5_9
    | ~ spl5_6
    | spl5_23
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f153,f102,f168,f94,f106,f126,f130,f134,f160,f157,f122])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl5_8 ),
    inference(resolution,[],[f61,f103])).

fof(f103,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f152,plain,(
    spl5_20 ),
    inference(avatar_split_clause,[],[f55,f150])).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f148,plain,(
    ~ spl5_19 ),
    inference(avatar_split_clause,[],[f39,f146])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) )
    & m1_pre_topc(sK3,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v5_pre_topc(sK4,sK2,sK1)
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f37,f36,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                        & m1_pre_topc(X3,X2)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(sK0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(sK0,X1,X2,X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(sK0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(sK0,X1,X2,X3,X4)) )
                      & m1_pre_topc(X3,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k3_tmap_1(sK0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,X2,X3,X4),X3,X1)
                      | ~ v1_funct_2(k3_tmap_1(sK0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(k3_tmap_1(sK0,X1,X2,X3,X4)) )
                    & m1_pre_topc(X3,X2)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v5_pre_topc(X4,X2,X1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,X2,X3,X4),X3,sK1)
                    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1))
                    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X2,X3,X4)) )
                  & m1_pre_topc(X3,X2)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                  & v5_pre_topc(X4,X2,sK1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,X2,X3,X4),X3,sK1)
                  | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1))
                  | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X2,X3,X4)) )
                & m1_pre_topc(X3,X2)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                & v5_pre_topc(X4,X2,sK1)
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,X3,X4),X3,sK1)
                | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1))
                | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X3,X4)) )
              & m1_pre_topc(X3,sK2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
              & v5_pre_topc(X4,sK2,sK1)
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
              | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,X3,X4),X3,sK1)
              | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1))
              | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X3,X4)) )
            & m1_pre_topc(X3,sK2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
            & v5_pre_topc(X4,sK2,sK1)
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
            | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,X4),sK3,sK1)
            | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,X4),u1_struct_0(sK3),u1_struct_0(sK1))
            | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,X4)) )
          & m1_pre_topc(sK3,sK2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v5_pre_topc(X4,sK2,sK1)
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,X4),sK3,sK1)
          | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,X4),u1_struct_0(sK3),u1_struct_0(sK1))
          | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,X4)) )
        & m1_pre_topc(sK3,sK2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v5_pre_topc(X4,sK2,sK1)
        & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) )
      & m1_pre_topc(sK3,sK2)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v5_pre_topc(sK4,sK2,sK1)
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      & m1_pre_topc(X3,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      & m1_pre_topc(X3,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X3,X2)
                         => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

% (31289)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f12,conjecture,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_tmap_1)).

fof(f144,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f40,f142])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f140,plain,(
    spl5_17 ),
    inference(avatar_split_clause,[],[f41,f138])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f136,plain,(
    ~ spl5_16 ),
    inference(avatar_split_clause,[],[f42,f134])).

fof(f42,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f132,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f43,f130])).

fof(f43,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f128,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f44,f126])).

fof(f44,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f124,plain,(
    ~ spl5_13 ),
    inference(avatar_split_clause,[],[f45,f122])).

fof(f45,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f120,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f46,f118])).

fof(f46,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f116,plain,(
    ~ spl5_11 ),
    inference(avatar_split_clause,[],[f47,f114])).

fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f112,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f48,f110])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f108,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f49,f106])).

fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f50,f102])).

fof(f50,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f100,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f51,f98])).

fof(f51,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f52,f94])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f53,f90])).

fof(f53,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f54,f86,f83,f80,f77])).

fof(f77,plain,
    ( spl5_1
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f80,plain,
    ( spl5_2
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f86,plain,
    ( spl5_4
  <=> m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f54,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f38])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 19:24:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (31275)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (31275)Refutation not found, incomplete strategy% (31275)------------------------------
% 0.21/0.48  % (31275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31275)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (31275)Memory used [KB]: 10746
% 0.21/0.48  % (31275)Time elapsed: 0.036 s
% 0.21/0.48  % (31275)------------------------------
% 0.21/0.48  % (31275)------------------------------
% 0.21/0.50  % (31288)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (31280)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (31284)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (31276)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.53  % (31283)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.53  % (31280)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f545,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f88,f92,f96,f100,f104,f108,f112,f116,f120,f124,f128,f132,f136,f140,f144,f148,f152,f170,f177,f182,f188,f206,f210,f214,f217,f254,f286,f311,f380,f502,f522,f534,f535,f540,f543,f544])).
% 0.21/0.53  fof(f544,plain,(
% 0.21/0.53    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) != k2_tmap_1(sK2,sK1,sK4,sK3) | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.53  fof(f543,plain,(
% 0.21/0.53    spl5_13 | ~spl5_21 | ~spl5_22 | spl5_16 | ~spl5_15 | ~spl5_14 | ~spl5_9 | ~spl5_8 | ~spl5_7 | ~spl5_6 | spl5_11 | ~spl5_5 | spl5_87),
% 0.21/0.53    inference(avatar_split_clause,[],[f541,f538,f90,f114,f94,f98,f102,f106,f126,f130,f134,f160,f157,f122])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    spl5_13 <=> v2_struct_0(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    spl5_21 <=> v2_pre_topc(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    spl5_22 <=> l1_pre_topc(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    spl5_16 <=> v2_struct_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    spl5_15 <=> v2_pre_topc(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    spl5_14 <=> l1_pre_topc(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    spl5_9 <=> v1_funct_1(sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    spl5_8 <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    spl5_7 <=> v5_pre_topc(sK4,sK2,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    spl5_6 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    spl5_11 <=> v2_struct_0(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    spl5_5 <=> m1_pre_topc(sK3,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.53  fof(f538,plain,(
% 0.21/0.53    spl5_87 <=> v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 0.21/0.53  fof(f541,plain,(
% 0.21/0.53    ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(sK4,sK2,sK1) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl5_87),
% 0.21/0.53    inference(resolution,[],[f539,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tmap_1)).
% 0.21/0.53  fof(f539,plain,(
% 0.21/0.53    ~v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1) | spl5_87),
% 0.21/0.53    inference(avatar_component_clause,[],[f538])).
% 0.21/0.53  fof(f540,plain,(
% 0.21/0.53    ~spl5_87 | spl5_3 | ~spl5_83),
% 0.21/0.53    inference(avatar_split_clause,[],[f536,f520,f83,f538])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    spl5_3 <=> v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.53  fof(f520,plain,(
% 0.21/0.53    spl5_83 <=> k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).
% 0.21/0.53  fof(f536,plain,(
% 0.21/0.53    ~v5_pre_topc(k2_tmap_1(sK2,sK1,sK4,sK3),sK3,sK1) | (spl5_3 | ~spl5_83)),
% 0.21/0.53    inference(forward_demodulation,[],[f84,f521])).
% 0.21/0.53  fof(f521,plain,(
% 0.21/0.53    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~spl5_83),
% 0.21/0.53    inference(avatar_component_clause,[],[f520])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) | spl5_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f83])).
% 0.21/0.53  fof(f535,plain,(
% 0.21/0.53    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) != k2_tmap_1(sK2,sK1,sK4,sK3) | v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.53  fof(f534,plain,(
% 0.21/0.53    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) != k2_tmap_1(sK2,sK1,sK4,sK3) | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))),
% 0.21/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.53  fof(f522,plain,(
% 0.21/0.53    ~spl5_9 | ~spl5_8 | spl5_83 | ~spl5_6 | ~spl5_24 | ~spl5_79),
% 0.21/0.53    inference(avatar_split_clause,[],[f518,f500,f186,f94,f520,f102,f106])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    spl5_24 <=> k2_tmap_1(sK2,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.53  fof(f500,plain,(
% 0.21/0.53    spl5_79 <=> ! [X0] : (~v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) | k3_tmap_1(sK0,sK1,sK2,sK3,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).
% 0.21/0.53  fof(f518,plain,(
% 0.21/0.53    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_tmap_1(sK2,sK1,sK4,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | (~spl5_6 | ~spl5_24 | ~spl5_79)),
% 0.21/0.53    inference(forward_demodulation,[],[f515,f187])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    k2_tmap_1(sK2,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | ~spl5_24),
% 0.21/0.53    inference(avatar_component_clause,[],[f186])).
% 0.21/0.53  fof(f515,plain,(
% 0.21/0.53    k3_tmap_1(sK0,sK1,sK2,sK3,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | (~spl5_6 | ~spl5_79)),
% 0.21/0.53    inference(resolution,[],[f501,f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~spl5_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f94])).
% 0.21/0.53  fof(f501,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | k3_tmap_1(sK0,sK1,sK2,sK3,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3)) | ~v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(X0)) ) | ~spl5_79),
% 0.21/0.53    inference(avatar_component_clause,[],[f500])).
% 0.21/0.53  fof(f502,plain,(
% 0.21/0.53    ~spl5_12 | spl5_79 | ~spl5_5 | ~spl5_10 | ~spl5_57),
% 0.21/0.53    inference(avatar_split_clause,[],[f495,f378,f110,f90,f500,f118])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    spl5_12 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    spl5_10 <=> m1_pre_topc(sK3,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.53  fof(f378,plain,(
% 0.21/0.53    spl5_57 <=> ! [X3,X5,X4] : (~m1_pre_topc(X3,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(X5) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X4,sK0) | k3_tmap_1(sK0,sK1,X4,X3,X5) = k2_partfun1(u1_struct_0(X4),u1_struct_0(sK1),X5,u1_struct_0(X3)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 0.21/0.53  fof(f495,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK0) | k3_tmap_1(sK0,sK1,sK2,sK3,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3))) ) | (~spl5_5 | ~spl5_10 | ~spl5_57)),
% 0.21/0.53    inference(resolution,[],[f488,f91])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    m1_pre_topc(sK3,sK2) | ~spl5_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f90])).
% 0.21/0.53  fof(f488,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(sK3,X1) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(sK0,sK1,X1,sK3,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X0,u1_struct_0(sK3))) ) | (~spl5_10 | ~spl5_57)),
% 0.21/0.53    inference(resolution,[],[f379,f111])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    m1_pre_topc(sK3,sK0) | ~spl5_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f110])).
% 0.21/0.53  fof(f379,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~m1_pre_topc(X3,sK0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(X5) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X4,sK0) | k3_tmap_1(sK0,sK1,X4,X3,X5) = k2_partfun1(u1_struct_0(X4),u1_struct_0(sK1),X5,u1_struct_0(X3))) ) | ~spl5_57),
% 0.21/0.53    inference(avatar_component_clause,[],[f378])).
% 0.21/0.53  fof(f380,plain,(
% 0.21/0.53    spl5_57 | ~spl5_18 | spl5_19 | ~spl5_17 | ~spl5_44),
% 0.21/0.53    inference(avatar_split_clause,[],[f371,f309,f138,f146,f142,f378])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    spl5_18 <=> v2_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    spl5_19 <=> v2_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    spl5_17 <=> l1_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.53  fof(f309,plain,(
% 0.21/0.53    spl5_44 <=> ! [X1,X3,X0,X2] : (~m1_pre_topc(X0,X1) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | k3_tmap_1(X3,sK1,X1,X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(X0,X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 0.21/0.53  fof(f371,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X3,X4) | k3_tmap_1(sK0,sK1,X4,X3,X5) = k2_partfun1(u1_struct_0(X4),u1_struct_0(sK1),X5,u1_struct_0(X3)) | ~m1_pre_topc(X4,sK0) | ~m1_pre_topc(X3,sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))) ) | (~spl5_17 | ~spl5_44)),
% 0.21/0.53    inference(resolution,[],[f310,f139])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    l1_pre_topc(sK0) | ~spl5_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f138])).
% 0.21/0.53  fof(f310,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X3) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~m1_pre_topc(X0,X1) | k3_tmap_1(X3,sK1,X1,X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(X0,X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))) ) | ~spl5_44),
% 0.21/0.53    inference(avatar_component_clause,[],[f309])).
% 0.21/0.53  fof(f311,plain,(
% 0.21/0.53    spl5_16 | ~spl5_15 | spl5_44 | ~spl5_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f305,f126,f309,f130,f134])).
% 0.21/0.53  fof(f305,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X0,X3) | ~m1_pre_topc(X1,X3) | k3_tmap_1(X3,sK1,X1,X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X2,u1_struct_0(X0)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_14),
% 0.21/0.53    inference(resolution,[],[f60,f127])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    l1_pre_topc(sK1) | ~spl5_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f126])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.21/0.53  fof(f286,plain,(
% 0.21/0.53    ~spl5_14 | spl5_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f285,f251,f126])).
% 0.21/0.53  fof(f251,plain,(
% 0.21/0.53    spl5_37 <=> l1_struct_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.21/0.53  fof(f285,plain,(
% 0.21/0.53    ~l1_pre_topc(sK1) | spl5_37),
% 0.21/0.53    inference(resolution,[],[f252,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.53  fof(f252,plain,(
% 0.21/0.53    ~l1_struct_0(sK1) | spl5_37),
% 0.21/0.53    inference(avatar_component_clause,[],[f251])).
% 0.21/0.53  fof(f254,plain,(
% 0.21/0.53    spl5_16 | ~spl5_37 | ~spl5_20 | ~spl5_27),
% 0.21/0.53    inference(avatar_split_clause,[],[f228,f201,f150,f251,f134])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    spl5_20 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    spl5_27 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.53  fof(f228,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl5_27),
% 0.21/0.53    inference(superposition,[],[f59,f202])).
% 0.21/0.53  fof(f202,plain,(
% 0.21/0.53    k1_xboole_0 = u1_struct_0(sK1) | ~spl5_27),
% 0.21/0.53    inference(avatar_component_clause,[],[f201])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.53  fof(f217,plain,(
% 0.21/0.53    ~spl5_22 | ~spl5_5 | spl5_26),
% 0.21/0.53    inference(avatar_split_clause,[],[f215,f198,f90,f160])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    spl5_26 <=> r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    ~m1_pre_topc(sK3,sK2) | ~l1_pre_topc(sK2) | spl5_26),
% 0.21/0.53    inference(resolution,[],[f199,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    ~r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) | spl5_26),
% 0.21/0.53    inference(avatar_component_clause,[],[f198])).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    ~spl5_9 | ~spl5_8 | ~spl5_6 | ~spl5_26 | spl5_27 | spl5_30 | ~spl5_24),
% 0.21/0.53    inference(avatar_split_clause,[],[f195,f186,f212,f201,f198,f94,f102,f106])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    spl5_30 <=> v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) | k1_xboole_0 = u1_struct_0(sK1) | ~r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~spl5_24),
% 0.21/0.53    inference(superposition,[],[f67,f187])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X3,X2)) | k1_xboole_0 = X1 | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.53    inference(flattening,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    ~spl5_9 | ~spl5_8 | ~spl5_6 | ~spl5_26 | spl5_27 | spl5_29 | ~spl5_24),
% 0.21/0.53    inference(avatar_split_clause,[],[f194,f186,f208,f201,f198,f94,f102,f106])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    spl5_29 <=> v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | k1_xboole_0 = u1_struct_0(sK1) | ~r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~spl5_24),
% 0.21/0.53    inference(superposition,[],[f69,f187])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | k1_xboole_0 = X1 | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  % (31278)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    ~spl5_9 | ~spl5_8 | ~spl5_6 | ~spl5_26 | spl5_27 | spl5_28 | ~spl5_24),
% 0.21/0.53    inference(avatar_split_clause,[],[f193,f186,f204,f201,f198,f94,f102,f106])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    spl5_28 <=> m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | k1_xboole_0 = u1_struct_0(sK1) | ~r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~spl5_24),
% 0.21/0.53    inference(superposition,[],[f71,f187])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | k1_xboole_0 = X1 | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    spl5_24 | ~spl5_5 | ~spl5_23),
% 0.21/0.53    inference(avatar_split_clause,[],[f183,f168,f90,f186])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    spl5_23 <=> ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    k2_tmap_1(sK2,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | (~spl5_5 | ~spl5_23)),
% 0.21/0.53    inference(resolution,[],[f169,f91])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | ~spl5_23),
% 0.21/0.53    inference(avatar_component_clause,[],[f168])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    ~spl5_17 | ~spl5_12 | spl5_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f179,f160,f118,f138])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | (~spl5_12 | spl5_22)),
% 0.21/0.53    inference(resolution,[],[f178,f119])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0) | ~spl5_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f118])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) ) | spl5_22),
% 0.21/0.53    inference(resolution,[],[f161,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    ~l1_pre_topc(sK2) | spl5_22),
% 0.21/0.53    inference(avatar_component_clause,[],[f160])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ~spl5_18 | ~spl5_17 | ~spl5_12 | spl5_21),
% 0.21/0.53    inference(avatar_split_clause,[],[f172,f157,f118,f138,f142])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl5_12 | spl5_21)),
% 0.21/0.53    inference(resolution,[],[f171,f119])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl5_21),
% 0.21/0.53    inference(resolution,[],[f158,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    ~v2_pre_topc(sK2) | spl5_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f157])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    spl5_13 | ~spl5_21 | ~spl5_22 | spl5_16 | ~spl5_15 | ~spl5_14 | ~spl5_9 | ~spl5_6 | spl5_23 | ~spl5_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f153,f102,f168,f94,f106,f126,f130,f134,f160,f157,f122])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl5_8),
% 0.21/0.53    inference(resolution,[],[f61,f103])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl5_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f102])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    spl5_20),
% 0.21/0.53    inference(avatar_split_clause,[],[f55,f150])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    ~spl5_19),
% 0.21/0.53    inference(avatar_split_clause,[],[f39,f146])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    (((((~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))) & m1_pre_topc(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(sK4,sK2,sK1) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f37,f36,f35,f34,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,X2,X3,X4),X3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(X4,X2,sK1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,X2,X3,X4),X3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(X4,X2,sK1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,X3,X4),X3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X3,X4))) & m1_pre_topc(X3,sK2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,X3,X4),X3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,X3,X4),u1_struct_0(X3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X3,X4))) & m1_pre_topc(X3,sK2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,X4),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,X4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,X4))) & m1_pre_topc(sK3,sK2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ? [X4] : ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,X4),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,X4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,X4))) & m1_pre_topc(sK3,sK2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) => ((~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))) & m1_pre_topc(sK3,sK2) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(sK4,sK2,sK1) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) & m1_pre_topc(X3,X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)))))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f12])).
% 0.21/0.54  % (31289)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.54  fof(f12,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)))))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_tmap_1)).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    spl5_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f40,f142])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    v2_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    spl5_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f41,f138])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    l1_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ~spl5_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f42,f134])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ~v2_struct_0(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    spl5_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f43,f130])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    v2_pre_topc(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    spl5_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f44,f126])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    l1_pre_topc(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ~spl5_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f45,f122])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ~v2_struct_0(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    spl5_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f46,f118])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    m1_pre_topc(sK2,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ~spl5_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f47,f114])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ~v2_struct_0(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    spl5_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f48,f110])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    m1_pre_topc(sK3,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    spl5_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f49,f106])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    v1_funct_1(sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    spl5_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f50,f102])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    spl5_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f51,f98])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    v5_pre_topc(sK4,sK2,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    spl5_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f52,f94])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    spl5_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f53,f90])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    m1_pre_topc(sK3,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f54,f86,f83,f80,f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    spl5_1 <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    spl5_2 <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    spl5_4 <=> m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (31280)------------------------------
% 0.21/0.54  % (31280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31280)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (31280)Memory used [KB]: 11129
% 0.21/0.54  % (31280)Time elapsed: 0.090 s
% 0.21/0.54  % (31280)------------------------------
% 0.21/0.54  % (31280)------------------------------
% 0.21/0.54  % (31273)Success in time 0.172 s
%------------------------------------------------------------------------------
