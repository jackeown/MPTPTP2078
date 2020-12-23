%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t129_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:06 EDT 2019

% Result     : Theorem 30.38s
% Output     : Refutation 30.38s
% Verified   : 
% Statistics : Number of formulae       :  502 (1503 expanded)
%              Number of leaves         :  150 ( 747 expanded)
%              Depth                    :   11
%              Number of atoms          : 3078 (14995 expanded)
%              Number of equality atoms :   59 ( 151 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3565,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f262,f269,f276,f283,f290,f297,f304,f311,f318,f325,f332,f339,f350,f357,f364,f385,f413,f476,f479,f482,f549,f737,f750,f796,f846,f852,f990,f1016,f1170,f1202,f1446,f1854,f1936,f1939,f1953,f1969,f2093,f2124,f2129,f2135,f2156,f2164,f2202,f2204,f2219,f2222,f2226,f2233,f2241,f2258,f2303,f2401,f2404,f2414,f2425,f2433,f2462,f2466,f2472,f2602,f2635,f2828,f2833,f3083,f3090,f3097,f3105,f3108,f3111,f3112,f3115,f3116,f3117,f3136,f3139,f3190,f3205,f3209,f3229,f3255,f3296,f3345,f3408,f3426,f3430,f3439,f3446,f3455,f3463,f3522,f3529,f3530,f3537,f3564])).

fof(f3564,plain,
    ( spl14_0
    | ~ spl14_5
    | spl14_12
    | ~ spl14_19
    | spl14_14
    | ~ spl14_21
    | spl14_52
    | ~ spl14_454 ),
    inference(avatar_split_clause,[],[f3539,f2562,f451,f327,f306,f320,f299,f271,f257])).

fof(f257,plain,
    ( spl14_0
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_0])])).

fof(f271,plain,
    ( spl14_5
  <=> ~ l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f299,plain,
    ( spl14_12
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f320,plain,
    ( spl14_19
  <=> ~ m1_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).

fof(f306,plain,
    ( spl14_14
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f327,plain,
    ( spl14_21
  <=> ~ m1_pre_topc(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_21])])).

fof(f451,plain,
    ( spl14_52
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_tsep_1(sK2,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_52])])).

fof(f2562,plain,
    ( spl14_454
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_tsep_1(sK2,sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_454])])).

fof(f3539,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl14_454 ),
    inference(superposition,[],[f2563,f227])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t129_tmap_1.p',commutativity_k1_tsep_1)).

fof(f2563,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_tsep_1(sK2,sK5,sK4),sK3)
    | ~ spl14_454 ),
    inference(avatar_component_clause,[],[f2562])).

fof(f3537,plain,
    ( ~ spl14_354
    | ~ spl14_438
    | spl14_455 ),
    inference(avatar_contradiction_clause,[],[f3534])).

fof(f3534,plain,
    ( $false
    | ~ spl14_354
    | ~ spl14_438
    | ~ spl14_455 ),
    inference(unit_resulting_resolution,[],[f2413,f2566,f1965,f191])).

fof(f191,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f120,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
            & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
            & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
            & v1_funct_1(X2) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
          | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
          | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f119])).

fof(f119,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(flattening,[],[f118])).

fof(f118,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1965,plain,
    ( sP0(sK3,sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),sK5,sK2)
    | ~ spl14_354 ),
    inference(avatar_component_clause,[],[f1964])).

fof(f1964,plain,
    ( spl14_354
  <=> sP0(sK3,sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_354])])).

fof(f2566,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_tsep_1(sK2,sK5,sK4),sK3)
    | ~ spl14_455 ),
    inference(avatar_component_clause,[],[f2565])).

fof(f2565,plain,
    ( spl14_455
  <=> ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_tsep_1(sK2,sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_455])])).

fof(f2413,plain,
    ( sP1(sK2,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),sK4,sK3)
    | ~ spl14_438 ),
    inference(avatar_component_clause,[],[f2412])).

fof(f2412,plain,
    ( spl14_438
  <=> sP1(sK2,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_438])])).

fof(f3530,plain,
    ( k2_tmap_1(sK2,sK3,sK6,sK5) != k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))
    | k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)) != k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),sK5,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,sK5),sK5,sK3) ),
    introduced(theory_axiom,[])).

fof(f3529,plain,
    ( spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | spl14_7
    | ~ spl14_8
    | ~ spl14_10
    | ~ spl14_20
    | ~ spl14_42
    | ~ spl14_338
    | ~ spl14_448
    | ~ spl14_450
    | spl14_547 ),
    inference(avatar_contradiction_clause,[],[f3523])).

fof(f3523,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_10
    | ~ spl14_20
    | ~ spl14_42
    | ~ spl14_338
    | ~ spl14_448
    | ~ spl14_450
    | ~ spl14_547 ),
    inference(unit_resulting_resolution,[],[f261,f268,f275,f282,f289,f296,f331,f1850,f421,f2446,f2452,f3521,f246])).

fof(f246,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f103])).

fof(f103,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t129_tmap_1.p',dt_k3_tmap_1)).

fof(f3521,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl14_547 ),
    inference(avatar_component_clause,[],[f3520])).

fof(f3520,plain,
    ( spl14_547
  <=> ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_547])])).

fof(f2452,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))))
    | ~ spl14_450 ),
    inference(avatar_component_clause,[],[f2451])).

fof(f2451,plain,
    ( spl14_450
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_450])])).

fof(f2446,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))
    | ~ spl14_448 ),
    inference(avatar_component_clause,[],[f2445])).

fof(f2445,plain,
    ( spl14_448
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_448])])).

fof(f421,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))
    | ~ spl14_42 ),
    inference(avatar_component_clause,[],[f420])).

fof(f420,plain,
    ( spl14_42
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_42])])).

fof(f1850,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK5,sK4),sK2)
    | ~ spl14_338 ),
    inference(avatar_component_clause,[],[f1849])).

fof(f1849,plain,
    ( spl14_338
  <=> m1_pre_topc(k1_tsep_1(sK2,sK5,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_338])])).

fof(f331,plain,
    ( m1_pre_topc(sK5,sK2)
    | ~ spl14_20 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl14_20
  <=> m1_pre_topc(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_20])])).

fof(f296,plain,
    ( l1_pre_topc(sK3)
    | ~ spl14_10 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl14_10
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f289,plain,
    ( v2_pre_topc(sK3)
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl14_8
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f282,plain,
    ( ~ v2_struct_0(sK3)
    | ~ spl14_7 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl14_7
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).

fof(f275,plain,
    ( l1_pre_topc(sK2)
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl14_4
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f268,plain,
    ( v2_pre_topc(sK2)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl14_2
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f261,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl14_1
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f3522,plain,
    ( spl14_544
    | ~ spl14_547
    | ~ spl14_535
    | ~ spl14_537
    | ~ spl14_337
    | ~ spl14_21
    | spl14_14
    | ~ spl14_162
    | ~ spl14_486 ),
    inference(avatar_split_clause,[],[f2837,f2826,f850,f306,f327,f1846,f3453,f3437,f3520,f3514])).

fof(f3514,plain,
    ( spl14_544
  <=> k2_tmap_1(sK2,sK3,sK6,sK5) = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_544])])).

fof(f3437,plain,
    ( spl14_535
  <=> ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_535])])).

fof(f3453,plain,
    ( spl14_537
  <=> ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_537])])).

fof(f1846,plain,
    ( spl14_337
  <=> ~ m1_pre_topc(sK5,k1_tsep_1(sK2,sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_337])])).

fof(f850,plain,
    ( spl14_162
  <=> ! [X6] :
        ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X6,k2_tmap_1(sK2,sK3,sK6,sK5))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | k2_tmap_1(sK2,sK3,sK6,sK5) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_162])])).

fof(f2826,plain,
    ( spl14_486
  <=> ! [X1] :
        ( r2_funct_2(u1_struct_0(X1),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),X1,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))),k2_tmap_1(sK2,sK3,sK6,X1))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK2)
        | ~ m1_pre_topc(X1,k1_tsep_1(sK2,sK5,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_486])])).

fof(f2837,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK5,k1_tsep_1(sK2,sK5,sK4))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | k2_tmap_1(sK2,sK3,sK6,sK5) = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))
    | ~ spl14_162
    | ~ spl14_486 ),
    inference(resolution,[],[f2827,f851])).

fof(f851,plain,
    ( ! [X6] :
        ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X6,k2_tmap_1(sK2,sK3,sK6,sK5))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | k2_tmap_1(sK2,sK3,sK6,sK5) = X6 )
    | ~ spl14_162 ),
    inference(avatar_component_clause,[],[f850])).

fof(f2827,plain,
    ( ! [X1] :
        ( r2_funct_2(u1_struct_0(X1),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),X1,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))),k2_tmap_1(sK2,sK3,sK6,X1))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK2)
        | ~ m1_pre_topc(X1,k1_tsep_1(sK2,sK5,sK4)) )
    | ~ spl14_486 ),
    inference(avatar_component_clause,[],[f2826])).

fof(f3463,plain,
    ( spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | spl14_7
    | ~ spl14_8
    | ~ spl14_10
    | ~ spl14_20
    | ~ spl14_42
    | ~ spl14_338
    | ~ spl14_448
    | ~ spl14_450
    | spl14_537 ),
    inference(avatar_contradiction_clause,[],[f3457])).

fof(f3457,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_10
    | ~ spl14_20
    | ~ spl14_42
    | ~ spl14_338
    | ~ spl14_448
    | ~ spl14_450
    | ~ spl14_537 ),
    inference(unit_resulting_resolution,[],[f261,f268,f275,f282,f289,f296,f331,f1850,f421,f2446,f2452,f3454,f244])).

fof(f244,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f3454,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))))
    | ~ spl14_537 ),
    inference(avatar_component_clause,[],[f3453])).

fof(f3455,plain,
    ( ~ spl14_537
    | spl14_327
    | ~ spl14_452 ),
    inference(avatar_split_clause,[],[f3447,f2460,f1816,f3453])).

fof(f1816,plain,
    ( spl14_327
  <=> ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_327])])).

fof(f2460,plain,
    ( spl14_452
  <=> k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)) = k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_452])])).

fof(f3447,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))))
    | ~ spl14_327
    | ~ spl14_452 ),
    inference(forward_demodulation,[],[f1817,f2461])).

fof(f2461,plain,
    ( k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)) = k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))
    | ~ spl14_452 ),
    inference(avatar_component_clause,[],[f2460])).

fof(f1817,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))))
    | ~ spl14_327 ),
    inference(avatar_component_clause,[],[f1816])).

fof(f3446,plain,
    ( spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | spl14_7
    | ~ spl14_8
    | ~ spl14_10
    | ~ spl14_20
    | ~ spl14_42
    | ~ spl14_338
    | ~ spl14_448
    | ~ spl14_450
    | spl14_535 ),
    inference(avatar_contradiction_clause,[],[f3440])).

fof(f3440,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_10
    | ~ spl14_20
    | ~ spl14_42
    | ~ spl14_338
    | ~ spl14_448
    | ~ spl14_450
    | ~ spl14_535 ),
    inference(unit_resulting_resolution,[],[f261,f268,f275,f282,f289,f296,f331,f1850,f421,f2446,f2452,f3438,f245])).

fof(f245,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f3438,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl14_535 ),
    inference(avatar_component_clause,[],[f3437])).

fof(f3439,plain,
    ( ~ spl14_535
    | spl14_325
    | ~ spl14_452 ),
    inference(avatar_split_clause,[],[f3410,f2460,f1810,f3437])).

fof(f1810,plain,
    ( spl14_325
  <=> ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_325])])).

fof(f3410,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl14_325
    | ~ spl14_452 ),
    inference(forward_demodulation,[],[f1811,f2461])).

fof(f1811,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl14_325 ),
    inference(avatar_component_clause,[],[f1810])).

fof(f3430,plain,
    ( spl14_0
    | ~ spl14_5
    | spl14_12
    | ~ spl14_19
    | spl14_14
    | ~ spl14_21
    | spl14_528
    | ~ spl14_336 ),
    inference(avatar_split_clause,[],[f3414,f1843,f3340,f327,f306,f320,f299,f271,f257])).

fof(f3340,plain,
    ( spl14_528
  <=> m1_pre_topc(sK5,k1_tsep_1(sK2,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_528])])).

fof(f1843,plain,
    ( spl14_336
  <=> m1_pre_topc(sK5,k1_tsep_1(sK2,sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_336])])).

fof(f3414,plain,
    ( m1_pre_topc(sK5,k1_tsep_1(sK2,sK4,sK5))
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl14_336 ),
    inference(superposition,[],[f1844,f227])).

fof(f1844,plain,
    ( m1_pre_topc(sK5,k1_tsep_1(sK2,sK5,sK4))
    | ~ spl14_336 ),
    inference(avatar_component_clause,[],[f1843])).

fof(f3426,plain,
    ( spl14_52
    | spl14_68 ),
    inference(avatar_split_clause,[],[f173,f508,f451])).

fof(f508,plain,
    ( spl14_68
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,sK5),sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_68])])).

fof(f173,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,sK5),sK5,sK3)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,sK5),sK5,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,sK4),sK4,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_tsep_1(sK2,sK4,sK5),sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))) )
    & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,sK5),sK5,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5))
        & m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,sK4),sK4,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) )
      | ( m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_tsep_1(sK2,sK4,sK5),sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))) ) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & r4_tsep_1(sK2,sK4,sK5)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f109,f114,f113,f112,f111,f110])).

fof(f110,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                            & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
                          | ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & r4_tsep_1(X0,X2,X3)
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
                      ( ( ~ m1_subset_1(k2_tmap_1(sK2,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X4,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X4,X3))
                        | ~ m1_subset_1(k2_tmap_1(sK2,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X4,X2),X2,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X4,X2))
                        | ~ m1_subset_1(k2_tmap_1(sK2,X1,X4,k1_tsep_1(sK2,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X4,k1_tsep_1(sK2,X2,X3)),k1_tsep_1(sK2,X2,X3),X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X4,k1_tsep_1(sK2,X2,X3)),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X4,k1_tsep_1(sK2,X2,X3))) )
                      & ( ( m1_subset_1(k2_tmap_1(sK2,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(sK2,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X4,X2)) )
                        | ( m1_subset_1(k2_tmap_1(sK2,X1,X4,k1_tsep_1(sK2,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X4,k1_tsep_1(sK2,X2,X3)),k1_tsep_1(sK2,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X4,k1_tsep_1(sK2,X2,X3)),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X4,k1_tsep_1(sK2,X2,X3))) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r4_tsep_1(sK2,X2,X3)
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f111,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
                        | ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r4_tsep_1(X0,X2,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k2_tmap_1(X0,sK3,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(k2_tmap_1(X0,sK3,X4,X3),X3,sK3)
                      | ~ v1_funct_2(k2_tmap_1(X0,sK3,X4,X3),u1_struct_0(X3),u1_struct_0(sK3))
                      | ~ v1_funct_1(k2_tmap_1(X0,sK3,X4,X3))
                      | ~ m1_subset_1(k2_tmap_1(X0,sK3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(k2_tmap_1(X0,sK3,X4,X2),X2,sK3)
                      | ~ v1_funct_2(k2_tmap_1(X0,sK3,X4,X2),u1_struct_0(X2),u1_struct_0(sK3))
                      | ~ v1_funct_1(k2_tmap_1(X0,sK3,X4,X2))
                      | ~ m1_subset_1(k2_tmap_1(X0,sK3,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))))
                      | ~ v5_pre_topc(k2_tmap_1(X0,sK3,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),sK3)
                      | ~ v1_funct_2(k2_tmap_1(X0,sK3,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))
                      | ~ v1_funct_1(k2_tmap_1(X0,sK3,X4,k1_tsep_1(X0,X2,X3))) )
                    & ( ( m1_subset_1(k2_tmap_1(X0,sK3,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                        & v5_pre_topc(k2_tmap_1(X0,sK3,X4,X3),X3,sK3)
                        & v1_funct_2(k2_tmap_1(X0,sK3,X4,X3),u1_struct_0(X3),u1_struct_0(sK3))
                        & v1_funct_1(k2_tmap_1(X0,sK3,X4,X3))
                        & m1_subset_1(k2_tmap_1(X0,sK3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                        & v5_pre_topc(k2_tmap_1(X0,sK3,X4,X2),X2,sK3)
                        & v1_funct_2(k2_tmap_1(X0,sK3,X4,X2),u1_struct_0(X2),u1_struct_0(sK3))
                        & v1_funct_1(k2_tmap_1(X0,sK3,X4,X2)) )
                      | ( m1_subset_1(k2_tmap_1(X0,sK3,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))))
                        & v5_pre_topc(k2_tmap_1(X0,sK3,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),sK3)
                        & v1_funct_2(k2_tmap_1(X0,sK3,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))
                        & v1_funct_1(k2_tmap_1(X0,sK3,X4,k1_tsep_1(X0,X2,X3))) ) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & r4_tsep_1(X0,X2,X3)
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                    | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                    | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                    | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                    | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                    | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
                    | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                    | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                  & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                      & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                      & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                      & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
                    | ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                      & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & r4_tsep_1(X0,X2,X3)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                  | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                  | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                  | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,sK4),sK4,X1)
                  | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,sK4),u1_struct_0(sK4),u1_struct_0(X1))
                  | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,sK4))
                  | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,sK4,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,sK4,X3)),k1_tsep_1(X0,sK4,X3),X1)
                  | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,sK4,X3)),u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))
                  | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,sK4,X3))) )
                & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                    & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                    & m1_subset_1(k2_tmap_1(X0,X1,X4,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                    & v5_pre_topc(k2_tmap_1(X0,X1,X4,sK4),sK4,X1)
                    & v1_funct_2(k2_tmap_1(X0,X1,X4,sK4),u1_struct_0(sK4),u1_struct_0(X1))
                    & v1_funct_1(k2_tmap_1(X0,X1,X4,sK4)) )
                  | ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,sK4,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))))
                    & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,sK4,X3)),k1_tsep_1(X0,sK4,X3),X1)
                    & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,sK4,X3)),u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))
                    & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,sK4,X3))) ) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & r4_tsep_1(X0,sK4,X3)
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
                | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
              & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                  & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                  & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                  & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
                | ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                  & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                  & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                  & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & r4_tsep_1(X0,X2,X3)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
              | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,sK5),sK5,X1)
              | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,sK5),u1_struct_0(sK5),u1_struct_0(X1))
              | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,sK5))
              | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
              | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
              | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
              | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))))
              | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,sK5)),k1_tsep_1(X0,X2,sK5),X1)
              | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,sK5)),u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))
              | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,sK5))) )
            & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                & v5_pre_topc(k2_tmap_1(X0,X1,X4,sK5),sK5,X1)
                & v1_funct_2(k2_tmap_1(X0,X1,X4,sK5),u1_struct_0(sK5),u1_struct_0(X1))
                & v1_funct_1(k2_tmap_1(X0,X1,X4,sK5))
                & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
              | ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))))
                & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,sK5)),k1_tsep_1(X0,X2,sK5),X1)
                & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,sK5)),u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))
                & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,sK5))) ) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & r4_tsep_1(X0,X2,sK5)
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
            | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
            | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
            | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
            | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
            | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
            | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
            | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
          & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
              & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
              & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
              & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
            | ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
              & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
              & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
              & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,sK6,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,sK6,X3),X3,X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,sK6,X3),u1_struct_0(X3),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,sK6,X3))
          | ~ m1_subset_1(k2_tmap_1(X0,X1,sK6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,sK6,X2),X2,X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,sK6,X2),u1_struct_0(X2),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,sK6,X2))
          | ~ m1_subset_1(k2_tmap_1(X0,X1,sK6,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,sK6,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,sK6,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,sK6,k1_tsep_1(X0,X2,X3))) )
        & ( ( m1_subset_1(k2_tmap_1(X0,X1,sK6,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,sK6,X3),X3,X1)
            & v1_funct_2(k2_tmap_1(X0,X1,sK6,X3),u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,sK6,X3))
            & m1_subset_1(k2_tmap_1(X0,X1,sK6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,sK6,X2),X2,X1)
            & v1_funct_2(k2_tmap_1(X0,X1,sK6,X2),u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,sK6,X2)) )
          | ( m1_subset_1(k2_tmap_1(X0,X1,sK6,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,sK6,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(k2_tmap_1(X0,X1,sK6,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,sK6,k1_tsep_1(X0,X2,X3))) ) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f109,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
                        | ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r4_tsep_1(X0,X2,X3)
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
    inference(flattening,[],[f108])).

fof(f108,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
                        | ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r4_tsep_1(X0,X2,X3)
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
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r4_tsep_1(X0,X2,X3)
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r4_tsep_1(X0,X2,X3)
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
                   => ( r4_tsep_1(X0,X2,X3)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                          <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                              & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
                 => ( r4_tsep_1(X0,X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                            & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t129_tmap_1.p',t129_tmap_1)).

fof(f3408,plain,
    ( spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | spl14_13
    | spl14_15
    | ~ spl14_18
    | ~ spl14_20
    | spl14_337 ),
    inference(avatar_contradiction_clause,[],[f3404])).

fof(f3404,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_13
    | ~ spl14_15
    | ~ spl14_18
    | ~ spl14_20
    | ~ spl14_337 ),
    inference(unit_resulting_resolution,[],[f261,f268,f275,f310,f303,f331,f324,f1847,f209])).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
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
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t129_tmap_1.p',t22_tsep_1)).

fof(f1847,plain,
    ( ~ m1_pre_topc(sK5,k1_tsep_1(sK2,sK5,sK4))
    | ~ spl14_337 ),
    inference(avatar_component_clause,[],[f1846])).

fof(f324,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ spl14_18 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl14_18
  <=> m1_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).

fof(f303,plain,
    ( ~ v2_struct_0(sK4)
    | ~ spl14_13 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl14_13
  <=> ~ v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).

fof(f310,plain,
    ( ~ v2_struct_0(sK5)
    | ~ spl14_15 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl14_15
  <=> ~ v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).

fof(f3345,plain,
    ( ~ spl14_465
    | ~ spl14_529
    | spl14_456
    | ~ spl14_84
    | ~ spl14_526 ),
    inference(avatar_split_clause,[],[f3336,f3294,f575,f2594,f3343,f2627])).

fof(f2627,plain,
    ( spl14_465
  <=> ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_465])])).

fof(f3343,plain,
    ( spl14_529
  <=> ~ m1_pre_topc(sK5,k1_tsep_1(sK2,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_529])])).

fof(f2594,plain,
    ( spl14_456
  <=> v2_struct_0(k1_tsep_1(sK2,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_456])])).

fof(f575,plain,
    ( spl14_84
  <=> sP0(sK3,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_84])])).

fof(f3294,plain,
    ( spl14_526
  <=> ! [X4] :
        ( ~ sP0(sK3,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X4,sK5)),X4,sK2)
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X4,sK5),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X4,sK5))),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X4,sK5),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X4,sK5))))
        | v2_struct_0(k1_tsep_1(sK2,X4,sK5))
        | ~ m1_pre_topc(sK5,k1_tsep_1(sK2,X4,sK5))
        | ~ m1_pre_topc(k1_tsep_1(sK2,X4,sK5),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_526])])).

fof(f3336,plain,
    ( v2_struct_0(k1_tsep_1(sK2,sK4,sK5))
    | ~ m1_pre_topc(sK5,k1_tsep_1(sK2,sK4,sK5))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ spl14_84
    | ~ spl14_526 ),
    inference(resolution,[],[f3333,f576])).

fof(f576,plain,
    ( sP0(sK3,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),sK4,sK2)
    | ~ spl14_84 ),
    inference(avatar_component_clause,[],[f575])).

fof(f3333,plain,
    ( ! [X0] :
        ( ~ sP0(sK3,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X0,sK5)),X0,sK2)
        | v2_struct_0(k1_tsep_1(sK2,X0,sK5))
        | ~ m1_pre_topc(sK5,k1_tsep_1(sK2,X0,sK5))
        | ~ m1_pre_topc(k1_tsep_1(sK2,X0,sK5),sK2) )
    | ~ spl14_526 ),
    inference(duplicate_literal_removal,[],[f3319])).

fof(f3319,plain,
    ( ! [X0] :
        ( ~ sP0(sK3,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X0,sK5)),X0,sK2)
        | v2_struct_0(k1_tsep_1(sK2,X0,sK5))
        | ~ m1_pre_topc(sK5,k1_tsep_1(sK2,X0,sK5))
        | ~ m1_pre_topc(k1_tsep_1(sK2,X0,sK5),sK2)
        | ~ sP0(sK3,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X0,sK5)),X0,sK2) )
    | ~ spl14_526 ),
    inference(resolution,[],[f3315,f197])).

fof(f197,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f123])).

fof(f123,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
      & ( ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
          & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f122])).

fof(f122,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(flattening,[],[f121])).

fof(f121,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( sP0(X1,X3,X4,X2,X0)
    <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3315,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X0,sK5),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X0,sK5))))
        | ~ sP0(sK3,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X0,sK5)),X0,sK2)
        | v2_struct_0(k1_tsep_1(sK2,X0,sK5))
        | ~ m1_pre_topc(sK5,k1_tsep_1(sK2,X0,sK5))
        | ~ m1_pre_topc(k1_tsep_1(sK2,X0,sK5),sK2) )
    | ~ spl14_526 ),
    inference(duplicate_literal_removal,[],[f3297])).

fof(f3297,plain,
    ( ! [X0] :
        ( ~ sP0(sK3,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X0,sK5)),X0,sK2)
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X0,sK5),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X0,sK5))))
        | v2_struct_0(k1_tsep_1(sK2,X0,sK5))
        | ~ m1_pre_topc(sK5,k1_tsep_1(sK2,X0,sK5))
        | ~ m1_pre_topc(k1_tsep_1(sK2,X0,sK5),sK2)
        | ~ sP0(sK3,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X0,sK5)),X0,sK2) )
    | ~ spl14_526 ),
    inference(resolution,[],[f3295,f198])).

fof(f198,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f123])).

fof(f3295,plain,
    ( ! [X4] :
        ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X4,sK5),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X4,sK5))),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ sP0(sK3,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X4,sK5)),X4,sK2)
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X4,sK5),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X4,sK5))))
        | v2_struct_0(k1_tsep_1(sK2,X4,sK5))
        | ~ m1_pre_topc(sK5,k1_tsep_1(sK2,X4,sK5))
        | ~ m1_pre_topc(k1_tsep_1(sK2,X4,sK5),sK2) )
    | ~ spl14_526 ),
    inference(avatar_component_clause,[],[f3294])).

fof(f3296,plain,
    ( spl14_526
    | spl14_68
    | ~ spl14_208 ),
    inference(avatar_split_clause,[],[f1123,f1014,f508,f3294])).

fof(f1014,plain,
    ( spl14_208
  <=> ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,X0,sK5,k2_tmap_1(sK2,sK3,sK6,X0)))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(sK5,X0)
        | k2_tmap_1(sK2,sK3,sK6,sK5) = k3_tmap_1(sK2,sK3,X0,sK5,k2_tmap_1(sK2,sK3,sK6,X0))
        | ~ m1_subset_1(k3_tmap_1(sK2,sK3,X0,sK5,k2_tmap_1(sK2,sK3,sK6,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,X0,sK5,k2_tmap_1(sK2,sK3,sK6,X0)),u1_struct_0(sK5),u1_struct_0(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_208])])).

fof(f1123,plain,
    ( ! [X4] :
        ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,sK5),sK5,sK3)
        | ~ sP0(sK3,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X4,sK5)),X4,sK2)
        | ~ m1_pre_topc(k1_tsep_1(sK2,X4,sK5),sK2)
        | ~ m1_pre_topc(sK5,k1_tsep_1(sK2,X4,sK5))
        | v2_struct_0(k1_tsep_1(sK2,X4,sK5))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X4,sK5),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X4,sK5))))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X4,sK5),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X4,sK5))),u1_struct_0(sK5),u1_struct_0(sK3)) )
    | ~ spl14_208 ),
    inference(duplicate_literal_removal,[],[f1110])).

fof(f1110,plain,
    ( ! [X4] :
        ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,sK5),sK5,sK3)
        | ~ sP0(sK3,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X4,sK5)),X4,sK2)
        | ~ m1_pre_topc(k1_tsep_1(sK2,X4,sK5),sK2)
        | ~ m1_pre_topc(sK5,k1_tsep_1(sK2,X4,sK5))
        | v2_struct_0(k1_tsep_1(sK2,X4,sK5))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X4,sK5),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X4,sK5))))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X4,sK5),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X4,sK5))),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ sP0(sK3,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X4,sK5)),X4,sK2) )
    | ~ spl14_208 ),
    inference(superposition,[],[f199,f1021])).

fof(f1021,plain,
    ( ! [X0] :
        ( k2_tmap_1(sK2,sK3,sK6,sK5) = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X0,sK5),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X0,sK5)))
        | ~ m1_pre_topc(k1_tsep_1(sK2,X0,sK5),sK2)
        | ~ m1_pre_topc(sK5,k1_tsep_1(sK2,X0,sK5))
        | v2_struct_0(k1_tsep_1(sK2,X0,sK5))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X0,sK5),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X0,sK5))))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X0,sK5),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X0,sK5))),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ sP0(sK3,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,X0,sK5)),X0,sK2) )
    | ~ spl14_208 ),
    inference(resolution,[],[f1015,f200])).

fof(f200,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f123])).

fof(f1015,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,X0,sK5,k2_tmap_1(sK2,sK3,sK6,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(sK5,X0)
        | k2_tmap_1(sK2,sK3,sK6,sK5) = k3_tmap_1(sK2,sK3,X0,sK5,k2_tmap_1(sK2,sK3,sK6,X0))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,X0,sK5,k2_tmap_1(sK2,sK3,sK6,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,X0,sK5,k2_tmap_1(sK2,sK3,sK6,X0)),u1_struct_0(sK5),u1_struct_0(sK3)) )
    | ~ spl14_208 ),
    inference(avatar_component_clause,[],[f1014])).

fof(f199,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f123])).

fof(f3255,plain,
    ( ~ spl14_83
    | ~ spl14_43
    | ~ spl14_63
    | ~ spl14_53
    | spl14_84
    | ~ spl14_66 ),
    inference(avatar_split_clause,[],[f2207,f501,f575,f448,f484,f417,f572])).

fof(f572,plain,
    ( spl14_83
  <=> ~ sP1(sK2,sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_83])])).

fof(f417,plain,
    ( spl14_43
  <=> ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_43])])).

fof(f484,plain,
    ( spl14_63
  <=> ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_63])])).

fof(f448,plain,
    ( spl14_53
  <=> ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_tsep_1(sK2,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_53])])).

fof(f501,plain,
    ( spl14_66
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_66])])).

fof(f2207,plain,
    ( sP0(sK3,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),sK4,sK2)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))
    | ~ sP1(sK2,sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),sK5,sK3)
    | ~ spl14_66 ),
    inference(resolution,[],[f502,f188])).

fof(f188,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
      | sP0(X4,X3,X2,X1,X0)
      | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(X2)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f502,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ spl14_66 ),
    inference(avatar_component_clause,[],[f501])).

fof(f3229,plain,
    ( spl14_354
    | ~ spl14_320
    | ~ spl14_452 ),
    inference(avatar_split_clause,[],[f3226,f2460,f1798,f1964])).

fof(f1798,plain,
    ( spl14_320
  <=> sP0(sK3,sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_320])])).

fof(f3226,plain,
    ( sP0(sK3,sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),sK5,sK2)
    | ~ spl14_320
    | ~ spl14_452 ),
    inference(forward_demodulation,[],[f1799,f2461])).

fof(f1799,plain,
    ( sP0(sK3,sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),sK5,sK2)
    | ~ spl14_320 ),
    inference(avatar_component_clause,[],[f1798])).

fof(f3209,plain,
    ( ~ spl14_42
    | spl14_355
    | ~ spl14_438
    | ~ spl14_448
    | ~ spl14_450
    | ~ spl14_454 ),
    inference(avatar_contradiction_clause,[],[f3206])).

fof(f3206,plain,
    ( $false
    | ~ spl14_42
    | ~ spl14_355
    | ~ spl14_438
    | ~ spl14_448
    | ~ spl14_450
    | ~ spl14_454 ),
    inference(unit_resulting_resolution,[],[f421,f2413,f1968,f2446,f2452,f2563,f188])).

fof(f1968,plain,
    ( ~ sP0(sK3,sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),sK5,sK2)
    | ~ spl14_355 ),
    inference(avatar_component_clause,[],[f1967])).

fof(f1967,plain,
    ( spl14_355
  <=> ~ sP0(sK3,sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_355])])).

fof(f3205,plain,
    ( spl14_454
    | ~ spl14_384
    | ~ spl14_452 ),
    inference(avatar_split_clause,[],[f3198,f2460,f2067,f2562])).

fof(f2067,plain,
    ( spl14_384
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),k1_tsep_1(sK2,sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_384])])).

fof(f3198,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_tsep_1(sK2,sK5,sK4),sK3)
    | ~ spl14_384
    | ~ spl14_452 ),
    inference(forward_demodulation,[],[f2068,f2461])).

fof(f2068,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),k1_tsep_1(sK2,sK5,sK4),sK3)
    | ~ spl14_384 ),
    inference(avatar_component_clause,[],[f2067])).

fof(f3190,plain,
    ( spl14_0
    | ~ spl14_5
    | spl14_12
    | ~ spl14_19
    | spl14_14
    | ~ spl14_21
    | ~ spl14_53
    | spl14_385 ),
    inference(avatar_split_clause,[],[f2166,f2070,f448,f327,f306,f320,f299,f271,f257])).

fof(f2070,plain,
    ( spl14_385
  <=> ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),k1_tsep_1(sK2,sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_385])])).

fof(f2166,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl14_385 ),
    inference(superposition,[],[f2071,f227])).

fof(f2071,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),k1_tsep_1(sK2,sK5,sK4),sK3)
    | ~ spl14_385 ),
    inference(avatar_component_clause,[],[f2070])).

fof(f3139,plain,
    ( ~ spl14_16
    | ~ spl14_26
    | ~ spl14_34
    | ~ spl14_56
    | ~ spl14_58
    | spl14_87
    | ~ spl14_128 ),
    inference(avatar_contradiction_clause,[],[f3137])).

fof(f3137,plain,
    ( $false
    | ~ spl14_16
    | ~ spl14_26
    | ~ spl14_34
    | ~ spl14_56
    | ~ spl14_58
    | ~ spl14_87
    | ~ spl14_128 ),
    inference(unit_resulting_resolution,[],[f463,f469,f317,f740,f356,f384,f584,f235])).

fof(f235,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t129_tmap_1.p',dt_k2_tmap_1)).

fof(f584,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl14_87 ),
    inference(avatar_component_clause,[],[f583])).

fof(f583,plain,
    ( spl14_87
  <=> ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_87])])).

fof(f384,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl14_34 ),
    inference(avatar_component_clause,[],[f383])).

fof(f383,plain,
    ( spl14_34
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_34])])).

fof(f356,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl14_26 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl14_26
  <=> v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_26])])).

fof(f740,plain,
    ( l1_struct_0(sK5)
    | ~ spl14_128 ),
    inference(avatar_component_clause,[],[f739])).

fof(f739,plain,
    ( spl14_128
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_128])])).

fof(f317,plain,
    ( v1_funct_1(sK6)
    | ~ spl14_16 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl14_16
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_16])])).

fof(f469,plain,
    ( l1_struct_0(sK3)
    | ~ spl14_58 ),
    inference(avatar_component_clause,[],[f468])).

fof(f468,plain,
    ( spl14_58
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_58])])).

fof(f463,plain,
    ( l1_struct_0(sK2)
    | ~ spl14_56 ),
    inference(avatar_component_clause,[],[f462])).

fof(f462,plain,
    ( spl14_56
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_56])])).

fof(f3136,plain,
    ( ~ spl14_16
    | ~ spl14_26
    | ~ spl14_34
    | ~ spl14_56
    | ~ spl14_58
    | spl14_105
    | ~ spl14_128 ),
    inference(avatar_contradiction_clause,[],[f3134])).

fof(f3134,plain,
    ( $false
    | ~ spl14_16
    | ~ spl14_26
    | ~ spl14_34
    | ~ spl14_56
    | ~ spl14_58
    | ~ spl14_105
    | ~ spl14_128 ),
    inference(unit_resulting_resolution,[],[f463,f469,f317,f740,f356,f384,f652,f236])).

fof(f236,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f652,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl14_105 ),
    inference(avatar_component_clause,[],[f651])).

fof(f651,plain,
    ( spl14_105
  <=> ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_105])])).

fof(f3117,plain,
    ( k2_tmap_1(sK2,sK3,sK6,sK4) != k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))
    | k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)) != k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) ),
    introduced(theory_axiom,[])).

fof(f3116,plain,
    ( k2_tmap_1(sK2,sK3,sK6,sK4) != k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))
    | k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)) != k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) ),
    introduced(theory_axiom,[])).

fof(f3115,plain,
    ( k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)) != k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))
    | k2_tmap_1(sK2,sK3,sK6,sK4) != k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,sK4),sK4,sK3)
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),sK4,sK3) ),
    introduced(theory_axiom,[])).

fof(f3112,plain,
    ( k2_tmap_1(sK2,sK3,sK6,sK4) != k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))
    | k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)) != k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),sK4,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,sK4),sK4,sK3) ),
    introduced(theory_axiom,[])).

fof(f3111,plain,
    ( ~ spl14_16
    | ~ spl14_26
    | ~ spl14_34
    | ~ spl14_56
    | ~ spl14_58
    | spl14_89
    | ~ spl14_124 ),
    inference(avatar_contradiction_clause,[],[f3109])).

fof(f3109,plain,
    ( $false
    | ~ spl14_16
    | ~ spl14_26
    | ~ spl14_34
    | ~ spl14_56
    | ~ spl14_58
    | ~ spl14_89
    | ~ spl14_124 ),
    inference(unit_resulting_resolution,[],[f463,f469,f317,f727,f356,f384,f591,f236])).

fof(f591,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ spl14_89 ),
    inference(avatar_component_clause,[],[f590])).

fof(f590,plain,
    ( spl14_89
  <=> ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_89])])).

fof(f727,plain,
    ( l1_struct_0(sK4)
    | ~ spl14_124 ),
    inference(avatar_component_clause,[],[f726])).

fof(f726,plain,
    ( spl14_124
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_124])])).

fof(f3108,plain,
    ( ~ spl14_16
    | ~ spl14_26
    | ~ spl14_34
    | ~ spl14_56
    | ~ spl14_58
    | spl14_81
    | ~ spl14_124 ),
    inference(avatar_contradiction_clause,[],[f3106])).

fof(f3106,plain,
    ( $false
    | ~ spl14_16
    | ~ spl14_26
    | ~ spl14_34
    | ~ spl14_56
    | ~ spl14_58
    | ~ spl14_81
    | ~ spl14_124 ),
    inference(unit_resulting_resolution,[],[f463,f469,f317,f727,f356,f384,f561,f235])).

fof(f561,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ spl14_81 ),
    inference(avatar_component_clause,[],[f560])).

fof(f560,plain,
    ( spl14_81
  <=> ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_81])])).

fof(f3105,plain,
    ( spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | spl14_7
    | ~ spl14_8
    | ~ spl14_10
    | ~ spl14_18
    | ~ spl14_42
    | ~ spl14_338
    | ~ spl14_448
    | ~ spl14_450
    | spl14_515 ),
    inference(avatar_contradiction_clause,[],[f3099])).

fof(f3099,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_10
    | ~ spl14_18
    | ~ spl14_42
    | ~ spl14_338
    | ~ spl14_448
    | ~ spl14_450
    | ~ spl14_515 ),
    inference(unit_resulting_resolution,[],[f261,f268,f275,f282,f289,f296,f324,f1850,f421,f2446,f2452,f3082,f244])).

fof(f3082,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))))
    | ~ spl14_515 ),
    inference(avatar_component_clause,[],[f3081])).

fof(f3081,plain,
    ( spl14_515
  <=> ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_515])])).

fof(f3097,plain,
    ( spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | spl14_7
    | ~ spl14_8
    | ~ spl14_10
    | ~ spl14_18
    | ~ spl14_42
    | ~ spl14_338
    | ~ spl14_448
    | ~ spl14_450
    | spl14_513 ),
    inference(avatar_contradiction_clause,[],[f3091])).

fof(f3091,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_10
    | ~ spl14_18
    | ~ spl14_42
    | ~ spl14_338
    | ~ spl14_448
    | ~ spl14_450
    | ~ spl14_513 ),
    inference(unit_resulting_resolution,[],[f261,f268,f275,f282,f289,f296,f324,f1850,f421,f2446,f2452,f3076,f245])).

fof(f3076,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ spl14_513 ),
    inference(avatar_component_clause,[],[f3075])).

fof(f3075,plain,
    ( spl14_513
  <=> ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))),u1_struct_0(sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_513])])).

fof(f3090,plain,
    ( spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | spl14_7
    | ~ spl14_8
    | ~ spl14_10
    | ~ spl14_18
    | ~ spl14_42
    | ~ spl14_338
    | ~ spl14_448
    | ~ spl14_450
    | spl14_511 ),
    inference(avatar_contradiction_clause,[],[f3084])).

fof(f3084,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_10
    | ~ spl14_18
    | ~ spl14_42
    | ~ spl14_338
    | ~ spl14_448
    | ~ spl14_450
    | ~ spl14_511 ),
    inference(unit_resulting_resolution,[],[f261,f268,f275,f282,f289,f296,f324,f1850,f421,f2446,f2452,f3070,f246])).

fof(f3070,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ spl14_511 ),
    inference(avatar_component_clause,[],[f3069])).

fof(f3069,plain,
    ( spl14_511
  <=> ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_511])])).

fof(f3083,plain,
    ( spl14_508
    | ~ spl14_511
    | ~ spl14_513
    | ~ spl14_515
    | ~ spl14_313
    | ~ spl14_19
    | spl14_12
    | ~ spl14_160
    | ~ spl14_486 ),
    inference(avatar_split_clause,[],[f2836,f2826,f844,f299,f320,f1774,f3081,f3075,f3069,f3063])).

fof(f3063,plain,
    ( spl14_508
  <=> k2_tmap_1(sK2,sK3,sK6,sK4) = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_508])])).

fof(f1774,plain,
    ( spl14_313
  <=> ~ m1_pre_topc(sK4,k1_tsep_1(sK2,sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_313])])).

fof(f844,plain,
    ( spl14_160
  <=> ! [X6] :
        ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X6,k2_tmap_1(sK2,sK3,sK6,sK4))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        | k2_tmap_1(sK2,sK3,sK6,sK4) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_160])])).

fof(f2836,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK4,k1_tsep_1(sK2,sK5,sK4))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | k2_tmap_1(sK2,sK3,sK6,sK4) = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))
    | ~ spl14_160
    | ~ spl14_486 ),
    inference(resolution,[],[f2827,f845])).

fof(f845,plain,
    ( ! [X6] :
        ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X6,k2_tmap_1(sK2,sK3,sK6,sK4))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        | k2_tmap_1(sK2,sK3,sK6,sK4) = X6 )
    | ~ spl14_160 ),
    inference(avatar_component_clause,[],[f844])).

fof(f2833,plain,
    ( spl14_1
    | ~ spl14_4
    | spl14_13
    | spl14_15
    | ~ spl14_18
    | ~ spl14_20
    | ~ spl14_334 ),
    inference(avatar_contradiction_clause,[],[f2829])).

fof(f2829,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_4
    | ~ spl14_13
    | ~ spl14_15
    | ~ spl14_18
    | ~ spl14_20
    | ~ spl14_334 ),
    inference(unit_resulting_resolution,[],[f261,f275,f310,f303,f331,f324,f1841,f228])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
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
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t129_tmap_1.p',dt_k1_tsep_1)).

fof(f1841,plain,
    ( v2_struct_0(k1_tsep_1(sK2,sK5,sK4))
    | ~ spl14_334 ),
    inference(avatar_component_clause,[],[f1840])).

fof(f1840,plain,
    ( spl14_334
  <=> v2_struct_0(k1_tsep_1(sK2,sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_334])])).

fof(f2828,plain,
    ( spl14_0
    | ~ spl14_3
    | ~ spl14_5
    | spl14_6
    | ~ spl14_9
    | ~ spl14_11
    | spl14_334
    | ~ spl14_339
    | ~ spl14_17
    | ~ spl14_27
    | ~ spl14_35
    | spl14_486
    | ~ spl14_452 ),
    inference(avatar_split_clause,[],[f2512,f2460,f2826,f380,f352,f313,f1852,f1840,f292,f285,f278,f271,f264,f257])).

fof(f264,plain,
    ( spl14_3
  <=> ~ v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f278,plain,
    ( spl14_6
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f285,plain,
    ( spl14_9
  <=> ~ v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).

fof(f292,plain,
    ( spl14_11
  <=> ~ l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).

fof(f1852,plain,
    ( spl14_339
  <=> ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_339])])).

fof(f313,plain,
    ( spl14_17
  <=> ~ v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).

fof(f352,plain,
    ( spl14_27
  <=> ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_27])])).

fof(f380,plain,
    ( spl14_35
  <=> ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_35])])).

fof(f2512,plain,
    ( ! [X1] :
        ( r2_funct_2(u1_struct_0(X1),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),X1,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))),k2_tmap_1(sK2,sK3,sK6,X1))
        | ~ m1_pre_topc(X1,k1_tsep_1(sK2,sK5,sK4))
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK4),sK2)
        | v2_struct_0(k1_tsep_1(sK2,sK5,sK4))
        | ~ m1_pre_topc(X1,sK2)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl14_452 ),
    inference(superposition,[],[f207,f2461])).

fof(f207,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t129_tmap_1.p',t78_tmap_1)).

fof(f2635,plain,
    ( spl14_1
    | ~ spl14_4
    | spl14_13
    | spl14_15
    | ~ spl14_18
    | ~ spl14_20
    | spl14_465 ),
    inference(avatar_contradiction_clause,[],[f2633])).

fof(f2633,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_4
    | ~ spl14_13
    | ~ spl14_15
    | ~ spl14_18
    | ~ spl14_20
    | ~ spl14_465 ),
    inference(unit_resulting_resolution,[],[f261,f275,f303,f310,f324,f331,f2628,f230])).

fof(f230,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f2628,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ spl14_465 ),
    inference(avatar_component_clause,[],[f2627])).

fof(f2602,plain,
    ( spl14_1
    | ~ spl14_4
    | spl14_13
    | spl14_15
    | ~ spl14_18
    | ~ spl14_20
    | ~ spl14_456 ),
    inference(avatar_contradiction_clause,[],[f2600])).

fof(f2600,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_4
    | ~ spl14_13
    | ~ spl14_15
    | ~ spl14_18
    | ~ spl14_20
    | ~ spl14_456 ),
    inference(unit_resulting_resolution,[],[f261,f275,f303,f310,f324,f331,f2595,f228])).

fof(f2595,plain,
    ( v2_struct_0(k1_tsep_1(sK2,sK4,sK5))
    | ~ spl14_456 ),
    inference(avatar_component_clause,[],[f2594])).

fof(f2472,plain,
    ( spl14_0
    | ~ spl14_5
    | spl14_12
    | ~ spl14_19
    | spl14_14
    | ~ spl14_21
    | ~ spl14_67
    | spl14_451 ),
    inference(avatar_split_clause,[],[f2470,f2454,f498,f327,f306,f320,f299,f271,f257])).

fof(f498,plain,
    ( spl14_67
  <=> ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_67])])).

fof(f2454,plain,
    ( spl14_451
  <=> ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_451])])).

fof(f2470,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl14_451 ),
    inference(superposition,[],[f2455,f227])).

fof(f2455,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))))
    | ~ spl14_451 ),
    inference(avatar_component_clause,[],[f2454])).

fof(f2466,plain,
    ( spl14_0
    | ~ spl14_5
    | spl14_12
    | ~ spl14_19
    | spl14_14
    | ~ spl14_21
    | ~ spl14_63
    | spl14_449 ),
    inference(avatar_split_clause,[],[f2464,f2448,f484,f327,f306,f320,f299,f271,f257])).

fof(f2448,plain,
    ( spl14_449
  <=> ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_449])])).

fof(f2464,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl14_449 ),
    inference(superposition,[],[f2449,f227])).

fof(f2449,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))
    | ~ spl14_449 ),
    inference(avatar_component_clause,[],[f2448])).

fof(f2462,plain,
    ( ~ spl14_43
    | ~ spl14_449
    | ~ spl14_451
    | spl14_452
    | ~ spl14_412
    | ~ spl14_444 ),
    inference(avatar_split_clause,[],[f2439,f2431,f2301,f2460,f2454,f2448,f417])).

fof(f2301,plain,
    ( spl14_412
  <=> r2_funct_2(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_412])])).

fof(f2431,plain,
    ( spl14_444
  <=> ! [X0] :
        ( ~ r2_funct_2(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),X0,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))
        | k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))))
        | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_444])])).

fof(f2439,plain,
    ( k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)) = k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))
    | ~ spl14_412
    | ~ spl14_444 ),
    inference(resolution,[],[f2432,f2302])).

fof(f2302,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))
    | ~ spl14_412 ),
    inference(avatar_component_clause,[],[f2301])).

fof(f2432,plain,
    ( ! [X0] :
        ( ~ r2_funct_2(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),X0,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))
        | k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))))
        | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))
        | ~ v1_funct_1(X0) )
    | ~ spl14_444 ),
    inference(avatar_component_clause,[],[f2431])).

fof(f2433,plain,
    ( spl14_0
    | ~ spl14_5
    | spl14_12
    | ~ spl14_19
    | spl14_14
    | ~ spl14_21
    | spl14_444
    | ~ spl14_442 ),
    inference(avatar_split_clause,[],[f2428,f2423,f2431,f327,f306,f320,f299,f271,f257])).

fof(f2423,plain,
    ( spl14_442
  <=> ! [X6] :
        ( ~ r2_funct_2(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3),X6,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))))
        | k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_442])])).

fof(f2428,plain,
    ( ! [X0] :
        ( ~ r2_funct_2(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),X0,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))))
        | k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)) = X0
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK2)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl14_442 ),
    inference(superposition,[],[f2424,f227])).

fof(f2424,plain,
    ( ! [X6] :
        ( ~ r2_funct_2(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3),X6,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))))
        | k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)) = X6 )
    | ~ spl14_442 ),
    inference(avatar_component_clause,[],[f2423])).

fof(f2425,plain,
    ( ~ spl14_329
    | ~ spl14_331
    | spl14_442
    | ~ spl14_332 ),
    inference(avatar_split_clause,[],[f2174,f1831,f2423,f1828,f1822])).

fof(f1822,plain,
    ( spl14_329
  <=> ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_329])])).

fof(f1828,plain,
    ( spl14_331
  <=> ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_331])])).

fof(f1831,plain,
    ( spl14_332
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_332])])).

fof(f2174,plain,
    ( ! [X6] :
        ( ~ r2_funct_2(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3),X6,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)))
        | k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)) = X6
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))))
        | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))
        | ~ v1_funct_1(X6) )
    | ~ spl14_332 ),
    inference(resolution,[],[f1832,f239])).

fof(f239,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f128])).

fof(f128,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f97])).

fof(f97,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t129_tmap_1.p',redefinition_r2_funct_2)).

fof(f1832,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))))
    | ~ spl14_332 ),
    inference(avatar_component_clause,[],[f1831])).

fof(f2414,plain,
    ( spl14_0
    | ~ spl14_5
    | spl14_12
    | ~ spl14_19
    | spl14_14
    | ~ spl14_21
    | spl14_438
    | ~ spl14_436 ),
    inference(avatar_split_clause,[],[f2406,f2399,f2412,f327,f306,f320,f299,f271,f257])).

fof(f2399,plain,
    ( spl14_436
  <=> sP1(sK2,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_436])])).

fof(f2406,plain,
    ( sP1(sK2,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),sK4,sK3)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl14_436 ),
    inference(superposition,[],[f2400,f227])).

fof(f2400,plain,
    ( sP1(sK2,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),sK4,sK3)
    | ~ spl14_436 ),
    inference(avatar_component_clause,[],[f2399])).

fof(f2404,plain,
    ( ~ spl14_4
    | ~ spl14_18
    | ~ spl14_20
    | ~ spl14_22
    | spl14_435 ),
    inference(avatar_contradiction_clause,[],[f2402])).

fof(f2402,plain,
    ( $false
    | ~ spl14_4
    | ~ spl14_18
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_435 ),
    inference(unit_resulting_resolution,[],[f275,f324,f331,f338,f2394,f231])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X2,X1)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( r4_tsep_1(X0,X2,X1)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( r4_tsep_1(X0,X2,X1)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & m1_pre_topc(X1,X0)
        & l1_pre_topc(X0) )
     => ( r4_tsep_1(X0,X1,X2)
       => r4_tsep_1(X0,X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t129_tmap_1.p',symmetry_r4_tsep_1)).

fof(f2394,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK4)
    | ~ spl14_435 ),
    inference(avatar_component_clause,[],[f2393])).

fof(f2393,plain,
    ( spl14_435
  <=> ~ r4_tsep_1(sK2,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_435])])).

fof(f338,plain,
    ( r4_tsep_1(sK2,sK4,sK5)
    | ~ spl14_22 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl14_22
  <=> r4_tsep_1(sK2,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_22])])).

fof(f2401,plain,
    ( spl14_0
    | ~ spl14_3
    | ~ spl14_5
    | spl14_6
    | ~ spl14_9
    | ~ spl14_11
    | spl14_14
    | ~ spl14_21
    | spl14_12
    | ~ spl14_19
    | ~ spl14_435
    | ~ spl14_329
    | ~ spl14_331
    | spl14_436
    | ~ spl14_332 ),
    inference(avatar_split_clause,[],[f2168,f1831,f2399,f1828,f1822,f2393,f320,f299,f327,f306,f292,f285,f278,f271,f264,f257])).

fof(f2168,plain,
    ( sP1(sK2,sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),sK4,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)))
    | ~ r4_tsep_1(sK2,sK5,sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl14_332 ),
    inference(resolution,[],[f1832,f202])).

fof(f202,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | sP1(X0,X2,X4,X3,X1)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X0,X2,X4,X3,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(definition_folding,[],[f60,f106,f105])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
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
                 => ( r4_tsep_1(X0,X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                        <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t129_tmap_1.p',t126_tmap_1)).

fof(f2303,plain,
    ( ~ spl14_43
    | ~ spl14_63
    | spl14_412
    | ~ spl14_66 ),
    inference(avatar_split_clause,[],[f2213,f501,f2301,f484,f417])).

fof(f2213,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))
    | ~ spl14_66 ),
    inference(resolution,[],[f502,f255])).

fof(f255,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f240])).

fof(f240,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f128])).

fof(f2258,plain,
    ( spl14_52
    | spl14_64 ),
    inference(avatar_split_clause,[],[f157,f494,f451])).

fof(f494,plain,
    ( spl14_64
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,sK4),sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_64])])).

fof(f157,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,sK4),sK4,sK3)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_tsep_1(sK2,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f115])).

fof(f2241,plain,
    ( spl14_55
    | ~ spl14_60
    | ~ spl14_128 ),
    inference(avatar_contradiction_clause,[],[f2236])).

fof(f2236,plain,
    ( $false
    | ~ spl14_55
    | ~ spl14_60
    | ~ spl14_128 ),
    inference(unit_resulting_resolution,[],[f740,f456,f475])).

fof(f475,plain,
    ( ! [X2] :
        ( v1_funct_1(k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ l1_struct_0(X2) )
    | ~ spl14_60 ),
    inference(avatar_component_clause,[],[f474])).

fof(f474,plain,
    ( spl14_60
  <=> ! [X2] :
        ( ~ l1_struct_0(X2)
        | v1_funct_1(k2_tmap_1(sK2,sK3,sK6,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_60])])).

fof(f456,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ spl14_55 ),
    inference(avatar_component_clause,[],[f455])).

fof(f455,plain,
    ( spl14_55
  <=> ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_55])])).

fof(f2233,plain,
    ( spl14_45
    | ~ spl14_60
    | ~ spl14_124 ),
    inference(avatar_contradiction_clause,[],[f2228])).

fof(f2228,plain,
    ( $false
    | ~ spl14_45
    | ~ spl14_60
    | ~ spl14_124 ),
    inference(unit_resulting_resolution,[],[f727,f424,f475])).

fof(f424,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ spl14_45 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl14_45
  <=> ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_45])])).

fof(f2226,plain,
    ( ~ spl14_16
    | ~ spl14_26
    | ~ spl14_34
    | ~ spl14_56
    | ~ spl14_58
    | spl14_63
    | ~ spl14_76 ),
    inference(avatar_contradiction_clause,[],[f2223])).

fof(f2223,plain,
    ( $false
    | ~ spl14_16
    | ~ spl14_26
    | ~ spl14_34
    | ~ spl14_56
    | ~ spl14_58
    | ~ spl14_63
    | ~ spl14_76 ),
    inference(unit_resulting_resolution,[],[f463,f469,f317,f545,f356,f384,f485,f235])).

fof(f485,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ spl14_63 ),
    inference(avatar_component_clause,[],[f484])).

fof(f545,plain,
    ( l1_struct_0(k1_tsep_1(sK2,sK4,sK5))
    | ~ spl14_76 ),
    inference(avatar_component_clause,[],[f544])).

fof(f544,plain,
    ( spl14_76
  <=> l1_struct_0(k1_tsep_1(sK2,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_76])])).

fof(f2222,plain,
    ( ~ spl14_43
    | ~ spl14_63
    | ~ spl14_53
    | ~ spl14_67
    | ~ spl14_45
    | ~ spl14_81
    | ~ spl14_65
    | ~ spl14_89
    | ~ spl14_55
    | ~ spl14_87
    | ~ spl14_69
    | ~ spl14_105 ),
    inference(avatar_split_clause,[],[f179,f651,f505,f583,f455,f590,f491,f560,f423,f498,f448,f484,f417])).

fof(f491,plain,
    ( spl14_65
  <=> ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,sK4),sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_65])])).

fof(f505,plain,
    ( spl14_69
  <=> ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,sK5),sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_69])])).

fof(f179,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,sK4),sK4,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5))) ),
    inference(cnf_transformation,[],[f115])).

fof(f2219,plain,
    ( spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | spl14_7
    | ~ spl14_8
    | ~ spl14_10
    | spl14_13
    | spl14_15
    | ~ spl14_18
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_42
    | ~ spl14_62
    | ~ spl14_66
    | spl14_83 ),
    inference(avatar_contradiction_clause,[],[f2205])).

fof(f2205,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_10
    | ~ spl14_13
    | ~ spl14_15
    | ~ spl14_18
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_42
    | ~ spl14_62
    | ~ spl14_66
    | ~ spl14_83 ),
    inference(unit_resulting_resolution,[],[f261,f268,f275,f282,f289,f296,f303,f310,f324,f331,f338,f421,f573,f488,f502,f202])).

fof(f488,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ spl14_62 ),
    inference(avatar_component_clause,[],[f487])).

fof(f487,plain,
    ( spl14_62
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_62])])).

fof(f573,plain,
    ( ~ sP1(sK2,sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),sK5,sK3)
    | ~ spl14_83 ),
    inference(avatar_component_clause,[],[f572])).

fof(f2204,plain,
    ( ~ spl14_16
    | ~ spl14_26
    | ~ spl14_34
    | ~ spl14_56
    | ~ spl14_58
    | spl14_67
    | ~ spl14_76 ),
    inference(avatar_contradiction_clause,[],[f2203])).

fof(f2203,plain,
    ( $false
    | ~ spl14_16
    | ~ spl14_26
    | ~ spl14_34
    | ~ spl14_56
    | ~ spl14_58
    | ~ spl14_67
    | ~ spl14_76 ),
    inference(unit_resulting_resolution,[],[f463,f469,f317,f356,f384,f499,f545,f236])).

fof(f499,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ spl14_67 ),
    inference(avatar_component_clause,[],[f498])).

fof(f2202,plain,
    ( spl14_0
    | ~ spl14_5
    | spl14_12
    | ~ spl14_19
    | spl14_14
    | ~ spl14_21
    | spl14_76
    | ~ spl14_386 ),
    inference(avatar_split_clause,[],[f2136,f2078,f544,f327,f306,f320,f299,f271,f257])).

fof(f2078,plain,
    ( spl14_386
  <=> l1_struct_0(k1_tsep_1(sK2,sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_386])])).

fof(f2136,plain,
    ( l1_struct_0(k1_tsep_1(sK2,sK4,sK5))
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl14_386 ),
    inference(superposition,[],[f2079,f227])).

fof(f2079,plain,
    ( l1_struct_0(k1_tsep_1(sK2,sK5,sK4))
    | ~ spl14_386 ),
    inference(avatar_component_clause,[],[f2078])).

fof(f2164,plain,
    ( ~ spl14_16
    | ~ spl14_26
    | ~ spl14_34
    | ~ spl14_56
    | ~ spl14_58
    | spl14_333
    | ~ spl14_386 ),
    inference(avatar_contradiction_clause,[],[f2159])).

fof(f2159,plain,
    ( $false
    | ~ spl14_16
    | ~ spl14_26
    | ~ spl14_34
    | ~ spl14_56
    | ~ spl14_58
    | ~ spl14_333
    | ~ spl14_386 ),
    inference(unit_resulting_resolution,[],[f463,f469,f317,f2079,f356,f384,f1835,f236])).

fof(f1835,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))))
    | ~ spl14_333 ),
    inference(avatar_component_clause,[],[f1834])).

fof(f1834,plain,
    ( spl14_333
  <=> ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_333])])).

fof(f2156,plain,
    ( ~ spl14_16
    | ~ spl14_26
    | ~ spl14_34
    | ~ spl14_56
    | ~ spl14_58
    | spl14_331
    | ~ spl14_386 ),
    inference(avatar_contradiction_clause,[],[f2151])).

fof(f2151,plain,
    ( $false
    | ~ spl14_16
    | ~ spl14_26
    | ~ spl14_34
    | ~ spl14_56
    | ~ spl14_58
    | ~ spl14_331
    | ~ spl14_386 ),
    inference(unit_resulting_resolution,[],[f463,f469,f317,f2079,f356,f384,f1829,f235])).

fof(f1829,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))
    | ~ spl14_331 ),
    inference(avatar_component_clause,[],[f1828])).

fof(f2135,plain,
    ( ~ spl14_4
    | ~ spl14_338
    | spl14_389 ),
    inference(avatar_contradiction_clause,[],[f2130])).

fof(f2130,plain,
    ( $false
    | ~ spl14_4
    | ~ spl14_338
    | ~ spl14_389 ),
    inference(unit_resulting_resolution,[],[f275,f2092,f1850,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t129_tmap_1.p',dt_m1_pre_topc)).

fof(f2092,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK2,sK5,sK4))
    | ~ spl14_389 ),
    inference(avatar_component_clause,[],[f2091])).

fof(f2091,plain,
    ( spl14_389
  <=> ~ l1_pre_topc(k1_tsep_1(sK2,sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_389])])).

fof(f2129,plain,
    ( spl14_1
    | ~ spl14_4
    | spl14_13
    | spl14_15
    | ~ spl14_18
    | ~ spl14_20
    | spl14_339 ),
    inference(avatar_contradiction_clause,[],[f2125])).

fof(f2125,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_4
    | ~ spl14_13
    | ~ spl14_15
    | ~ spl14_18
    | ~ spl14_20
    | ~ spl14_339 ),
    inference(unit_resulting_resolution,[],[f261,f275,f310,f303,f331,f324,f1853,f230])).

fof(f1853,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK4),sK2)
    | ~ spl14_339 ),
    inference(avatar_component_clause,[],[f1852])).

fof(f2124,plain,
    ( ~ spl14_339
    | ~ spl14_144
    | spl14_329 ),
    inference(avatar_split_clause,[],[f2073,f1822,f794,f1852])).

fof(f794,plain,
    ( spl14_144
  <=> ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK2,sK3,sK6,X0))
        | ~ m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_144])])).

fof(f2073,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK4),sK2)
    | ~ spl14_144
    | ~ spl14_329 ),
    inference(resolution,[],[f1823,f795])).

fof(f795,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK2,sK3,sK6,X0))
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl14_144 ),
    inference(avatar_component_clause,[],[f794])).

fof(f1823,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)))
    | ~ spl14_329 ),
    inference(avatar_component_clause,[],[f1822])).

fof(f2093,plain,
    ( ~ spl14_389
    | spl14_387 ),
    inference(avatar_split_clause,[],[f2084,f2081,f2091])).

fof(f2081,plain,
    ( spl14_387
  <=> ~ l1_struct_0(k1_tsep_1(sK2,sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_387])])).

fof(f2084,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK2,sK5,sK4))
    | ~ spl14_387 ),
    inference(resolution,[],[f2082,f183])).

fof(f183,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t129_tmap_1.p',dt_l1_pre_topc)).

fof(f2082,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK2,sK5,sK4))
    | ~ spl14_387 ),
    inference(avatar_component_clause,[],[f2081])).

fof(f1969,plain,
    ( spl14_0
    | ~ spl14_5
    | spl14_12
    | ~ spl14_19
    | spl14_14
    | ~ spl14_21
    | ~ spl14_355
    | spl14_321 ),
    inference(avatar_split_clause,[],[f1954,f1795,f1967,f327,f306,f320,f299,f271,f257])).

fof(f1795,plain,
    ( spl14_321
  <=> ~ sP0(sK3,sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_321])])).

fof(f1954,plain,
    ( ~ sP0(sK3,sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)),sK5,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl14_321 ),
    inference(superposition,[],[f1796,f227])).

fof(f1796,plain,
    ( ~ sP0(sK3,sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),sK5,sK2)
    | ~ spl14_321 ),
    inference(avatar_component_clause,[],[f1795])).

fof(f1953,plain,
    ( ~ spl14_321
    | spl14_315 ),
    inference(avatar_split_clause,[],[f1946,f1780,f1795])).

fof(f1780,plain,
    ( spl14_315
  <=> ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_315])])).

fof(f1946,plain,
    ( ~ sP0(sK3,sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),sK5,sK2)
    | ~ spl14_315 ),
    inference(resolution,[],[f1781,f199])).

fof(f1781,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),sK4,sK3)
    | ~ spl14_315 ),
    inference(avatar_component_clause,[],[f1780])).

fof(f1939,plain,
    ( spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | spl14_13
    | spl14_15
    | ~ spl14_18
    | ~ spl14_20
    | spl14_351 ),
    inference(avatar_contradiction_clause,[],[f1937])).

fof(f1937,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_13
    | ~ spl14_15
    | ~ spl14_18
    | ~ spl14_20
    | ~ spl14_351 ),
    inference(unit_resulting_resolution,[],[f261,f268,f275,f303,f310,f324,f331,f1935,f209])).

fof(f1935,plain,
    ( ~ m1_pre_topc(sK4,k1_tsep_1(sK2,sK4,sK5))
    | ~ spl14_351 ),
    inference(avatar_component_clause,[],[f1934])).

fof(f1934,plain,
    ( spl14_351
  <=> ~ m1_pre_topc(sK4,k1_tsep_1(sK2,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_351])])).

fof(f1936,plain,
    ( spl14_0
    | ~ spl14_5
    | spl14_12
    | ~ spl14_19
    | spl14_14
    | ~ spl14_21
    | ~ spl14_351
    | spl14_313 ),
    inference(avatar_split_clause,[],[f1855,f1774,f1934,f327,f306,f320,f299,f271,f257])).

fof(f1855,plain,
    ( ~ m1_pre_topc(sK4,k1_tsep_1(sK2,sK4,sK5))
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl14_313 ),
    inference(superposition,[],[f1775,f227])).

fof(f1775,plain,
    ( ~ m1_pre_topc(sK4,k1_tsep_1(sK2,sK5,sK4))
    | ~ spl14_313 ),
    inference(avatar_component_clause,[],[f1774])).

fof(f1854,plain,
    ( ~ spl14_313
    | ~ spl14_315
    | ~ spl14_317
    | ~ spl14_319
    | spl14_320
    | ~ spl14_323
    | ~ spl14_325
    | ~ spl14_327
    | ~ spl14_329
    | ~ spl14_331
    | ~ spl14_333
    | spl14_334
    | ~ spl14_337
    | ~ spl14_339
    | ~ spl14_89
    | ~ spl14_212
    | ~ spl14_246 ),
    inference(avatar_split_clause,[],[f1464,f1444,f1168,f590,f1852,f1846,f1840,f1834,f1828,f1822,f1816,f1810,f1804,f1798,f1792,f1786,f1780,f1774])).

fof(f1786,plain,
    ( spl14_317
  <=> ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),u1_struct_0(sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_317])])).

fof(f1792,plain,
    ( spl14_319
  <=> ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_319])])).

fof(f1804,plain,
    ( spl14_323
  <=> ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_323])])).

fof(f1168,plain,
    ( spl14_212
  <=> ! [X2] :
        ( v2_struct_0(X2)
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,X2),u1_struct_0(X2),u1_struct_0(sK3))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,X2,sK4,k2_tmap_1(sK2,sK3,sK6,X2)),u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,X2,sK4,k2_tmap_1(sK2,sK3,sK6,X2)))
        | k2_tmap_1(sK2,sK3,sK6,sK4) = k3_tmap_1(sK2,sK3,X2,sK4,k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ m1_pre_topc(sK4,X2)
        | ~ m1_pre_topc(X2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_212])])).

fof(f1444,plain,
    ( spl14_246
  <=> ! [X8] :
        ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK3))))
        | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,X8),sK2)
        | ~ m1_pre_topc(sK5,k1_tsep_1(sK2,sK5,X8))
        | v2_struct_0(k1_tsep_1(sK2,sK5,X8))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,X8)),u1_struct_0(sK3))))
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8)),u1_struct_0(k1_tsep_1(sK2,sK5,X8)),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8)))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),sK5,sK3)
        | sP0(sK3,X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8)),sK5,sK2)
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),u1_struct_0(X8),u1_struct_0(sK3))
        | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),X8,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_246])])).

fof(f1464,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK4),sK2)
    | ~ m1_pre_topc(sK5,k1_tsep_1(sK2,sK5,sK4))
    | v2_struct_0(k1_tsep_1(sK2,sK5,sK4))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),sK5,sK3)
    | sP0(sK3,sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),sK5,sK2)
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),sK4,sK3)
    | ~ m1_pre_topc(sK4,k1_tsep_1(sK2,sK5,sK4))
    | ~ spl14_212
    | ~ spl14_246 ),
    inference(duplicate_literal_removal,[],[f1461])).

fof(f1461,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK4),sK2)
    | ~ m1_pre_topc(sK5,k1_tsep_1(sK2,sK5,sK4))
    | v2_struct_0(k1_tsep_1(sK2,sK5,sK4))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),sK5,sK3)
    | sP0(sK3,sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),sK5,sK2)
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),sK4,sK3)
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK4)),u1_struct_0(sK3))))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,sK4),sK4,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,sK4))))
    | v2_struct_0(k1_tsep_1(sK2,sK5,sK4))
    | ~ m1_pre_topc(sK4,k1_tsep_1(sK2,sK5,sK4))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,sK4),sK2)
    | ~ spl14_212
    | ~ spl14_246 ),
    inference(superposition,[],[f1445,f1169])).

fof(f1169,plain,
    ( ! [X2] :
        ( k2_tmap_1(sK2,sK3,sK6,sK4) = k3_tmap_1(sK2,sK3,X2,sK4,k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,X2),u1_struct_0(X2),u1_struct_0(sK3))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,X2,sK4,k2_tmap_1(sK2,sK3,sK6,X2)),u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,X2,sK4,k2_tmap_1(sK2,sK3,sK6,X2)))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK4,X2)
        | ~ m1_pre_topc(X2,sK2) )
    | ~ spl14_212 ),
    inference(avatar_component_clause,[],[f1168])).

fof(f1445,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK3))))
        | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,X8),sK2)
        | ~ m1_pre_topc(sK5,k1_tsep_1(sK2,sK5,X8))
        | v2_struct_0(k1_tsep_1(sK2,sK5,X8))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,X8)),u1_struct_0(sK3))))
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8)),u1_struct_0(k1_tsep_1(sK2,sK5,X8)),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8)))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),sK5,sK3)
        | sP0(sK3,X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8)),sK5,sK2)
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),u1_struct_0(X8),u1_struct_0(sK3))
        | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),X8,sK3) )
    | ~ spl14_246 ),
    inference(avatar_component_clause,[],[f1444])).

fof(f1446,plain,
    ( spl14_246
    | ~ spl14_105
    | ~ spl14_214 ),
    inference(avatar_split_clause,[],[f1226,f1200,f651,f1444])).

fof(f1200,plain,
    ( spl14_214
  <=> ! [X2] :
        ( v2_struct_0(X2)
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,X2),u1_struct_0(X2),u1_struct_0(sK3))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,X2,sK5,k2_tmap_1(sK2,sK3,sK6,X2)),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,X2,sK5,k2_tmap_1(sK2,sK3,sK6,X2)))
        | k2_tmap_1(sK2,sK3,sK6,sK5) = k3_tmap_1(sK2,sK3,X2,sK5,k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ m1_pre_topc(sK5,X2)
        | ~ m1_pre_topc(X2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_214])])).

fof(f1226,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),X8,sK3)
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),u1_struct_0(X8),u1_struct_0(sK3))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))))
        | sP0(sK3,X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8)),sK5,sK2)
        | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),sK5,sK3)
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8)))
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8)),u1_struct_0(k1_tsep_1(sK2,sK5,X8)),u1_struct_0(sK3))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,X8)),u1_struct_0(sK3))))
        | v2_struct_0(k1_tsep_1(sK2,sK5,X8))
        | ~ m1_pre_topc(sK5,k1_tsep_1(sK2,sK5,X8))
        | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,X8),sK2) )
    | ~ spl14_214 ),
    inference(duplicate_literal_removal,[],[f1211])).

fof(f1211,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),X8,sK3)
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),u1_struct_0(X8),u1_struct_0(sK3))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))))
        | sP0(sK3,X8,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8)),sK5,sK2)
        | ~ v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),sK5,sK3)
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8)))
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8)),u1_struct_0(k1_tsep_1(sK2,sK5,X8)),u1_struct_0(sK3))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,X8)),u1_struct_0(sK3))))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK5,X8),sK5,k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK5,X8))))
        | v2_struct_0(k1_tsep_1(sK2,sK5,X8))
        | ~ m1_pre_topc(sK5,k1_tsep_1(sK2,sK5,X8))
        | ~ m1_pre_topc(k1_tsep_1(sK2,sK5,X8),sK2) )
    | ~ spl14_214 ),
    inference(superposition,[],[f201,f1201])).

fof(f1201,plain,
    ( ! [X2] :
        ( k2_tmap_1(sK2,sK3,sK6,sK5) = k3_tmap_1(sK2,sK3,X2,sK5,k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,X2),u1_struct_0(X2),u1_struct_0(sK3))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,X2,sK5,k2_tmap_1(sK2,sK3,sK6,X2)),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,X2,sK5,k2_tmap_1(sK2,sK3,sK6,X2)))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK5,X2)
        | ~ m1_pre_topc(X2,sK2) )
    | ~ spl14_214 ),
    inference(avatar_component_clause,[],[f1200])).

fof(f201,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
      | sP0(X0,X1,X2,X3,X4)
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ) ),
    inference(cnf_transformation,[],[f123])).

fof(f1202,plain,
    ( spl14_0
    | ~ spl14_3
    | ~ spl14_5
    | spl14_6
    | ~ spl14_9
    | ~ spl14_11
    | ~ spl14_21
    | spl14_214
    | ~ spl14_208 ),
    inference(avatar_split_clause,[],[f1026,f1014,f1200,f327,f292,f285,f278,f271,f264,f257])).

fof(f1026,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK2)
        | ~ m1_pre_topc(sK5,X2)
        | k2_tmap_1(sK2,sK3,sK6,sK5) = k3_tmap_1(sK2,sK3,X2,sK5,k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,X2,sK5,k2_tmap_1(sK2,sK3,sK6,X2)))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,X2,sK5,k2_tmap_1(sK2,sK3,sK6,X2)),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,X2),u1_struct_0(X2),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ m1_pre_topc(sK5,sK2)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl14_208 ),
    inference(duplicate_literal_removal,[],[f1023])).

fof(f1023,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK2)
        | ~ m1_pre_topc(sK5,X2)
        | k2_tmap_1(sK2,sK3,sK6,sK5) = k3_tmap_1(sK2,sK3,X2,sK5,k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,X2,sK5,k2_tmap_1(sK2,sK3,sK6,X2)))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,X2,sK5,k2_tmap_1(sK2,sK3,sK6,X2)),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,X2),u1_struct_0(X2),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ m1_pre_topc(sK5,sK2)
        | ~ m1_pre_topc(X2,sK2)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl14_208 ),
    inference(resolution,[],[f1015,f246])).

fof(f1170,plain,
    ( spl14_0
    | ~ spl14_3
    | ~ spl14_5
    | spl14_6
    | ~ spl14_9
    | ~ spl14_11
    | ~ spl14_19
    | spl14_212
    | ~ spl14_202 ),
    inference(avatar_split_clause,[],[f1004,f988,f1168,f320,f292,f285,f278,f271,f264,f257])).

fof(f988,plain,
    ( spl14_202
  <=> ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,X0,sK4,k2_tmap_1(sK2,sK3,sK6,X0)))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(sK4,X0)
        | k2_tmap_1(sK2,sK3,sK6,sK4) = k3_tmap_1(sK2,sK3,X0,sK4,k2_tmap_1(sK2,sK3,sK6,X0))
        | ~ m1_subset_1(k3_tmap_1(sK2,sK3,X0,sK4,k2_tmap_1(sK2,sK3,sK6,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,X0,sK4,k2_tmap_1(sK2,sK3,sK6,X0)),u1_struct_0(sK4),u1_struct_0(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_202])])).

fof(f1004,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK2)
        | ~ m1_pre_topc(sK4,X2)
        | k2_tmap_1(sK2,sK3,sK6,sK4) = k3_tmap_1(sK2,sK3,X2,sK4,k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,X2,sK4,k2_tmap_1(sK2,sK3,sK6,X2)))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,X2,sK4,k2_tmap_1(sK2,sK3,sK6,X2)),u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,X2),u1_struct_0(X2),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ m1_pre_topc(sK4,sK2)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl14_202 ),
    inference(duplicate_literal_removal,[],[f1001])).

fof(f1001,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK2)
        | ~ m1_pre_topc(sK4,X2)
        | k2_tmap_1(sK2,sK3,sK6,sK4) = k3_tmap_1(sK2,sK3,X2,sK4,k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,X2,sK4,k2_tmap_1(sK2,sK3,sK6,X2)))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,X2,sK4,k2_tmap_1(sK2,sK3,sK6,X2)),u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,X2),u1_struct_0(X2),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ m1_pre_topc(sK4,sK2)
        | ~ m1_pre_topc(X2,sK2)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl14_202 ),
    inference(resolution,[],[f989,f246])).

fof(f989,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_tmap_1(sK2,sK3,X0,sK4,k2_tmap_1(sK2,sK3,sK6,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(sK4,X0)
        | k2_tmap_1(sK2,sK3,sK6,sK4) = k3_tmap_1(sK2,sK3,X0,sK4,k2_tmap_1(sK2,sK3,sK6,X0))
        | ~ v1_funct_1(k3_tmap_1(sK2,sK3,X0,sK4,k2_tmap_1(sK2,sK3,sK6,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,X0,sK4,k2_tmap_1(sK2,sK3,sK6,X0)),u1_struct_0(sK4),u1_struct_0(sK3)) )
    | ~ spl14_202 ),
    inference(avatar_component_clause,[],[f988])).

fof(f1016,plain,
    ( spl14_0
    | ~ spl14_3
    | ~ spl14_5
    | spl14_6
    | ~ spl14_9
    | ~ spl14_11
    | spl14_14
    | ~ spl14_21
    | ~ spl14_17
    | ~ spl14_27
    | ~ spl14_35
    | spl14_208
    | ~ spl14_162 ),
    inference(avatar_split_clause,[],[f853,f850,f1014,f380,f352,f313,f327,f306,f292,f285,f278,f271,f264,f257])).

fof(f853,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,X0,sK5,k2_tmap_1(sK2,sK3,sK6,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,X0,sK5,k2_tmap_1(sK2,sK3,sK6,X0)),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ m1_subset_1(k3_tmap_1(sK2,sK3,X0,sK5,k2_tmap_1(sK2,sK3,sK6,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | k2_tmap_1(sK2,sK3,sK6,sK5) = k3_tmap_1(sK2,sK3,X0,sK5,k2_tmap_1(sK2,sK3,sK6,X0))
        | ~ m1_pre_topc(sK5,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK5,sK2)
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl14_162 ),
    inference(resolution,[],[f851,f207])).

fof(f990,plain,
    ( spl14_0
    | ~ spl14_3
    | ~ spl14_5
    | spl14_6
    | ~ spl14_9
    | ~ spl14_11
    | spl14_12
    | ~ spl14_19
    | ~ spl14_17
    | ~ spl14_27
    | ~ spl14_35
    | spl14_202
    | ~ spl14_160 ),
    inference(avatar_split_clause,[],[f847,f844,f988,f380,f352,f313,f320,f299,f292,f285,f278,f271,f264,f257])).

fof(f847,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,X0,sK4,k2_tmap_1(sK2,sK3,sK6,X0)))
        | ~ v1_funct_2(k3_tmap_1(sK2,sK3,X0,sK4,k2_tmap_1(sK2,sK3,sK6,X0)),u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ m1_subset_1(k3_tmap_1(sK2,sK3,X0,sK4,k2_tmap_1(sK2,sK3,sK6,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        | k2_tmap_1(sK2,sK3,sK6,sK4) = k3_tmap_1(sK2,sK3,X0,sK4,k2_tmap_1(sK2,sK3,sK6,X0))
        | ~ m1_pre_topc(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK4,sK2)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl14_160 ),
    inference(resolution,[],[f845,f207])).

fof(f852,plain,
    ( ~ spl14_55
    | ~ spl14_87
    | spl14_162
    | ~ spl14_104 ),
    inference(avatar_split_clause,[],[f661,f654,f850,f583,f455])).

fof(f654,plain,
    ( spl14_104
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_104])])).

fof(f661,plain,
    ( ! [X6] :
        ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X6,k2_tmap_1(sK2,sK3,sK6,sK5))
        | k2_tmap_1(sK2,sK3,sK6,sK5) = X6
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(X6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(X6) )
    | ~ spl14_104 ),
    inference(resolution,[],[f655,f239])).

fof(f655,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl14_104 ),
    inference(avatar_component_clause,[],[f654])).

fof(f846,plain,
    ( ~ spl14_45
    | ~ spl14_81
    | spl14_160
    | ~ spl14_88 ),
    inference(avatar_split_clause,[],[f600,f593,f844,f560,f423])).

fof(f593,plain,
    ( spl14_88
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_88])])).

fof(f600,plain,
    ( ! [X6] :
        ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X6,k2_tmap_1(sK2,sK3,sK6,sK4))
        | k2_tmap_1(sK2,sK3,sK6,sK4) = X6
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        | ~ v1_funct_2(X6,u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ v1_funct_1(X6) )
    | ~ spl14_88 ),
    inference(resolution,[],[f594,f239])).

fof(f594,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ spl14_88 ),
    inference(avatar_component_clause,[],[f593])).

fof(f796,plain,
    ( spl14_0
    | ~ spl14_3
    | ~ spl14_5
    | spl14_6
    | ~ spl14_9
    | ~ spl14_11
    | ~ spl14_17
    | ~ spl14_27
    | ~ spl14_35
    | spl14_144
    | ~ spl14_40 ),
    inference(avatar_split_clause,[],[f414,f411,f794,f380,f352,f313,f292,f285,f278,f271,f264,f257])).

fof(f411,plain,
    ( spl14_40
  <=> ! [X5] : v1_funct_1(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_40])])).

fof(f414,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK2,sK3,sK6,X0))
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl14_40 ),
    inference(superposition,[],[f412,f208])).

fof(f208,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
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
    inference(flattening,[],[f65])).

fof(f65,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t129_tmap_1.p',d4_tmap_1)).

fof(f412,plain,
    ( ! [X5] : v1_funct_1(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,X5))
    | ~ spl14_40 ),
    inference(avatar_component_clause,[],[f411])).

fof(f750,plain,
    ( ~ spl14_28
    | spl14_129 ),
    inference(avatar_contradiction_clause,[],[f748])).

fof(f748,plain,
    ( $false
    | ~ spl14_28
    | ~ spl14_129 ),
    inference(unit_resulting_resolution,[],[f363,f743,f183])).

fof(f743,plain,
    ( ~ l1_struct_0(sK5)
    | ~ spl14_129 ),
    inference(avatar_component_clause,[],[f742])).

fof(f742,plain,
    ( spl14_129
  <=> ~ l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_129])])).

fof(f363,plain,
    ( l1_pre_topc(sK5)
    | ~ spl14_28 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl14_28
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_28])])).

fof(f737,plain,
    ( ~ spl14_24
    | spl14_125 ),
    inference(avatar_contradiction_clause,[],[f735])).

fof(f735,plain,
    ( $false
    | ~ spl14_24
    | ~ spl14_125 ),
    inference(unit_resulting_resolution,[],[f349,f730,f183])).

fof(f730,plain,
    ( ~ l1_struct_0(sK4)
    | ~ spl14_125 ),
    inference(avatar_component_clause,[],[f729])).

fof(f729,plain,
    ( spl14_125
  <=> ~ l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_125])])).

fof(f349,plain,
    ( l1_pre_topc(sK4)
    | ~ spl14_24 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl14_24
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_24])])).

fof(f549,plain,
    ( ~ spl14_77
    | spl14_43
    | ~ spl14_60 ),
    inference(avatar_split_clause,[],[f542,f474,f417,f547])).

fof(f547,plain,
    ( spl14_77
  <=> ~ l1_struct_0(k1_tsep_1(sK2,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_77])])).

fof(f542,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK2,sK4,sK5))
    | ~ spl14_43
    | ~ spl14_60 ),
    inference(resolution,[],[f418,f475])).

fof(f418,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,k1_tsep_1(sK2,sK4,sK5)))
    | ~ spl14_43 ),
    inference(avatar_component_clause,[],[f417])).

fof(f482,plain,
    ( ~ spl14_10
    | spl14_59 ),
    inference(avatar_contradiction_clause,[],[f480])).

fof(f480,plain,
    ( $false
    | ~ spl14_10
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f296,f472,f183])).

fof(f472,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl14_59 ),
    inference(avatar_component_clause,[],[f471])).

fof(f471,plain,
    ( spl14_59
  <=> ~ l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_59])])).

fof(f479,plain,
    ( ~ spl14_4
    | spl14_57 ),
    inference(avatar_contradiction_clause,[],[f477])).

fof(f477,plain,
    ( $false
    | ~ spl14_4
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f275,f466,f183])).

fof(f466,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl14_57 ),
    inference(avatar_component_clause,[],[f465])).

fof(f465,plain,
    ( spl14_57
  <=> ~ l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_57])])).

fof(f476,plain,
    ( ~ spl14_57
    | ~ spl14_59
    | ~ spl14_17
    | ~ spl14_27
    | spl14_60
    | ~ spl14_34 ),
    inference(avatar_split_clause,[],[f387,f383,f474,f352,f313,f471,f465])).

fof(f387,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(X2)
        | v1_funct_1(k2_tmap_1(sK2,sK3,sK6,X2))
        | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | ~ l1_struct_0(sK3)
        | ~ l1_struct_0(sK2) )
    | ~ spl14_34 ),
    inference(resolution,[],[f384,f234])).

fof(f234,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f413,plain,
    ( ~ spl14_17
    | spl14_40
    | ~ spl14_34 ),
    inference(avatar_split_clause,[],[f389,f383,f411,f313])).

fof(f389,plain,
    ( ! [X5] :
        ( v1_funct_1(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,X5))
        | ~ v1_funct_1(sK6) )
    | ~ spl14_34 ),
    inference(resolution,[],[f384,f242])).

fof(f242,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f101])).

fof(f101,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t129_tmap_1.p',dt_k2_partfun1)).

fof(f385,plain,(
    spl14_34 ),
    inference(avatar_split_clause,[],[f146,f383])).

fof(f146,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f115])).

fof(f364,plain,
    ( ~ spl14_5
    | spl14_28
    | ~ spl14_20 ),
    inference(avatar_split_clause,[],[f343,f330,f362,f271])).

fof(f343,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ spl14_20 ),
    inference(resolution,[],[f331,f186])).

fof(f357,plain,(
    spl14_26 ),
    inference(avatar_split_clause,[],[f145,f355])).

fof(f145,plain,(
    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f115])).

fof(f350,plain,
    ( ~ spl14_5
    | spl14_24
    | ~ spl14_18 ),
    inference(avatar_split_clause,[],[f341,f323,f348,f271])).

fof(f341,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ spl14_18 ),
    inference(resolution,[],[f324,f186])).

fof(f339,plain,(
    spl14_22 ),
    inference(avatar_split_clause,[],[f143,f337])).

fof(f143,plain,(
    r4_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f115])).

fof(f332,plain,(
    spl14_20 ),
    inference(avatar_split_clause,[],[f142,f330])).

fof(f142,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f115])).

fof(f325,plain,(
    spl14_18 ),
    inference(avatar_split_clause,[],[f140,f323])).

fof(f140,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f115])).

fof(f318,plain,(
    spl14_16 ),
    inference(avatar_split_clause,[],[f144,f316])).

fof(f144,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f115])).

fof(f311,plain,(
    ~ spl14_15 ),
    inference(avatar_split_clause,[],[f141,f309])).

fof(f141,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f115])).

fof(f304,plain,(
    ~ spl14_13 ),
    inference(avatar_split_clause,[],[f139,f302])).

fof(f139,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f115])).

fof(f297,plain,(
    spl14_10 ),
    inference(avatar_split_clause,[],[f138,f295])).

fof(f138,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f115])).

fof(f290,plain,(
    spl14_8 ),
    inference(avatar_split_clause,[],[f137,f288])).

fof(f137,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f115])).

fof(f283,plain,(
    ~ spl14_7 ),
    inference(avatar_split_clause,[],[f136,f281])).

fof(f136,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f115])).

fof(f276,plain,(
    spl14_4 ),
    inference(avatar_split_clause,[],[f135,f274])).

fof(f135,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f115])).

fof(f269,plain,(
    spl14_2 ),
    inference(avatar_split_clause,[],[f134,f267])).

fof(f134,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f115])).

fof(f262,plain,(
    ~ spl14_1 ),
    inference(avatar_split_clause,[],[f133,f260])).

fof(f133,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f115])).
%------------------------------------------------------------------------------
