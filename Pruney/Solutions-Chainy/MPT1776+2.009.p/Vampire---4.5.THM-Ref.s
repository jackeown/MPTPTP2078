%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 484 expanded)
%              Number of leaves         :   37 ( 188 expanded)
%              Depth                    :   22
%              Number of atoms          : 1507 (3689 expanded)
%              Number of equality atoms :   46 ( 137 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f332,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f70,f74,f78,f82,f86,f90,f94,f98,f106,f110,f114,f118,f174,f178,f186,f190,f198,f202,f231,f237,f241,f254,f283,f296,f312,f313,f330,f331])).

fof(f331,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k2_tmap_1(sK3,sK0,sK4,sK2)
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f330,plain,
    ( ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22
    | spl7_24
    | ~ spl7_28
    | ~ spl7_29 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22
    | spl7_24
    | ~ spl7_28
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f227,f327])).

fof(f327,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_28
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f326,f89])).

fof(f89,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl7_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f326,plain,
    ( v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_28
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f325,f185])).

fof(f185,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl7_18
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f325,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_28
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f324,f177])).

fof(f177,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl7_16
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f324,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_28
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f323,f109])).

fof(f109,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_12
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f323,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_28
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f322,f253])).

fof(f253,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl7_28
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f322,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f321,f73])).

fof(f73,plain,
    ( ~ v2_struct_0(sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl7_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f321,plain,
    ( v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f320,f201])).

fof(f201,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl7_22
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f320,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f319,f197])).

fof(f197,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl7_21
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f319,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f318,f65])).

fof(f65,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl7_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f318,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f317,f173])).

fof(f173,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl7_15
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f317,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_19
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f316,f189])).

fof(f189,plain,
    ( v2_pre_topc(sK3)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl7_19
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f316,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f315,f69])).

fof(f69,plain,
    ( ~ v2_struct_0(sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl7_2
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f315,plain,
    ( v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f314,f97])).

fof(f97,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl7_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f314,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_8
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f284,f93])).

fof(f93,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl7_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f284,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_29 ),
    inference(resolution,[],[f282,f59])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ v1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | v2_struct_0(X0)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ v1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | X4 != X5
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | r1_tmap_1(X1,X0,X2,X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f282,plain,
    ( r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl7_29
  <=> r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f227,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_24 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl7_24
  <=> r1_tmap_1(sK3,sK0,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f313,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k2_tmap_1(sK3,sK0,sK4,sK2)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f312,plain,
    ( spl7_34
    | ~ spl7_1
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f308,f294,f200,f196,f112,f108,f96,f92,f88,f84,f80,f76,f64,f310])).

fof(f310,plain,
    ( spl7_34
  <=> k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f76,plain,
    ( spl7_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f80,plain,
    ( spl7_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f84,plain,
    ( spl7_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f112,plain,
    ( spl7_13
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f294,plain,
    ( spl7_30
  <=> k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f308,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2)
    | ~ spl7_1
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_30 ),
    inference(forward_demodulation,[],[f307,f295])).

fof(f295,plain,
    ( k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f294])).

fof(f307,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | ~ spl7_1
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(resolution,[],[f290,f109])).

fof(f290,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | ~ spl7_1
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f289,f89])).

fof(f289,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | ~ spl7_1
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f288,f197])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | ~ spl7_1
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f287,f65])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f286,f97])).

fof(f286,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f285,f93])).

fof(f285,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(resolution,[],[f158,f201])).

fof(f158,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,sK3)
        | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2)) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f157,f154])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | m1_pre_topc(X0,sK1) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f153,f81])).

fof(f81,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK3)
        | m1_pre_topc(X0,sK1) )
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f139,f85])).

fof(f85,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK3)
        | m1_pre_topc(X0,sK1) )
    | ~ spl7_13 ),
    inference(resolution,[],[f113,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f113,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f112])).

fof(f157,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X2,sK1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ m1_pre_topc(X2,sK3)
        | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2)) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f156,f77])).

fof(f77,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f156,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X2,sK1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ m1_pre_topc(X2,sK3)
        | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2)) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f155,f85])).

fof(f155,plain,
    ( ! [X2,X3,X1] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X2,sK1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ m1_pre_topc(X2,sK3)
        | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2)) )
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f140,f81])).

fof(f140,plain,
    ( ! [X2,X3,X1] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X2,sK1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ m1_pre_topc(X2,sK3)
        | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2)) )
    | ~ spl7_13 ),
    inference(resolution,[],[f113,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f296,plain,
    ( spl7_30
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f267,f200,f196,f188,f172,f108,f96,f92,f88,f68,f64,f294])).

fof(f267,plain,
    ( k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(resolution,[],[f212,f109])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f211,f69])).

fof(f211,plain,
    ( ! [X0] :
        ( v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | ~ spl7_1
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f210,f197])).

fof(f210,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | ~ spl7_1
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f209,f65])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f208,f97])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | spl7_7
    | ~ spl7_8
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f207,f93])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | spl7_7
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f206,f89])).

fof(f206,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f205,f173])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK3)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f203,f189])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | ~ spl7_22 ),
    inference(resolution,[],[f201,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f283,plain,
    ( spl7_29
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f279,f252,f226,f200,f196,f188,f184,f176,f172,f108,f96,f92,f88,f72,f68,f64,f281])).

fof(f279,plain,
    ( r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f278,f236])).

fof(f236,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f226])).

fof(f278,plain,
    ( r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f277,f73])).

fof(f277,plain,
    ( v2_struct_0(sK2)
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f276,f177])).

fof(f276,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK2)
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f275,f109])).

fof(f275,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK2)
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f271,f253])).

fof(f271,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK2)
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(resolution,[],[f220,f185])).

fof(f220,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | v2_struct_0(X1)
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)
        | ~ r1_tmap_1(sK3,sK0,sK4,X2) )
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f219,f89])).

fof(f219,plain,
    ( ! [X2,X1] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)
        | ~ r1_tmap_1(sK3,sK0,sK4,X2) )
    | ~ spl7_1
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f218,f197])).

fof(f218,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)
        | ~ r1_tmap_1(sK3,sK0,sK4,X2) )
    | ~ spl7_1
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f217,f65])).

fof(f217,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)
        | ~ r1_tmap_1(sK3,sK0,sK4,X2) )
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f216,f173])).

fof(f216,plain,
    ( ! [X2,X1] :
        ( ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)
        | ~ r1_tmap_1(sK3,sK0,sK4,X2) )
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f215,f189])).

fof(f215,plain,
    ( ! [X2,X1] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)
        | ~ r1_tmap_1(sK3,sK0,sK4,X2) )
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f214,f69])).

fof(f214,plain,
    ( ! [X2,X1] :
        ( v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)
        | ~ r1_tmap_1(sK3,sK0,sK4,X2) )
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f213,f97])).

fof(f213,plain,
    ( ! [X2,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)
        | ~ r1_tmap_1(sK3,sK0,sK4,X2) )
    | ~ spl7_8
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f204,f93])).

fof(f204,plain,
    ( ! [X2,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)
        | ~ r1_tmap_1(sK3,sK0,sK4,X2) )
    | ~ spl7_22 ),
    inference(resolution,[],[f201,f58])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | v2_struct_0(X0)
      | v2_struct_0(X3)
      | ~ v1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ v1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | X4 != X5
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f254,plain,
    ( spl7_28
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f250,f239,f116,f112,f104,f84,f80,f76,f68,f252])).

fof(f104,plain,
    ( spl7_11
  <=> v1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f116,plain,
    ( spl7_14
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f239,plain,
    ( spl7_26
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f250,plain,
    ( v1_tsep_1(sK2,sK3)
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f249,f69])).

fof(f249,plain,
    ( v2_struct_0(sK3)
    | v1_tsep_1(sK2,sK3)
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f247,f113])).

fof(f247,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | v1_tsep_1(sK2,sK3)
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(resolution,[],[f124,f240])).

fof(f240,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f239])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | v1_tsep_1(sK2,X0) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f123,f117])).

fof(f117,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f116])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | v1_tsep_1(sK2,X0) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f122,f77])).

fof(f122,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | v1_tsep_1(sK2,X0) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f121,f85])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | v1_tsep_1(sK2,X0) )
    | ~ spl7_5
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f119,f81])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | v1_tsep_1(sK2,X0) )
    | ~ spl7_11 ),
    inference(resolution,[],[f105,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | v1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
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
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).

fof(f105,plain,
    ( v1_tsep_1(sK2,sK1)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f241,plain,
    ( spl7_26
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f147,f112,f108,f84,f239])).

fof(f147,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f129,f142])).

fof(f142,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f137,f85])).

fof(f137,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3)
    | ~ spl7_13 ),
    inference(resolution,[],[f113,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f129,plain,
    ( ~ l1_pre_topc(sK3)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl7_12 ),
    inference(resolution,[],[f109,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f237,plain,
    ( spl7_24
    | spl7_25 ),
    inference(avatar_split_clause,[],[f235,f229,f226])).

fof(f229,plain,
    ( spl7_25
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f235,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_25 ),
    inference(subsumption_resolution,[],[f62,f230])).

fof(f230,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f229])).

fof(f62,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(forward_demodulation,[],[f27,f30])).

fof(f30,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & m1_pre_topc(X2,X1)
                            & v1_tsep_1(X2,X1) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X0,X4,X5)
                                    <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X2,X1)
                          & v1_tsep_1(X2,X1) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X0,X4,X5)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).

fof(f27,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f12])).

fof(f231,plain,
    ( ~ spl7_24
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f61,f229,f226])).

fof(f61,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(forward_demodulation,[],[f28,f30])).

fof(f28,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f12])).

fof(f202,plain,(
    spl7_22 ),
    inference(avatar_split_clause,[],[f34,f200])).

fof(f34,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f198,plain,(
    spl7_21 ),
    inference(avatar_split_clause,[],[f33,f196])).

fof(f33,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f190,plain,
    ( spl7_19
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f149,f112,f84,f80,f188])).

fof(f149,plain,
    ( v2_pre_topc(sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f148,f81])).

fof(f148,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK3)
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f138,f85])).

fof(f138,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK3)
    | ~ spl7_13 ),
    inference(resolution,[],[f113,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f186,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f60,f184])).

fof(f60,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f29,f30])).

fof(f29,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f178,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f31,f176])).

fof(f31,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f174,plain,
    ( spl7_15
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f142,f112,f84,f172])).

fof(f118,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f41,f116])).

fof(f41,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f114,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f39,f112])).

fof(f39,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f110,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f37,f108])).

fof(f37,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f106,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f35,f104])).

fof(f35,plain,(
    v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f98,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f47,f96])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f94,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f46,f92])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f90,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f45,f88])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f86,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f44,f84])).

fof(f44,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f82,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f43,f80])).

fof(f43,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f42,f76])).

fof(f42,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f74,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f40,f72])).

fof(f40,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f38,f68])).

fof(f38,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f66,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f32,f64])).

fof(f32,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (16674)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (16674)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f332,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f66,f70,f74,f78,f82,f86,f90,f94,f98,f106,f110,f114,f118,f174,f178,f186,f190,f198,f202,f231,f237,f241,f254,f283,f296,f312,f313,f330,f331])).
% 0.21/0.47  fof(f331,plain,(
% 0.21/0.47    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k2_tmap_1(sK3,sK0,sK4,sK2) | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)),
% 0.21/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.47  fof(f330,plain,(
% 0.21/0.47    ~spl7_1 | spl7_2 | spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_22 | spl7_24 | ~spl7_28 | ~spl7_29),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f329])).
% 0.21/0.47  fof(f329,plain,(
% 0.21/0.47    $false | (~spl7_1 | spl7_2 | spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_22 | spl7_24 | ~spl7_28 | ~spl7_29)),
% 0.21/0.47    inference(subsumption_resolution,[],[f227,f327])).
% 0.21/0.47  fof(f327,plain,(
% 0.21/0.47    r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_22 | ~spl7_28 | ~spl7_29)),
% 0.21/0.47    inference(subsumption_resolution,[],[f326,f89])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ~v2_struct_0(sK0) | spl7_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f88])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl7_7 <=> v2_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.47  fof(f326,plain,(
% 0.21/0.47    v2_struct_0(sK0) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_22 | ~spl7_28 | ~spl7_29)),
% 0.21/0.47    inference(subsumption_resolution,[],[f325,f185])).
% 0.21/0.47  fof(f185,plain,(
% 0.21/0.47    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl7_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f184])).
% 0.21/0.47  fof(f184,plain,(
% 0.21/0.47    spl7_18 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.47  fof(f325,plain,(
% 0.21/0.47    ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_16 | ~spl7_19 | ~spl7_21 | ~spl7_22 | ~spl7_28 | ~spl7_29)),
% 0.21/0.47    inference(subsumption_resolution,[],[f324,f177])).
% 0.21/0.47  fof(f177,plain,(
% 0.21/0.47    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl7_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f176])).
% 0.21/0.47  fof(f176,plain,(
% 0.21/0.47    spl7_16 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.47  fof(f324,plain,(
% 0.21/0.47    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_19 | ~spl7_21 | ~spl7_22 | ~spl7_28 | ~spl7_29)),
% 0.21/0.47    inference(subsumption_resolution,[],[f323,f109])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    m1_pre_topc(sK2,sK3) | ~spl7_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f108])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    spl7_12 <=> m1_pre_topc(sK2,sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.47  fof(f323,plain,(
% 0.21/0.47    ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_21 | ~spl7_22 | ~spl7_28 | ~spl7_29)),
% 0.21/0.47    inference(subsumption_resolution,[],[f322,f253])).
% 0.21/0.47  fof(f253,plain,(
% 0.21/0.47    v1_tsep_1(sK2,sK3) | ~spl7_28),
% 0.21/0.47    inference(avatar_component_clause,[],[f252])).
% 0.21/0.47  fof(f252,plain,(
% 0.21/0.47    spl7_28 <=> v1_tsep_1(sK2,sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.47  fof(f322,plain,(
% 0.21/0.47    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_21 | ~spl7_22 | ~spl7_29)),
% 0.21/0.47    inference(subsumption_resolution,[],[f321,f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ~v2_struct_0(sK2) | spl7_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl7_3 <=> v2_struct_0(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.47  fof(f321,plain,(
% 0.21/0.47    v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_21 | ~spl7_22 | ~spl7_29)),
% 0.21/0.47    inference(subsumption_resolution,[],[f320,f201])).
% 0.21/0.47  fof(f201,plain,(
% 0.21/0.47    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~spl7_22),
% 0.21/0.47    inference(avatar_component_clause,[],[f200])).
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    spl7_22 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.47  fof(f320,plain,(
% 0.21/0.47    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_21 | ~spl7_29)),
% 0.21/0.47    inference(subsumption_resolution,[],[f319,f197])).
% 0.21/0.47  fof(f197,plain,(
% 0.21/0.47    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~spl7_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f196])).
% 0.21/0.47  fof(f196,plain,(
% 0.21/0.47    spl7_21 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.47  fof(f319,plain,(
% 0.21/0.47    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_29)),
% 0.21/0.47    inference(subsumption_resolution,[],[f318,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    v1_funct_1(sK4) | ~spl7_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl7_1 <=> v1_funct_1(sK4)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.47  fof(f318,plain,(
% 0.21/0.47    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK0,sK4,sK5) | (spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_29)),
% 0.21/0.47    inference(subsumption_resolution,[],[f317,f173])).
% 0.21/0.47  fof(f173,plain,(
% 0.21/0.47    l1_pre_topc(sK3) | ~spl7_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f172])).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    spl7_15 <=> l1_pre_topc(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.47  fof(f317,plain,(
% 0.21/0.47    ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK0,sK4,sK5) | (spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_19 | ~spl7_29)),
% 0.21/0.47    inference(subsumption_resolution,[],[f316,f189])).
% 0.21/0.47  fof(f189,plain,(
% 0.21/0.47    v2_pre_topc(sK3) | ~spl7_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f188])).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    spl7_19 <=> v2_pre_topc(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.47  fof(f316,plain,(
% 0.21/0.47    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK0,sK4,sK5) | (spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_29)),
% 0.21/0.47    inference(subsumption_resolution,[],[f315,f69])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ~v2_struct_0(sK3) | spl7_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f68])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl7_2 <=> v2_struct_0(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.47  fof(f315,plain,(
% 0.21/0.47    v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_8 | ~spl7_9 | ~spl7_29)),
% 0.21/0.47    inference(subsumption_resolution,[],[f314,f97])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    l1_pre_topc(sK0) | ~spl7_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f96])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl7_9 <=> l1_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.47  fof(f314,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_8 | ~spl7_29)),
% 0.21/0.47    inference(subsumption_resolution,[],[f284,f93])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    v2_pre_topc(sK0) | ~spl7_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f92])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl7_8 <=> v2_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.47  fof(f284,plain,(
% 0.21/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK0,sK4,sK5) | ~spl7_29),
% 0.21/0.47    inference(resolution,[],[f282,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X2,X0,X5,X3,X1] : (~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | v2_struct_0(X0) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.21/0.47    inference(equality_resolution,[],[f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.21/0.47  fof(f282,plain,(
% 0.21/0.47    r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | ~spl7_29),
% 0.21/0.47    inference(avatar_component_clause,[],[f281])).
% 0.21/0.47  fof(f281,plain,(
% 0.21/0.47    spl7_29 <=> r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.21/0.47  fof(f227,plain,(
% 0.21/0.47    ~r1_tmap_1(sK3,sK0,sK4,sK5) | spl7_24),
% 0.21/0.47    inference(avatar_component_clause,[],[f226])).
% 0.21/0.47  fof(f226,plain,(
% 0.21/0.47    spl7_24 <=> r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.47  fof(f313,plain,(
% 0.21/0.47    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k2_tmap_1(sK3,sK0,sK4,sK2) | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | ~r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)),
% 0.21/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.47  fof(f312,plain,(
% 0.21/0.47    spl7_34 | ~spl7_1 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_21 | ~spl7_22 | ~spl7_30),
% 0.21/0.47    inference(avatar_split_clause,[],[f308,f294,f200,f196,f112,f108,f96,f92,f88,f84,f80,f76,f64,f310])).
% 0.21/0.47  fof(f310,plain,(
% 0.21/0.47    spl7_34 <=> k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl7_4 <=> v2_struct_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl7_5 <=> v2_pre_topc(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    spl7_6 <=> l1_pre_topc(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    spl7_13 <=> m1_pre_topc(sK3,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.47  fof(f294,plain,(
% 0.21/0.47    spl7_30 <=> k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.47  fof(f308,plain,(
% 0.21/0.47    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2) | (~spl7_1 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_21 | ~spl7_22 | ~spl7_30)),
% 0.21/0.47    inference(forward_demodulation,[],[f307,f295])).
% 0.21/0.47  fof(f295,plain,(
% 0.21/0.47    k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) | ~spl7_30),
% 0.21/0.47    inference(avatar_component_clause,[],[f294])).
% 0.21/0.47  fof(f307,plain,(
% 0.21/0.47    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) | (~spl7_1 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_21 | ~spl7_22)),
% 0.21/0.47    inference(resolution,[],[f290,f109])).
% 0.21/0.47  fof(f290,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (~spl7_1 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_21 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f289,f89])).
% 0.21/0.47  fof(f289,plain,(
% 0.21/0.47    ( ! [X0] : (v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (~spl7_1 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_21 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f288,f197])).
% 0.21/0.47  fof(f288,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (~spl7_1 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f287,f65])).
% 0.21/0.47  fof(f287,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f286,f97])).
% 0.21/0.47  fof(f286,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_13 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f285,f93])).
% 0.21/0.47  fof(f285,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | ~spl7_22)),
% 0.21/0.47    inference(resolution,[],[f158,f201])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    ( ! [X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2))) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f157,f154])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK1)) ) | (~spl7_5 | ~spl7_6 | ~spl7_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f153,f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    v2_pre_topc(sK1) | ~spl7_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f80])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_pre_topc(sK1) | ~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK1)) ) | (~spl7_6 | ~spl7_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f139,f85])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    l1_pre_topc(sK1) | ~spl7_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f84])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK1)) ) | ~spl7_13),
% 0.21/0.47    inference(resolution,[],[f113,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    m1_pre_topc(sK3,sK1) | ~spl7_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f112])).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    ( ! [X2,X3,X1] : (v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2))) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f156,f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ~v2_struct_0(sK1) | spl7_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f76])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    ( ! [X2,X3,X1] : (v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK1) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2))) ) | (~spl7_5 | ~spl7_6 | ~spl7_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f155,f85])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    ( ! [X2,X3,X1] : (~l1_pre_topc(sK1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK1) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2))) ) | (~spl7_5 | ~spl7_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f140,f81])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    ( ! [X2,X3,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK1) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2))) ) | ~spl7_13),
% 0.21/0.47    inference(resolution,[],[f113,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.21/0.47  fof(f296,plain,(
% 0.21/0.47    spl7_30 | ~spl7_1 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_19 | ~spl7_21 | ~spl7_22),
% 0.21/0.47    inference(avatar_split_clause,[],[f267,f200,f196,f188,f172,f108,f96,f92,f88,f68,f64,f294])).
% 0.21/0.47  fof(f267,plain,(
% 0.21/0.47    k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) | (~spl7_1 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_19 | ~spl7_21 | ~spl7_22)),
% 0.21/0.47    inference(resolution,[],[f212,f109])).
% 0.21/0.47  fof(f212,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (~spl7_1 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_21 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f211,f69])).
% 0.21/0.47  fof(f211,plain,(
% 0.21/0.47    ( ! [X0] : (v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (~spl7_1 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_21 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f210,f197])).
% 0.21/0.47  fof(f210,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (~spl7_1 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f209,f65])).
% 0.21/0.47  fof(f209,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f208,f97])).
% 0.21/0.47  fof(f208,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (spl7_7 | ~spl7_8 | ~spl7_15 | ~spl7_19 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f207,f93])).
% 0.21/0.47  fof(f207,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (spl7_7 | ~spl7_15 | ~spl7_19 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f206,f89])).
% 0.21/0.47  fof(f206,plain,(
% 0.21/0.47    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (~spl7_15 | ~spl7_19 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f205,f173])).
% 0.21/0.47  fof(f205,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(sK3) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (~spl7_19 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f203,f189])).
% 0.21/0.47  fof(f203,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | ~spl7_22),
% 0.21/0.47    inference(resolution,[],[f201,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.21/0.47  fof(f283,plain,(
% 0.21/0.47    spl7_29 | ~spl7_1 | spl7_2 | spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_22 | ~spl7_24 | ~spl7_28),
% 0.21/0.47    inference(avatar_split_clause,[],[f279,f252,f226,f200,f196,f188,f184,f176,f172,f108,f96,f92,f88,f72,f68,f64,f281])).
% 0.21/0.47  fof(f279,plain,(
% 0.21/0.47    r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | (~spl7_1 | spl7_2 | spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_22 | ~spl7_24 | ~spl7_28)),
% 0.21/0.47    inference(subsumption_resolution,[],[f278,f236])).
% 0.21/0.47  fof(f236,plain,(
% 0.21/0.47    r1_tmap_1(sK3,sK0,sK4,sK5) | ~spl7_24),
% 0.21/0.47    inference(avatar_component_clause,[],[f226])).
% 0.21/0.47  fof(f278,plain,(
% 0.21/0.47    r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_22 | ~spl7_28)),
% 0.21/0.47    inference(subsumption_resolution,[],[f277,f73])).
% 0.21/0.47  fof(f277,plain,(
% 0.21/0.47    v2_struct_0(sK2) | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_22 | ~spl7_28)),
% 0.21/0.47    inference(subsumption_resolution,[],[f276,f177])).
% 0.21/0.47  fof(f276,plain,(
% 0.21/0.47    ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK2) | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_22 | ~spl7_28)),
% 0.21/0.47    inference(subsumption_resolution,[],[f275,f109])).
% 0.21/0.47  fof(f275,plain,(
% 0.21/0.47    ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK2) | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_22 | ~spl7_28)),
% 0.21/0.47    inference(subsumption_resolution,[],[f271,f253])).
% 0.21/0.47  fof(f271,plain,(
% 0.21/0.47    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK2) | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_22)),
% 0.21/0.47    inference(resolution,[],[f220,f185])).
% 0.21/0.47  fof(f220,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) | ~r1_tmap_1(sK3,sK0,sK4,X2)) ) | (~spl7_1 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_21 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f219,f89])).
% 0.21/0.47  fof(f219,plain,(
% 0.21/0.47    ( ! [X2,X1] : (v2_struct_0(sK0) | v2_struct_0(X1) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) | ~r1_tmap_1(sK3,sK0,sK4,X2)) ) | (~spl7_1 | spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_21 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f218,f197])).
% 0.21/0.47  fof(f218,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) | ~r1_tmap_1(sK3,sK0,sK4,X2)) ) | (~spl7_1 | spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f217,f65])).
% 0.21/0.47  fof(f217,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) | ~r1_tmap_1(sK3,sK0,sK4,X2)) ) | (spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f216,f173])).
% 0.21/0.47  fof(f216,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) | ~r1_tmap_1(sK3,sK0,sK4,X2)) ) | (spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_19 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f215,f189])).
% 0.21/0.47  fof(f215,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) | ~r1_tmap_1(sK3,sK0,sK4,X2)) ) | (spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f214,f69])).
% 0.21/0.47  fof(f214,plain,(
% 0.21/0.47    ( ! [X2,X1] : (v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) | ~r1_tmap_1(sK3,sK0,sK4,X2)) ) | (~spl7_8 | ~spl7_9 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f213,f97])).
% 0.21/0.47  fof(f213,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) | ~r1_tmap_1(sK3,sK0,sK4,X2)) ) | (~spl7_8 | ~spl7_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f204,f93])).
% 0.21/0.47  fof(f204,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) | ~r1_tmap_1(sK3,sK0,sK4,X2)) ) | ~spl7_22),
% 0.21/0.47    inference(resolution,[],[f201,f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | v2_struct_0(X0) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5)) )),
% 0.21/0.47    inference(equality_resolution,[],[f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f254,plain,(
% 0.21/0.47    spl7_28 | spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_26),
% 0.21/0.47    inference(avatar_split_clause,[],[f250,f239,f116,f112,f104,f84,f80,f76,f68,f252])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    spl7_11 <=> v1_tsep_1(sK2,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    spl7_14 <=> m1_pre_topc(sK2,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.47  fof(f239,plain,(
% 0.21/0.47    spl7_26 <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.21/0.47  fof(f250,plain,(
% 0.21/0.47    v1_tsep_1(sK2,sK3) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_26)),
% 0.21/0.47    inference(subsumption_resolution,[],[f249,f69])).
% 0.21/0.47  fof(f249,plain,(
% 0.21/0.47    v2_struct_0(sK3) | v1_tsep_1(sK2,sK3) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_26)),
% 0.21/0.47    inference(subsumption_resolution,[],[f247,f113])).
% 0.21/0.47  fof(f247,plain,(
% 0.21/0.47    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | v1_tsep_1(sK2,sK3) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_14 | ~spl7_26)),
% 0.21/0.47    inference(resolution,[],[f124,f240])).
% 0.21/0.47  fof(f240,plain,(
% 0.21/0.47    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl7_26),
% 0.21/0.47    inference(avatar_component_clause,[],[f239])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | v1_tsep_1(sK2,X0)) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_14)),
% 0.21/0.47    inference(subsumption_resolution,[],[f123,f117])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    m1_pre_topc(sK2,sK1) | ~spl7_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f116])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_pre_topc(sK2,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | v1_tsep_1(sK2,X0)) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11)),
% 0.21/0.47    inference(subsumption_resolution,[],[f122,f77])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ( ! [X0] : (v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | v1_tsep_1(sK2,X0)) ) | (~spl7_5 | ~spl7_6 | ~spl7_11)),
% 0.21/0.47    inference(subsumption_resolution,[],[f121,f85])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | v1_tsep_1(sK2,X0)) ) | (~spl7_5 | ~spl7_11)),
% 0.21/0.47    inference(subsumption_resolution,[],[f119,f81])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | v1_tsep_1(sK2,X0)) ) | ~spl7_11),
% 0.21/0.47    inference(resolution,[],[f105,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_tsep_1(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v1_tsep_1(X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    v1_tsep_1(sK2,sK1) | ~spl7_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f104])).
% 0.21/0.47  fof(f241,plain,(
% 0.21/0.47    spl7_26 | ~spl7_6 | ~spl7_12 | ~spl7_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f147,f112,f108,f84,f239])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | (~spl7_6 | ~spl7_12 | ~spl7_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f129,f142])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    l1_pre_topc(sK3) | (~spl7_6 | ~spl7_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f137,f85])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    ~l1_pre_topc(sK1) | l1_pre_topc(sK3) | ~spl7_13),
% 0.21/0.47    inference(resolution,[],[f113,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ~l1_pre_topc(sK3) | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl7_12),
% 0.21/0.47    inference(resolution,[],[f109,f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.47  fof(f237,plain,(
% 0.21/0.47    spl7_24 | spl7_25),
% 0.21/0.47    inference(avatar_split_clause,[],[f235,f229,f226])).
% 0.21/0.47  fof(f229,plain,(
% 0.21/0.47    spl7_25 <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.21/0.47  fof(f235,plain,(
% 0.21/0.47    r1_tmap_1(sK3,sK0,sK4,sK5) | spl7_25),
% 0.21/0.47    inference(subsumption_resolution,[],[f62,f230])).
% 0.21/0.47  fof(f230,plain,(
% 0.21/0.47    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | spl7_25),
% 0.21/0.47    inference(avatar_component_clause,[],[f229])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.47    inference(forward_demodulation,[],[f27,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    sK5 = sK6),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f9])).
% 0.21/0.47  fof(f9,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f231,plain,(
% 0.21/0.47    ~spl7_24 | ~spl7_25),
% 0.21/0.47    inference(avatar_split_clause,[],[f61,f229,f226])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.47    inference(forward_demodulation,[],[f28,f30])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f202,plain,(
% 0.21/0.47    spl7_22),
% 0.21/0.47    inference(avatar_split_clause,[],[f34,f200])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f198,plain,(
% 0.21/0.47    spl7_21),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f196])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f190,plain,(
% 0.21/0.47    spl7_19 | ~spl7_5 | ~spl7_6 | ~spl7_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f149,f112,f84,f80,f188])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    v2_pre_topc(sK3) | (~spl7_5 | ~spl7_6 | ~spl7_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f148,f81])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    ~v2_pre_topc(sK1) | v2_pre_topc(sK3) | (~spl7_6 | ~spl7_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f138,f85])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_pre_topc(sK3) | ~spl7_13),
% 0.21/0.47    inference(resolution,[],[f113,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    spl7_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f60,f184])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.47    inference(forward_demodulation,[],[f29,f30])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    spl7_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f31,f176])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f174,plain,(
% 0.21/0.47    spl7_15 | ~spl7_6 | ~spl7_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f142,f112,f84,f172])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    spl7_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f41,f116])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    m1_pre_topc(sK2,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl7_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f39,f112])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    m1_pre_topc(sK3,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    spl7_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f37,f108])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    m1_pre_topc(sK2,sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    spl7_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f35,f104])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    v1_tsep_1(sK2,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    spl7_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f47,f96])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl7_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f46,f92])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ~spl7_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f45,f88])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl7_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f44,f84])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    l1_pre_topc(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    spl7_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f43,f80])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    v2_pre_topc(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ~spl7_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f42,f76])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ~v2_struct_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ~spl7_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f72])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ~v2_struct_0(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ~spl7_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f38,f68])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ~v2_struct_0(sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    spl7_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f64])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    v1_funct_1(sK4)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (16674)------------------------------
% 0.21/0.47  % (16674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (16674)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (16674)Memory used [KB]: 6396
% 0.21/0.47  % (16674)Time elapsed: 0.063 s
% 0.21/0.47  % (16674)------------------------------
% 0.21/0.47  % (16674)------------------------------
% 0.21/0.48  % (16671)Success in time 0.121 s
%------------------------------------------------------------------------------
