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
% DateTime   : Thu Dec  3 13:18:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 394 expanded)
%              Number of leaves         :   35 ( 227 expanded)
%              Depth                    :    7
%              Number of atoms          :  593 (4109 expanded)
%              Number of equality atoms :   41 ( 313 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f72,f77,f82,f87,f92,f97,f102,f107,f112,f117,f122,f127,f132,f139,f152,f164,f172,f177,f178])).

fof(f178,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | k2_tmap_1(sK3,sK1,sK4,sK2) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f177,plain,
    ( spl6_24
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_9
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f165,f149,f136,f114,f109,f104,f89,f79,f74,f69,f64,f174])).

fof(f174,plain,
    ( spl6_24
  <=> k2_tmap_1(sK3,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f64,plain,
    ( spl6_4
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f69,plain,
    ( spl6_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f74,plain,
    ( spl6_6
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f79,plain,
    ( spl6_7
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f89,plain,
    ( spl6_9
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f104,plain,
    ( spl6_12
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f109,plain,
    ( spl6_13
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f114,plain,
    ( spl6_14
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f136,plain,
    ( spl6_18
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f149,plain,
    ( spl6_20
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f165,plain,
    ( k2_tmap_1(sK3,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_9
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f91,f66,f138,f116,f111,f106,f81,f76,f71,f151,f43])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f151,plain,
    ( v2_pre_topc(sK3)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f149])).

fof(f71,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f76,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f81,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f106,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f104])).

fof(f111,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f109])).

fof(f116,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f114])).

fof(f138,plain,
    ( l1_pre_topc(sK3)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f136])).

fof(f66,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f91,plain,
    ( ~ v2_struct_0(sK3)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f172,plain,
    ( spl6_23
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_9
    | spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f166,f149,f136,f114,f109,f104,f99,f89,f79,f74,f69,f64,f59,f54,f169])).

fof(f169,plain,
    ( spl6_23
  <=> k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f54,plain,
    ( spl6_2
  <=> r1_tarski(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f59,plain,
    ( spl6_3
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f99,plain,
    ( spl6_11
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f166,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_9
    | spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f116,f111,f106,f91,f81,f138,f101,f66,f56,f61,f76,f71,f151,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | ~ r1_tarski(X4,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ~ r1_tarski(X4,u1_struct_0(X2))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
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
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ~ r1_tarski(X4,u1_struct_0(X2))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
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
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r1_tarski(X4,u1_struct_0(X2))
                       => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tmap_1)).

fof(f61,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f56,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f101,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f164,plain,
    ( spl6_22
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_17 ),
    inference(avatar_split_clause,[],[f158,f129,f124,f119,f114,f109,f104,f94,f84,f79,f74,f69,f64,f161])).

fof(f161,plain,
    ( spl6_22
  <=> k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f84,plain,
    ( spl6_8
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f94,plain,
    ( spl6_10
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f119,plain,
    ( spl6_15
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f124,plain,
    ( spl6_16
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f129,plain,
    ( spl6_17
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f158,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_17 ),
    inference(unit_resulting_resolution,[],[f131,f126,f121,f116,f111,f106,f86,f96,f81,f66,f76,f71,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f96,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f86,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f121,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f119])).

fof(f126,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f124])).

fof(f131,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f129])).

fof(f152,plain,
    ( spl6_20
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f147,f124,f119,f84,f149])).

fof(f147,plain,
    ( v2_pre_topc(sK3)
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f126,f121,f86,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f139,plain,
    ( spl6_18
    | ~ spl6_8
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f134,f119,f84,f136])).

fof(f134,plain,
    ( l1_pre_topc(sK3)
    | ~ spl6_8
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f121,f86,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f132,plain,(
    ~ spl6_17 ),
    inference(avatar_split_clause,[],[f26,f129])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    & r1_tarski(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f24,f23,f22,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                            & r1_tarski(X5,u1_struct_0(X2))
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
                      ( ? [X5] :
                          ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5)
                          & r1_tarski(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5)
                        & r1_tarski(X5,u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
                  ( ? [X5] :
                      ( k7_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X4),X5)
                      & r1_tarski(X5,u1_struct_0(X2))
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k7_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X4),X5)
                    & r1_tarski(X5,u1_struct_0(X2))
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                & m1_pre_topc(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X4),X5)
                  & r1_tarski(X5,u1_struct_0(sK2))
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
              & m1_pre_topc(sK2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k7_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X4),X5)
                & r1_tarski(X5,u1_struct_0(sK2))
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
            & m1_pre_topc(sK2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5)
              & r1_tarski(X5,u1_struct_0(sK2))
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) )
          & m1_pre_topc(sK2,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5)
            & r1_tarski(X5,u1_struct_0(sK2))
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) )
        & m1_pre_topc(sK2,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5)
          & r1_tarski(X5,u1_struct_0(sK2))
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) )
      & m1_pre_topc(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X5] :
        ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5)
        & r1_tarski(X5,u1_struct_0(sK2))
        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
      & r1_tarski(sK5,u1_struct_0(sK2))
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r1_tarski(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r1_tarski(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                             => ( r1_tarski(X5,u1_struct_0(X2))
                               => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ( r1_tarski(X5,u1_struct_0(X2))
                             => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tmap_1)).

fof(f127,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f27,f124])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f122,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f28,f119])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f117,plain,(
    ~ spl6_14 ),
    inference(avatar_split_clause,[],[f29,f114])).

fof(f29,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f112,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f30,f109])).

fof(f30,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f107,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f31,f104])).

fof(f31,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f102,plain,(
    ~ spl6_11 ),
    inference(avatar_split_clause,[],[f32,f99])).

fof(f32,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f97,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f33,f94])).

fof(f33,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f92,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f34,f89])).

fof(f34,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f35,f84])).

fof(f35,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f36,f79])).

fof(f36,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f37,f74])).

fof(f37,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f39,f64])).

fof(f39,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f40,f59])).

fof(f40,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f41,f54])).

fof(f41,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f42,f49])).

fof(f49,plain,
    ( spl6_1
  <=> k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f42,plain,(
    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:34:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (13362)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.51  % (13356)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (13357)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (13358)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (13376)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (13368)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.51  % (13374)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (13359)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.52  % (13354)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.52  % (13376)Refutation not found, incomplete strategy% (13376)------------------------------
% 0.22/0.52  % (13376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13360)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (13359)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (13376)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13376)Memory used [KB]: 10618
% 0.22/0.52  % (13376)Time elapsed: 0.054 s
% 0.22/0.52  % (13376)------------------------------
% 0.22/0.52  % (13376)------------------------------
% 0.22/0.52  % (13365)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % (13366)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (13364)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (13356)Refutation not found, incomplete strategy% (13356)------------------------------
% 0.22/0.52  % (13356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13356)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13356)Memory used [KB]: 10618
% 0.22/0.52  % (13356)Time elapsed: 0.102 s
% 0.22/0.52  % (13356)------------------------------
% 0.22/0.52  % (13356)------------------------------
% 0.22/0.52  % (13367)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (13375)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.53  % (13372)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.53  % (13361)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f72,f77,f82,f87,f92,f97,f102,f107,f112,f117,f122,f127,f132,f139,f152,f164,f172,f177,f178])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | k2_tmap_1(sK3,sK1,sK4,sK2) != k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    spl6_24 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | spl6_9 | ~spl6_12 | ~spl6_13 | spl6_14 | ~spl6_18 | ~spl6_20),
% 0.22/0.53    inference(avatar_split_clause,[],[f165,f149,f136,f114,f109,f104,f89,f79,f74,f69,f64,f174])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    spl6_24 <=> k2_tmap_1(sK3,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    spl6_4 <=> m1_pre_topc(sK2,sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    spl6_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    spl6_6 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    spl6_7 <=> v1_funct_1(sK4)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl6_9 <=> v2_struct_0(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    spl6_12 <=> l1_pre_topc(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    spl6_13 <=> v2_pre_topc(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    spl6_14 <=> v2_struct_0(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    spl6_18 <=> l1_pre_topc(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    spl6_20 <=> v2_pre_topc(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    k2_tmap_1(sK3,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | spl6_9 | ~spl6_12 | ~spl6_13 | spl6_14 | ~spl6_18 | ~spl6_20)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f91,f66,f138,f116,f111,f106,f81,f76,f71,f151,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    v2_pre_topc(sK3) | ~spl6_20),
% 0.22/0.53    inference(avatar_component_clause,[],[f149])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl6_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f69])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl6_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f74])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    v1_funct_1(sK4) | ~spl6_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f79])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    l1_pre_topc(sK1) | ~spl6_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f104])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    v2_pre_topc(sK1) | ~spl6_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f109])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    ~v2_struct_0(sK1) | spl6_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f114])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    l1_pre_topc(sK3) | ~spl6_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f136])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    m1_pre_topc(sK2,sK3) | ~spl6_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f64])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ~v2_struct_0(sK3) | spl6_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f89])).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    spl6_23 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | spl6_9 | spl6_11 | ~spl6_12 | ~spl6_13 | spl6_14 | ~spl6_18 | ~spl6_20),
% 0.22/0.53    inference(avatar_split_clause,[],[f166,f149,f136,f114,f109,f104,f99,f89,f79,f74,f69,f64,f59,f54,f169])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    spl6_23 <=> k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    spl6_2 <=> r1_tarski(sK5,u1_struct_0(sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    spl6_3 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    spl6_11 <=> v2_struct_0(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | spl6_9 | spl6_11 | ~spl6_12 | ~spl6_13 | spl6_14 | ~spl6_18 | ~spl6_20)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f116,f111,f106,f91,f81,f138,f101,f66,f56,f61,f76,f71,f151,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ~r1_tarski(X4,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ~r1_tarski(X4,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ~r1_tarski(X4,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tmap_1)).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~spl6_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f59])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    r1_tarski(sK5,u1_struct_0(sK2)) | ~spl6_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f54])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ~v2_struct_0(sK2) | spl6_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f99])).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    spl6_22 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10 | ~spl6_12 | ~spl6_13 | spl6_14 | ~spl6_15 | ~spl6_16 | spl6_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f158,f129,f124,f119,f114,f109,f104,f94,f84,f79,f74,f69,f64,f161])).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    spl6_22 <=> k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    spl6_8 <=> m1_pre_topc(sK3,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    spl6_10 <=> m1_pre_topc(sK2,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    spl6_15 <=> l1_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    spl6_16 <=> v2_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    spl6_17 <=> v2_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10 | ~spl6_12 | ~spl6_13 | spl6_14 | ~spl6_15 | ~spl6_16 | spl6_17)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f131,f126,f121,f116,f111,f106,f86,f96,f81,f66,f76,f71,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    m1_pre_topc(sK2,sK0) | ~spl6_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f94])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    m1_pre_topc(sK3,sK0) | ~spl6_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f84])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    l1_pre_topc(sK0) | ~spl6_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f119])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    v2_pre_topc(sK0) | ~spl6_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f124])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    ~v2_struct_0(sK0) | spl6_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f129])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    spl6_20 | ~spl6_8 | ~spl6_15 | ~spl6_16),
% 0.22/0.53    inference(avatar_split_clause,[],[f147,f124,f119,f84,f149])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    v2_pre_topc(sK3) | (~spl6_8 | ~spl6_15 | ~spl6_16)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f126,f121,f86,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    spl6_18 | ~spl6_8 | ~spl6_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f134,f119,f84,f136])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    l1_pre_topc(sK3) | (~spl6_8 | ~spl6_15)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f121,f86,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    ~spl6_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f26,f129])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    (((((k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & r1_tarski(sK5,u1_struct_0(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f24,f23,f22,f21,f20,f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X4),X5) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X4),X5) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ? [X5] : (k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) => (k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & r1_tarski(sK5,u1_struct_0(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => (r1_tarski(X5,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f6])).
% 0.22/0.53  fof(f6,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => (r1_tarski(X5,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tmap_1)).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    spl6_16),
% 0.22/0.53    inference(avatar_split_clause,[],[f27,f124])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    spl6_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f28,f119])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ~spl6_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f29,f114])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ~v2_struct_0(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    spl6_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f30,f109])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    v2_pre_topc(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    spl6_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f31,f104])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    l1_pre_topc(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ~spl6_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f32,f99])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ~v2_struct_0(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    spl6_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f33,f94])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    m1_pre_topc(sK2,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ~spl6_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f34,f89])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ~v2_struct_0(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    spl6_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f84])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    m1_pre_topc(sK3,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    spl6_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f36,f79])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    v1_funct_1(sK4)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl6_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f37,f74])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    spl6_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f38,f69])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    spl6_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f39,f64])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    m1_pre_topc(sK2,sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    spl6_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f40,f59])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    spl6_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f41,f54])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    r1_tarski(sK5,u1_struct_0(sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ~spl6_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f42,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    spl6_1 <=> k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (13359)------------------------------
% 0.22/0.53  % (13359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13359)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (13359)Memory used [KB]: 10874
% 0.22/0.53  % (13359)Time elapsed: 0.096 s
% 0.22/0.53  % (13359)------------------------------
% 0.22/0.53  % (13359)------------------------------
% 0.22/0.53  % (13352)Success in time 0.164 s
%------------------------------------------------------------------------------
