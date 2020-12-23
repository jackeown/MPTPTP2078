%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1745+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 320 expanded)
%              Number of leaves         :   30 ( 123 expanded)
%              Depth                    :   26
%              Number of atoms          : 1021 (2575 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   29 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f255,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f70,f75,f80,f85,f90,f95,f100,f119,f124,f129,f134,f139,f144,f149,f154,f199,f214,f218,f245,f251,f254])).

fof(f254,plain,
    ( ~ spl7_12
    | ~ spl7_23
    | spl7_27 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_23
    | spl7_27 ),
    inference(subsumption_resolution,[],[f252,f118])).

fof(f118,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl7_12
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f252,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl7_23
    | spl7_27 ),
    inference(resolution,[],[f250,f194])).

fof(f194,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl7_23
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f250,plain,
    ( ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | spl7_27 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl7_27
  <=> m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f251,plain,
    ( ~ spl7_27
    | ~ spl7_1
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_17
    | spl7_26 ),
    inference(avatar_split_clause,[],[f246,f242,f141,f131,f121,f97,f92,f87,f82,f77,f72,f47,f248])).

fof(f47,plain,
    ( spl7_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f72,plain,
    ( spl7_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f77,plain,
    ( spl7_7
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f82,plain,
    ( spl7_8
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f87,plain,
    ( spl7_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f92,plain,
    ( spl7_10
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f97,plain,
    ( spl7_11
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f121,plain,
    ( spl7_13
  <=> v5_pre_topc(sK4,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f131,plain,
    ( spl7_15
  <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f141,plain,
    ( spl7_17
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f242,plain,
    ( spl7_26
  <=> r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f246,plain,
    ( ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5),u1_struct_0(sK0))
    | ~ spl7_1
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_17
    | spl7_26 ),
    inference(resolution,[],[f244,f209])).

fof(f209,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK0,sK1,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_1
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f208,f123])).

fof(f123,plain,
    ( v5_pre_topc(sK4,sK0,sK1)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | ~ spl7_1
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f207,f89])).

fof(f89,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f207,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | ~ spl7_1
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f206,f133])).

fof(f133,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f131])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | ~ spl7_1
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f205,f49])).

fof(f49,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f204,f99])).

fof(f99,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f203,f94])).

fof(f94,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f92])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK0,sK1) )
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_17 ),
    inference(resolution,[],[f200,f143])).

fof(f143,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f141])).

fof(f200,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | v2_struct_0(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r1_tmap_1(X0,sK1,X1,X2)
        | ~ v5_pre_topc(X1,X0,sK1) )
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f109,f84])).

fof(f84,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f109,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r1_tmap_1(X0,sK1,X1,X2)
        | ~ v5_pre_topc(X1,X0,sK1) )
    | spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f107,f74])).

fof(f74,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f107,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r1_tmap_1(X0,sK1,X1,X2)
        | ~ v5_pre_topc(X1,X0,sK1) )
    | ~ spl7_7 ),
    inference(resolution,[],[f79,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r1_tmap_1(X1,X0,X2,X3)
      | ~ v5_pre_topc(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f79,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f244,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | spl7_26 ),
    inference(avatar_component_clause,[],[f242])).

fof(f245,plain,
    ( ~ spl7_26
    | ~ spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | spl7_19
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f240,f193,f151,f146,f141,f136,f131,f126,f116,f97,f92,f87,f82,f77,f72,f67,f62,f57,f52,f47,f242])).

fof(f52,plain,
    ( spl7_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f57,plain,
    ( spl7_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f62,plain,
    ( spl7_4
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f67,plain,
    ( spl7_5
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f126,plain,
    ( spl7_14
  <=> r1_tmap_1(sK2,sK0,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f136,plain,
    ( spl7_16
  <=> v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f146,plain,
    ( spl7_18
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f151,plain,
    ( spl7_19
  <=> r1_tmap_1(sK2,sK1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f240,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | ~ spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | spl7_19
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f239,f79])).

fof(f239,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | ~ v2_pre_topc(sK1)
    | ~ spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | spl7_19
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f238,f74])).

fof(f238,plain,
    ( v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | ~ v2_pre_topc(sK1)
    | ~ spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | spl7_19
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f237,f143])).

fof(f237,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | ~ v2_pre_topc(sK1)
    | ~ spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_18
    | spl7_19
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f236,f133])).

fof(f236,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | ~ v2_pre_topc(sK1)
    | ~ spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_18
    | spl7_19
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f235,f49])).

fof(f235,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | ~ v2_pre_topc(sK1)
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_18
    | spl7_19
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f234,f84])).

fof(f234,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ r1_tmap_1(sK0,sK1,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
    | ~ v2_pre_topc(sK1)
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_18
    | spl7_19
    | ~ spl7_23 ),
    inference(resolution,[],[f233,f153])).

fof(f153,plain,
    ( ~ r1_tmap_1(sK2,sK1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),sK5)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f151])).

fof(f233,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(sK2,X0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X0),sK3,X1),sK5)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ r1_tmap_1(sK0,X0,X1,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,sK5))
        | ~ v2_pre_topc(X0) )
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f232,f118])).

fof(f232,plain,
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
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_23 ),
    inference(resolution,[],[f229,f128])).

fof(f128,plain,
    ( r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f229,plain,
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
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f228,f148])).

fof(f148,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f146])).

fof(f228,plain,
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
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_16
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f227,f138])).

fof(f138,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f136])).

fof(f227,plain,
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
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f226,f54])).

fof(f54,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f226,plain,
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
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f225,f99])).

% (4772)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f225,plain,
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
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f224,f94])).

fof(f224,plain,
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
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f223,f89])).

fof(f223,plain,
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
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f222,f69])).

fof(f69,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f222,plain,
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
    | spl7_3
    | ~ spl7_4
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f221,f64])).

fof(f64,plain,
    ( v2_pre_topc(sK2)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f221,plain,
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
    | spl7_3
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f220,f59])).

fof(f59,plain,
    ( ~ v2_struct_0(sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f220,plain,
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
    | ~ spl7_23 ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,
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
    | ~ spl7_23 ),
    inference(resolution,[],[f194,f45])).

fof(f45,plain,(
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
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f218,plain,
    ( ~ spl7_5
    | spl7_25 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl7_5
    | spl7_25 ),
    inference(subsumption_resolution,[],[f216,f69])).

fof(f216,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_25 ),
    inference(resolution,[],[f213,f38])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f213,plain,
    ( ~ l1_struct_0(sK2)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl7_25
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f214,plain,
    ( ~ spl7_25
    | spl7_3
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f202,f196,f57,f211])).

fof(f196,plain,
    ( spl7_24
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f202,plain,
    ( ~ l1_struct_0(sK2)
    | spl7_3
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f201,f59])).

fof(f201,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_24 ),
    inference(resolution,[],[f198,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f198,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f196])).

fof(f199,plain,
    ( spl7_23
    | spl7_24
    | ~ spl7_2
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f166,f146,f136,f52,f196,f193])).

fof(f166,plain,
    ( ! [X0] :
        ( v1_xboole_0(u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0),u1_struct_0(sK0)) )
    | ~ spl7_2
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f165,f138])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK3,X0),u1_struct_0(sK0)) )
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(resolution,[],[f102,f148])).

fof(f102,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK3,X0,X1)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X2,X0)
        | m1_subset_1(k3_funct_2(X0,X1,sK3,X2),X1) )
    | ~ spl7_2 ),
    inference(resolution,[],[f54,f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f154,plain,(
    ~ spl7_19 ),
    inference(avatar_split_clause,[],[f22,f151])).

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

fof(f149,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f28,f146])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f144,plain,(
    spl7_17 ),
    inference(avatar_split_clause,[],[f25,f141])).

fof(f25,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f139,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f27,f136])).

fof(f27,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f134,plain,(
    spl7_15 ),
    inference(avatar_split_clause,[],[f24,f131])).

fof(f24,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f129,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f20,f126])).

fof(f20,plain,(
    r1_tmap_1(sK2,sK0,sK3,sK5) ),
    inference(cnf_transformation,[],[f9])).

fof(f124,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f21,f121])).

fof(f21,plain,(
    v5_pre_topc(sK4,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f119,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f19,f116])).

fof(f19,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f100,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f37,f97])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f95,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f36,f92])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f90,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f35,f87])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f85,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f34,f82])).

fof(f34,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f80,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    ~ spl7_6 ),
    inference(avatar_split_clause,[],[f32,f72])).

fof(f32,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f70,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f31,f67])).

fof(f31,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f60,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f29,f57])).

fof(f29,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f26,f52])).

fof(f26,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
