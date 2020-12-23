%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  292 ( 728 expanded)
%              Number of leaves         :   62 ( 344 expanded)
%              Depth                    :   24
%              Number of atoms          : 1919 (8801 expanded)
%              Number of equality atoms :   45 ( 452 expanded)
%              Maximal formula depth    :   32 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f477,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f162,f167,f172,f177,f183,f188,f195,f199,f210,f219,f233,f247,f254,f260,f261,f290,f334,f348,f357,f370,f375,f384,f392,f402,f407,f421,f428,f442,f447,f456,f476])).

fof(f476,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | spl10_8
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_13
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_25
    | spl10_26 ),
    inference(avatar_contradiction_clause,[],[f475])).

fof(f475,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | spl10_8
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_13
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_25
    | spl10_26 ),
    inference(subsumption_resolution,[],[f474,f106])).

fof(f106,plain,
    ( ~ v2_struct_0(sK0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl10_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f474,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_2
    | ~ spl10_3
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | spl10_8
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_13
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_25
    | spl10_26 ),
    inference(subsumption_resolution,[],[f473,f111])).

fof(f111,plain,
    ( v2_pre_topc(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl10_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f473,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | spl10_8
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_13
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_25
    | spl10_26 ),
    inference(subsumption_resolution,[],[f472,f116])).

fof(f116,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl10_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f472,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | spl10_8
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_13
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_25
    | spl10_26 ),
    inference(subsumption_resolution,[],[f471,f121])).

fof(f121,plain,
    ( ~ v2_struct_0(sK1)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl10_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f471,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | spl10_8
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_13
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_25
    | spl10_26 ),
    inference(subsumption_resolution,[],[f470,f126])).

fof(f126,plain,
    ( v2_pre_topc(sK1)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl10_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f470,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_6
    | spl10_7
    | spl10_8
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_13
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_25
    | spl10_26 ),
    inference(subsumption_resolution,[],[f469,f131])).

fof(f131,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl10_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f469,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl10_7
    | spl10_8
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_13
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_25
    | spl10_26 ),
    inference(subsumption_resolution,[],[f468,f141])).

fof(f141,plain,
    ( ~ v2_struct_0(sK3)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl10_8
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f468,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl10_7
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_13
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_25
    | spl10_26 ),
    inference(subsumption_resolution,[],[f467,f156])).

fof(f156,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl10_11
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f467,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl10_7
    | ~ spl10_9
    | ~ spl10_13
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_25
    | spl10_26 ),
    inference(subsumption_resolution,[],[f466,f136])).

fof(f136,plain,
    ( ~ v2_struct_0(sK2)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl10_7
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f466,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_9
    | ~ spl10_13
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_25
    | spl10_26 ),
    inference(subsumption_resolution,[],[f465,f146])).

fof(f146,plain,
    ( v1_funct_1(sK4)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl10_9
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f465,plain,
    ( ~ v1_funct_1(sK4)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_13
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_25
    | spl10_26 ),
    inference(subsumption_resolution,[],[f464,f187])).

fof(f187,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl10_17
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f464,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_13
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_25
    | spl10_26 ),
    inference(subsumption_resolution,[],[f463,f194])).

fof(f194,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl10_18
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f463,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_13
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_25
    | spl10_26 ),
    inference(subsumption_resolution,[],[f462,f176])).

fof(f176,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl10_15
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f462,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_25
    | spl10_26 ),
    inference(subsumption_resolution,[],[f461,f182])).

fof(f182,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl10_16
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f461,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_13
    | ~ spl10_25
    | spl10_26 ),
    inference(subsumption_resolution,[],[f460,f166])).

fof(f166,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl10_13
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f460,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_25
    | spl10_26 ),
    inference(subsumption_resolution,[],[f458,f242])).

fof(f242,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl10_25
  <=> r1_tmap_1(sK3,sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f458,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl10_26 ),
    inference(resolution,[],[f245,f291])).

fof(f291,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f90,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

fof(f245,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | spl10_26 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl10_26
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f456,plain,
    ( spl10_7
    | ~ spl10_16
    | ~ spl10_21
    | ~ spl10_27
    | ~ spl10_56 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | spl10_7
    | ~ spl10_16
    | ~ spl10_21
    | ~ spl10_27
    | ~ spl10_56 ),
    inference(subsumption_resolution,[],[f454,f136])).

fof(f454,plain,
    ( v2_struct_0(sK2)
    | ~ spl10_16
    | ~ spl10_21
    | ~ spl10_27
    | ~ spl10_56 ),
    inference(subsumption_resolution,[],[f453,f253])).

fof(f253,plain,
    ( v2_pre_topc(sK2)
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl10_27
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f453,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_16
    | ~ spl10_21
    | ~ spl10_56 ),
    inference(subsumption_resolution,[],[f452,f209])).

fof(f209,plain,
    ( l1_pre_topc(sK2)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl10_21
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f452,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_16
    | ~ spl10_56 ),
    inference(subsumption_resolution,[],[f449,f182])).

fof(f449,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_56 ),
    inference(resolution,[],[f446,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

fof(f446,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_connsp_2(sK2,sK5))
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl10_56
  <=> ! [X0] : ~ r2_hidden(X0,k1_connsp_2(sK2,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f447,plain,
    ( spl10_56
    | ~ spl10_55 ),
    inference(avatar_split_clause,[],[f443,f439,f445])).

fof(f439,plain,
    ( spl10_55
  <=> sP9(k1_connsp_2(sK2,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).

fof(f443,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_connsp_2(sK2,sK5))
    | ~ spl10_55 ),
    inference(resolution,[],[f441,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ sP9(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(general_splitting,[],[f87,f100_D])).

fof(f100,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP9(X1) ) ),
    inference(cnf_transformation,[],[f100_D])).

fof(f100_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP9(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f441,plain,
    ( sP9(k1_connsp_2(sK2,sK5))
    | ~ spl10_55 ),
    inference(avatar_component_clause,[],[f439])).

fof(f442,plain,
    ( spl10_55
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f437,f419,f180,f439])).

fof(f419,plain,
    ( spl10_54
  <=> ! [X1] :
        ( sP9(k1_connsp_2(sK2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f437,plain,
    ( sP9(k1_connsp_2(sK2,sK5))
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(resolution,[],[f420,f182])).

fof(f420,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | sP9(k1_connsp_2(sK2,X1)) )
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f419])).

fof(f428,plain,
    ( ~ spl10_15
    | ~ spl10_16
    | spl10_25
    | ~ spl10_26
    | ~ spl10_51 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | ~ spl10_15
    | ~ spl10_16
    | spl10_25
    | ~ spl10_26
    | ~ spl10_51 ),
    inference(subsumption_resolution,[],[f426,f246])).

fof(f246,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f244])).

fof(f426,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl10_15
    | ~ spl10_16
    | spl10_25
    | ~ spl10_51 ),
    inference(subsumption_resolution,[],[f425,f182])).

fof(f425,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl10_15
    | spl10_25
    | ~ spl10_51 ),
    inference(subsumption_resolution,[],[f423,f241])).

fof(f241,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | spl10_25 ),
    inference(avatar_component_clause,[],[f240])).

fof(f423,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl10_15
    | ~ spl10_51 ),
    inference(resolution,[],[f401,f176])).

fof(f401,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_tmap_1(sK3,sK1,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0) )
    | ~ spl10_51 ),
    inference(avatar_component_clause,[],[f400])).

fof(f400,plain,
    ( spl10_51
  <=> ! [X0] :
        ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0)
        | r1_tmap_1(sK3,sK1,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).

fof(f421,plain,
    ( spl10_54
    | spl10_7
    | ~ spl10_21
    | ~ spl10_27
    | ~ spl10_52 ),
    inference(avatar_split_clause,[],[f413,f405,f251,f207,f134,f419])).

fof(f405,plain,
    ( spl10_52
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP9(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f413,plain,
    ( ! [X1] :
        ( sP9(k1_connsp_2(sK2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK2)) )
    | spl10_7
    | ~ spl10_21
    | ~ spl10_27
    | ~ spl10_52 ),
    inference(subsumption_resolution,[],[f412,f136])).

fof(f412,plain,
    ( ! [X1] :
        ( sP9(k1_connsp_2(sK2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | v2_struct_0(sK2) )
    | ~ spl10_21
    | ~ spl10_27
    | ~ spl10_52 ),
    inference(subsumption_resolution,[],[f411,f253])).

fof(f411,plain,
    ( ! [X1] :
        ( sP9(k1_connsp_2(sK2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl10_21
    | ~ spl10_52 ),
    inference(subsumption_resolution,[],[f409,f209])).

fof(f409,plain,
    ( ! [X1] :
        ( sP9(k1_connsp_2(sK2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl10_52 ),
    inference(resolution,[],[f406,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(f406,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP9(X0) )
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f405])).

fof(f407,plain,
    ( spl10_52
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f403,f396,f405])).

fof(f396,plain,
    ( spl10_50
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f403,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP9(X0) )
    | ~ spl10_50 ),
    inference(resolution,[],[f398,f100])).

fof(f398,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f396])).

fof(f402,plain,
    ( spl10_50
    | spl10_51
    | ~ spl10_49 ),
    inference(avatar_split_clause,[],[f394,f390,f400,f396])).

fof(f390,plain,
    ( spl10_49
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK3,sK1,sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f394,plain,
    ( ! [X0] :
        ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK3,sK1,sK4,X0)
        | v1_xboole_0(u1_struct_0(sK2)) )
    | ~ spl10_49 ),
    inference(duplicate_literal_removal,[],[f393])).

fof(f393,plain,
    ( ! [X0] :
        ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK3,sK1,sK4,X0)
        | v1_xboole_0(u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl10_49 ),
    inference(resolution,[],[f391,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f391,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f390])).

fof(f392,plain,
    ( spl10_49
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_11
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f388,f382,f154,f114,f109,f104,f390])).

fof(f382,plain,
    ( spl10_48
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK3,sK1,sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f388,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_11
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f387,f106])).

fof(f387,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_11
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f386,f111])).

fof(f386,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_3
    | ~ spl10_11
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f385,f116])).

fof(f385,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_11
    | ~ spl10_48 ),
    inference(resolution,[],[f383,f156])).

fof(f383,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f382])).

fof(f384,plain,
    ( spl10_48
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_47 ),
    inference(avatar_split_clause,[],[f380,f373,f192,f185,f129,f124,f119,f382])).

fof(f373,plain,
    ( spl10_47
  <=> ! [X1,X0,X2] :
        ( ~ r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,sK3,sK2,sK4),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ r2_hidden(X2,u1_struct_0(sK2))
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK3,X0,sK4,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f380,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f379,f121])).

fof(f379,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f378,f126])).

fof(f378,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ m1_pre_topc(sK3,X1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_6
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f377,f131])).

fof(f377,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f376,f194])).

fof(f376,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK3,sK1,sK4,X0) )
    | ~ spl10_17
    | ~ spl10_47 ),
    inference(resolution,[],[f374,f187])).

fof(f374,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,sK3,sK2,sK4),X2)
        | ~ r2_hidden(X2,u1_struct_0(sK2))
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK3,X0,sK4,X2) )
    | ~ spl10_47 ),
    inference(avatar_component_clause,[],[f373])).

fof(f375,plain,
    ( spl10_47
    | ~ spl10_9
    | ~ spl10_46 ),
    inference(avatar_split_clause,[],[f371,f368,f144,f373])).

fof(f368,plain,
    ( spl10_46
  <=> ! [X1,X3,X0,X2] :
        ( ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,X1,k3_tmap_1(X2,X1,sK3,sK2,X3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(sK3,X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | r1_tmap_1(sK3,X1,X3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f371,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,sK3,sK2,sK4),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ r2_hidden(X2,u1_struct_0(sK2))
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK3,X0,sK4,X2) )
    | ~ spl10_9
    | ~ spl10_46 ),
    inference(resolution,[],[f369,f146])).

fof(f369,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(X3)
        | ~ r1_tmap_1(sK2,X1,k3_tmap_1(X2,X1,sK3,sK2,X3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ m1_pre_topc(sK3,X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | r1_tmap_1(sK3,X1,X3,X0) )
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f368])).

fof(f370,plain,
    ( spl10_46
    | spl10_7
    | spl10_8
    | ~ spl10_13
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f361,f355,f164,f139,f134,f368])).

fof(f355,plain,
    ( spl10_44
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK2))
        | sP7(sK3,sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f361,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,X1,k3_tmap_1(X2,X1,sK3,sK2,X3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(sK3,X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | r1_tmap_1(sK3,X1,X3,X0) )
    | spl10_7
    | spl10_8
    | ~ spl10_13
    | ~ spl10_44 ),
    inference(subsumption_resolution,[],[f360,f136])).

fof(f360,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,X1,k3_tmap_1(X2,X1,sK3,sK2,X3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(sK3,X2)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | r1_tmap_1(sK3,X1,X3,X0) )
    | spl10_8
    | ~ spl10_13
    | ~ spl10_44 ),
    inference(subsumption_resolution,[],[f359,f141])).

fof(f359,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,X1,k3_tmap_1(X2,X1,sK3,sK2,X3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(sK3,X2)
        | v2_struct_0(sK3)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | r1_tmap_1(sK3,X1,X3,X0) )
    | ~ spl10_13
    | ~ spl10_44 ),
    inference(subsumption_resolution,[],[f358,f166])).

fof(f358,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,X1,k3_tmap_1(X2,X1,sK3,sK2,X3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(sK3,X2)
        | v2_struct_0(sK3)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | r1_tmap_1(sK3,X1,X3,X0) )
    | ~ spl10_44 ),
    inference(resolution,[],[f356,f295])).

fof(f295,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( ~ sP7(X3,X2,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r1_tmap_1(X3,X1,X4,X7) ) ),
    inference(subsumption_resolution,[],[f97,f78])).

fof(f97,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
      | v2_struct_0(X0)
      | ~ sP7(X3,X2,X7) ) ),
    inference(general_splitting,[],[f88,f96_D])).

fof(f96,plain,(
    ! [X2,X7,X5,X3] :
      ( ~ v3_pre_topc(X5,X3)
      | ~ r2_hidden(X7,X5)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | sP7(X3,X2,X7) ) ),
    inference(cnf_transformation,[],[f96_D])).

fof(f96_D,plain,(
    ! [X7,X2,X3] :
      ( ! [X5] :
          ( ~ v3_pre_topc(X5,X3)
          | ~ r2_hidden(X7,X5)
          | ~ r1_tarski(X5,u1_struct_0(X2))
          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
    <=> ~ sP7(X3,X2,X7) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f88,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X1,X4,X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) ) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

fof(f356,plain,
    ( ! [X0] :
        ( sP7(sK3,sK2,X0)
        | ~ r2_hidden(X0,u1_struct_0(sK2)) )
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f355])).

fof(f357,plain,
    ( spl10_44
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f353,f346,f355])).

fof(f346,plain,
    ( spl10_42
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,u1_struct_0(sK2))
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X3))
        | sP7(sK3,X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f353,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK2))
        | sP7(sK3,sK2,X0) )
    | ~ spl10_42 ),
    inference(resolution,[],[f347,f94])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f347,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X3))
        | ~ r2_hidden(X2,u1_struct_0(sK2))
        | sP7(sK3,X3,X2) )
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f346])).

fof(f348,plain,
    ( spl10_42
    | ~ spl10_32
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f344,f322,f287,f346])).

fof(f287,plain,
    ( spl10_32
  <=> v3_pre_topc(u1_struct_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f322,plain,
    ( spl10_38
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f344,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,u1_struct_0(sK2))
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X3))
        | sP7(sK3,X3,X2) )
    | ~ spl10_32
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f294,f323])).

fof(f323,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f322])).

fof(f294,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,u1_struct_0(sK2))
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X3))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
        | sP7(sK3,X3,X2) )
    | ~ spl10_32 ),
    inference(resolution,[],[f289,f96])).

fof(f289,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f287])).

fof(f334,plain,
    ( ~ spl10_13
    | ~ spl10_22
    | spl10_38 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl10_13
    | ~ spl10_22
    | spl10_38 ),
    inference(subsumption_resolution,[],[f332,f218])).

fof(f218,plain,
    ( l1_pre_topc(sK3)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl10_22
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f332,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl10_13
    | spl10_38 ),
    inference(subsumption_resolution,[],[f330,f166])).

fof(f330,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | spl10_38 ),
    inference(resolution,[],[f324,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f324,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl10_38 ),
    inference(avatar_component_clause,[],[f322])).

fof(f290,plain,
    ( spl10_32
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f285,f257,f216,f164,f159,f287])).

fof(f159,plain,
    ( spl10_12
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f257,plain,
    ( spl10_28
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f285,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f284,f259])).

fof(f259,plain,
    ( v2_pre_topc(sK3)
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f257])).

fof(f284,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f283,f218])).

fof(f283,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_12
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f282,f166])).

fof(f282,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_12 ),
    inference(resolution,[],[f277,f161])).

fof(f161,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f159])).

fof(f277,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f102,f72])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f261,plain,
    ( ~ spl10_25
    | ~ spl10_14
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f255,f244,f169,f240])).

fof(f169,plain,
    ( spl10_14
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f255,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl10_14
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f234,f246])).

fof(f234,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl10_14 ),
    inference(forward_demodulation,[],[f70,f171])).

fof(f171,plain,
    ( sK5 = sK6
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f70,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
      | ~ r1_tmap_1(sK3,sK1,sK4,sK5) )
    & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
      | r1_tmap_1(sK3,sK1,sK4,sK5) )
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_pre_topc(sK2,sK3)
    & v1_tsep_1(sK2,sK3)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f37,f44,f43,f42,f41,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | r1_tmap_1(X3,X1,X4,X5) )
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & v1_tsep_1(X2,X3)
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
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,X1,X4,X5) )
                            & ( r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                              | r1_tmap_1(X3,X1,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & v1_tsep_1(X2,X3)
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
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,sK1,X4,X5) )
                          & ( r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6)
                            | r1_tmap_1(X3,sK1,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & v1_tsep_1(X2,X3)
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

fof(f40,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6)
                          | ~ r1_tmap_1(X3,sK1,X4,X5) )
                        & ( r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6)
                          | r1_tmap_1(X3,sK1,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(X2,X3)
                & v1_tsep_1(X2,X3)
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
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6)
                        | ~ r1_tmap_1(X3,sK1,X4,X5) )
                      & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6)
                        | r1_tmap_1(X3,sK1,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(sK2,X3)
              & v1_tsep_1(sK2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6)
                      | ~ r1_tmap_1(X3,sK1,X4,X5) )
                    & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6)
                      | r1_tmap_1(X3,sK1,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK2)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_pre_topc(sK2,X3)
            & v1_tsep_1(sK2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6)
                    | ~ r1_tmap_1(sK3,sK1,X4,X5) )
                  & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6)
                    | r1_tmap_1(sK3,sK1,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK2)) )
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & m1_pre_topc(sK2,sK3)
          & v1_tsep_1(sK2,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6)
                  | ~ r1_tmap_1(sK3,sK1,X4,X5) )
                & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6)
                  | r1_tmap_1(sK3,sK1,X4,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK2)) )
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & m1_pre_topc(sK2,sK3)
        & v1_tsep_1(sK2,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
                | ~ r1_tmap_1(sK3,sK1,sK4,X5) )
              & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
                | r1_tmap_1(sK3,sK1,sK4,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK2)) )
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & m1_pre_topc(sK2,sK3)
      & v1_tsep_1(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
              | ~ r1_tmap_1(sK3,sK1,sK4,X5) )
            & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
              | r1_tmap_1(sK3,sK1,sK4,X5) )
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK2)) )
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( ? [X6] :
          ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
            | ~ r1_tmap_1(sK3,sK1,sK4,sK5) )
          & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
            | r1_tmap_1(sK3,sK1,sK4,sK5) )
          & sK5 = X6
          & m1_subset_1(X6,u1_struct_0(sK2)) )
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X6] :
        ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
          | ~ r1_tmap_1(sK3,sK1,sK4,sK5) )
        & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
          | r1_tmap_1(sK3,sK1,sK4,sK5) )
        & sK5 = X6
        & m1_subset_1(X6,u1_struct_0(sK2)) )
   => ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
        | ~ r1_tmap_1(sK3,sK1,sK4,sK5) )
      & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
        | r1_tmap_1(sK3,sK1,sK4,sK5) )
      & sK5 = sK6
      & m1_subset_1(sK6,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
                       => ( ( m1_pre_topc(X2,X3)
                            & v1_tsep_1(X2,X3) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X1,X4,X5)
                                    <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f260,plain,
    ( spl10_28
    | ~ spl10_11
    | ~ spl10_23 ),
    inference(avatar_split_clause,[],[f249,f231,f154,f257])).

fof(f231,plain,
    ( spl10_23
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f249,plain,
    ( v2_pre_topc(sK3)
    | ~ spl10_11
    | ~ spl10_23 ),
    inference(resolution,[],[f232,f156])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_pre_topc(X0) )
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f231])).

fof(f254,plain,
    ( spl10_27
    | ~ spl10_10
    | ~ spl10_23 ),
    inference(avatar_split_clause,[],[f248,f231,f149,f251])).

fof(f149,plain,
    ( spl10_10
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f248,plain,
    ( v2_pre_topc(sK2)
    | ~ spl10_10
    | ~ spl10_23 ),
    inference(resolution,[],[f232,f151])).

fof(f151,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f149])).

fof(f247,plain,
    ( spl10_25
    | spl10_26
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f229,f169,f244,f240])).

fof(f229,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl10_14 ),
    inference(forward_demodulation,[],[f69,f171])).

fof(f69,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f233,plain,
    ( spl10_23
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f213,f114,f109,f231])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_pre_topc(X0) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f211,f111])).

fof(f211,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_pre_topc(X0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl10_3 ),
    inference(resolution,[],[f77,f116])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f219,plain,
    ( spl10_22
    | ~ spl10_11
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f205,f197,f154,f216])).

fof(f197,plain,
    ( spl10_19
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f205,plain,
    ( l1_pre_topc(sK3)
    | ~ spl10_11
    | ~ spl10_19 ),
    inference(resolution,[],[f198,f156])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f197])).

fof(f210,plain,
    ( spl10_21
    | ~ spl10_10
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f204,f197,f149,f207])).

fof(f204,plain,
    ( l1_pre_topc(sK2)
    | ~ spl10_10
    | ~ spl10_19 ),
    inference(resolution,[],[f198,f151])).

fof(f199,plain,
    ( spl10_19
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f189,f114,f197])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl10_3 ),
    inference(resolution,[],[f71,f116])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
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

fof(f195,plain,(
    spl10_18 ),
    inference(avatar_split_clause,[],[f63,f192])).

fof(f63,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f188,plain,(
    spl10_17 ),
    inference(avatar_split_clause,[],[f62,f185])).

fof(f62,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f183,plain,
    ( spl10_16
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f178,f169,f180])).

fof(f178,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl10_14 ),
    inference(forward_demodulation,[],[f67,f171])).

fof(f67,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f177,plain,(
    spl10_15 ),
    inference(avatar_split_clause,[],[f66,f174])).

fof(f66,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f172,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f68,f169])).

fof(f68,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f45])).

fof(f167,plain,(
    spl10_13 ),
    inference(avatar_split_clause,[],[f65,f164])).

fof(f65,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f162,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f64,f159])).

fof(f64,plain,(
    v1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f157,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f60,f154])).

fof(f60,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f152,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f58,f149])).

fof(f58,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f147,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f61,f144])).

fof(f61,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f142,plain,(
    ~ spl10_8 ),
    inference(avatar_split_clause,[],[f59,f139])).

fof(f59,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f137,plain,(
    ~ spl10_7 ),
    inference(avatar_split_clause,[],[f57,f134])).

fof(f57,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f132,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f56,f129])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f127,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f55,f124])).

fof(f55,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f122,plain,(
    ~ spl10_4 ),
    inference(avatar_split_clause,[],[f54,f119])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f117,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f53,f114])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f112,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f52,f109])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f107,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f51,f104])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n003.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:57:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (13728)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (13726)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (13725)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (13727)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (13739)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (13744)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (13742)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (13745)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (13749)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (13731)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (13735)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (13724)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (13726)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (13748)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (13733)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (13747)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (13729)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (13740)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (13731)Refutation not found, incomplete strategy% (13731)------------------------------
% 0.21/0.52  % (13731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13743)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (13731)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  % (13736)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  
% 0.21/0.52  % (13731)Memory used [KB]: 1791
% 0.21/0.52  % (13731)Time elapsed: 0.069 s
% 0.21/0.52  % (13731)------------------------------
% 0.21/0.52  % (13731)------------------------------
% 0.21/0.52  % (13725)Refutation not found, incomplete strategy% (13725)------------------------------
% 0.21/0.52  % (13725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13725)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13725)Memory used [KB]: 10746
% 0.21/0.53  % (13725)Time elapsed: 0.104 s
% 0.21/0.53  % (13725)------------------------------
% 0.21/0.53  % (13725)------------------------------
% 0.21/0.53  % (13737)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.32/0.54  % (13734)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.32/0.54  % (13724)Refutation not found, incomplete strategy% (13724)------------------------------
% 1.32/0.54  % (13724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (13724)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (13724)Memory used [KB]: 10746
% 1.32/0.54  % (13724)Time elapsed: 0.124 s
% 1.32/0.54  % (13724)------------------------------
% 1.32/0.54  % (13724)------------------------------
% 1.32/0.54  % (13741)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.32/0.54  % SZS output start Proof for theBenchmark
% 1.32/0.54  fof(f477,plain,(
% 1.32/0.54    $false),
% 1.32/0.54    inference(avatar_sat_refutation,[],[f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f162,f167,f172,f177,f183,f188,f195,f199,f210,f219,f233,f247,f254,f260,f261,f290,f334,f348,f357,f370,f375,f384,f392,f402,f407,f421,f428,f442,f447,f456,f476])).
% 1.32/0.54  fof(f476,plain,(
% 1.32/0.54    spl10_1 | ~spl10_2 | ~spl10_3 | spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | spl10_8 | ~spl10_9 | ~spl10_11 | ~spl10_13 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_25 | spl10_26),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f475])).
% 1.32/0.54  fof(f475,plain,(
% 1.32/0.54    $false | (spl10_1 | ~spl10_2 | ~spl10_3 | spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | spl10_8 | ~spl10_9 | ~spl10_11 | ~spl10_13 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_25 | spl10_26)),
% 1.32/0.54    inference(subsumption_resolution,[],[f474,f106])).
% 1.32/0.54  fof(f106,plain,(
% 1.32/0.54    ~v2_struct_0(sK0) | spl10_1),
% 1.32/0.54    inference(avatar_component_clause,[],[f104])).
% 1.32/0.54  fof(f104,plain,(
% 1.32/0.54    spl10_1 <=> v2_struct_0(sK0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.32/0.54  fof(f474,plain,(
% 1.32/0.54    v2_struct_0(sK0) | (~spl10_2 | ~spl10_3 | spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | spl10_8 | ~spl10_9 | ~spl10_11 | ~spl10_13 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_25 | spl10_26)),
% 1.32/0.54    inference(subsumption_resolution,[],[f473,f111])).
% 1.32/0.54  fof(f111,plain,(
% 1.32/0.54    v2_pre_topc(sK0) | ~spl10_2),
% 1.32/0.54    inference(avatar_component_clause,[],[f109])).
% 1.32/0.54  fof(f109,plain,(
% 1.32/0.54    spl10_2 <=> v2_pre_topc(sK0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.32/0.54  fof(f473,plain,(
% 1.32/0.54    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_3 | spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | spl10_8 | ~spl10_9 | ~spl10_11 | ~spl10_13 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_25 | spl10_26)),
% 1.32/0.54    inference(subsumption_resolution,[],[f472,f116])).
% 1.32/0.54  fof(f116,plain,(
% 1.32/0.54    l1_pre_topc(sK0) | ~spl10_3),
% 1.32/0.54    inference(avatar_component_clause,[],[f114])).
% 1.32/0.54  fof(f114,plain,(
% 1.32/0.54    spl10_3 <=> l1_pre_topc(sK0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.32/0.54  fof(f472,plain,(
% 1.32/0.54    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | spl10_8 | ~spl10_9 | ~spl10_11 | ~spl10_13 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_25 | spl10_26)),
% 1.32/0.54    inference(subsumption_resolution,[],[f471,f121])).
% 1.32/0.54  fof(f121,plain,(
% 1.32/0.54    ~v2_struct_0(sK1) | spl10_4),
% 1.32/0.54    inference(avatar_component_clause,[],[f119])).
% 1.32/0.54  fof(f119,plain,(
% 1.32/0.54    spl10_4 <=> v2_struct_0(sK1)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.32/0.54  fof(f471,plain,(
% 1.32/0.54    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_5 | ~spl10_6 | spl10_7 | spl10_8 | ~spl10_9 | ~spl10_11 | ~spl10_13 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_25 | spl10_26)),
% 1.32/0.54    inference(subsumption_resolution,[],[f470,f126])).
% 1.32/0.54  fof(f126,plain,(
% 1.32/0.54    v2_pre_topc(sK1) | ~spl10_5),
% 1.32/0.54    inference(avatar_component_clause,[],[f124])).
% 1.32/0.54  fof(f124,plain,(
% 1.32/0.54    spl10_5 <=> v2_pre_topc(sK1)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.32/0.54  fof(f470,plain,(
% 1.32/0.54    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_6 | spl10_7 | spl10_8 | ~spl10_9 | ~spl10_11 | ~spl10_13 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_25 | spl10_26)),
% 1.32/0.54    inference(subsumption_resolution,[],[f469,f131])).
% 1.32/0.54  fof(f131,plain,(
% 1.32/0.54    l1_pre_topc(sK1) | ~spl10_6),
% 1.32/0.54    inference(avatar_component_clause,[],[f129])).
% 1.32/0.54  fof(f129,plain,(
% 1.32/0.54    spl10_6 <=> l1_pre_topc(sK1)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.32/0.54  fof(f469,plain,(
% 1.32/0.54    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl10_7 | spl10_8 | ~spl10_9 | ~spl10_11 | ~spl10_13 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_25 | spl10_26)),
% 1.32/0.54    inference(subsumption_resolution,[],[f468,f141])).
% 1.32/0.54  fof(f141,plain,(
% 1.32/0.54    ~v2_struct_0(sK3) | spl10_8),
% 1.32/0.54    inference(avatar_component_clause,[],[f139])).
% 1.32/0.54  fof(f139,plain,(
% 1.32/0.54    spl10_8 <=> v2_struct_0(sK3)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 1.32/0.54  fof(f468,plain,(
% 1.32/0.54    v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl10_7 | ~spl10_9 | ~spl10_11 | ~spl10_13 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_25 | spl10_26)),
% 1.32/0.54    inference(subsumption_resolution,[],[f467,f156])).
% 1.32/0.54  fof(f156,plain,(
% 1.32/0.54    m1_pre_topc(sK3,sK0) | ~spl10_11),
% 1.32/0.54    inference(avatar_component_clause,[],[f154])).
% 1.32/0.54  fof(f154,plain,(
% 1.32/0.54    spl10_11 <=> m1_pre_topc(sK3,sK0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 1.32/0.54  fof(f467,plain,(
% 1.32/0.54    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl10_7 | ~spl10_9 | ~spl10_13 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_25 | spl10_26)),
% 1.32/0.54    inference(subsumption_resolution,[],[f466,f136])).
% 1.32/0.54  fof(f136,plain,(
% 1.32/0.54    ~v2_struct_0(sK2) | spl10_7),
% 1.32/0.54    inference(avatar_component_clause,[],[f134])).
% 1.32/0.54  fof(f134,plain,(
% 1.32/0.54    spl10_7 <=> v2_struct_0(sK2)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 1.32/0.54  fof(f466,plain,(
% 1.32/0.54    v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_9 | ~spl10_13 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_25 | spl10_26)),
% 1.32/0.54    inference(subsumption_resolution,[],[f465,f146])).
% 1.32/0.54  fof(f146,plain,(
% 1.32/0.54    v1_funct_1(sK4) | ~spl10_9),
% 1.32/0.54    inference(avatar_component_clause,[],[f144])).
% 1.32/0.54  fof(f144,plain,(
% 1.32/0.54    spl10_9 <=> v1_funct_1(sK4)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 1.32/0.54  fof(f465,plain,(
% 1.32/0.54    ~v1_funct_1(sK4) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_13 | ~spl10_15 | ~spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_25 | spl10_26)),
% 1.32/0.54    inference(subsumption_resolution,[],[f464,f187])).
% 1.32/0.54  fof(f187,plain,(
% 1.32/0.54    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl10_17),
% 1.32/0.54    inference(avatar_component_clause,[],[f185])).
% 1.32/0.54  fof(f185,plain,(
% 1.32/0.54    spl10_17 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 1.32/0.54  fof(f464,plain,(
% 1.32/0.54    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_13 | ~spl10_15 | ~spl10_16 | ~spl10_18 | ~spl10_25 | spl10_26)),
% 1.32/0.54    inference(subsumption_resolution,[],[f463,f194])).
% 1.32/0.54  fof(f194,plain,(
% 1.32/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl10_18),
% 1.32/0.54    inference(avatar_component_clause,[],[f192])).
% 1.32/0.54  fof(f192,plain,(
% 1.32/0.54    spl10_18 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 1.32/0.54  fof(f463,plain,(
% 1.32/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_13 | ~spl10_15 | ~spl10_16 | ~spl10_25 | spl10_26)),
% 1.32/0.54    inference(subsumption_resolution,[],[f462,f176])).
% 1.32/0.54  fof(f176,plain,(
% 1.32/0.54    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl10_15),
% 1.32/0.54    inference(avatar_component_clause,[],[f174])).
% 1.32/0.54  fof(f174,plain,(
% 1.32/0.54    spl10_15 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 1.32/0.54  fof(f462,plain,(
% 1.32/0.54    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_13 | ~spl10_16 | ~spl10_25 | spl10_26)),
% 1.32/0.54    inference(subsumption_resolution,[],[f461,f182])).
% 1.32/0.54  fof(f182,plain,(
% 1.32/0.54    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl10_16),
% 1.32/0.54    inference(avatar_component_clause,[],[f180])).
% 1.32/0.54  fof(f180,plain,(
% 1.32/0.54    spl10_16 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 1.32/0.54  fof(f461,plain,(
% 1.32/0.54    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_13 | ~spl10_25 | spl10_26)),
% 1.32/0.54    inference(subsumption_resolution,[],[f460,f166])).
% 1.32/0.54  fof(f166,plain,(
% 1.32/0.54    m1_pre_topc(sK2,sK3) | ~spl10_13),
% 1.32/0.54    inference(avatar_component_clause,[],[f164])).
% 1.32/0.54  fof(f164,plain,(
% 1.32/0.54    spl10_13 <=> m1_pre_topc(sK2,sK3)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 1.32/0.54  fof(f460,plain,(
% 1.32/0.54    ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl10_25 | spl10_26)),
% 1.32/0.54    inference(subsumption_resolution,[],[f458,f242])).
% 1.32/0.54  fof(f242,plain,(
% 1.32/0.54    r1_tmap_1(sK3,sK1,sK4,sK5) | ~spl10_25),
% 1.32/0.54    inference(avatar_component_clause,[],[f240])).
% 1.32/0.54  fof(f240,plain,(
% 1.32/0.54    spl10_25 <=> r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 1.32/0.54  fof(f458,plain,(
% 1.32/0.54    ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl10_26),
% 1.32/0.54    inference(resolution,[],[f245,f291])).
% 1.32/0.54  fof(f291,plain,(
% 1.32/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f90,f78])).
% 1.32/0.54  fof(f78,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_pre_topc(X2,X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f28])).
% 1.32/0.54  fof(f28,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.32/0.54    inference(flattening,[],[f27])).
% 1.32/0.54  fof(f27,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f10])).
% 1.32/0.54  fof(f10,axiom,(
% 1.32/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.32/0.54  fof(f90,plain,(
% 1.32/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.54    inference(equality_resolution,[],[f76])).
% 1.32/0.54  fof(f76,plain,(
% 1.32/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f24])).
% 1.32/0.54  fof(f24,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.54    inference(flattening,[],[f23])).
% 1.32/0.54  fof(f23,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f11])).
% 1.32/0.54  fof(f11,axiom,(
% 1.32/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).
% 1.32/0.54  fof(f245,plain,(
% 1.32/0.54    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | spl10_26),
% 1.32/0.54    inference(avatar_component_clause,[],[f244])).
% 1.32/0.54  fof(f244,plain,(
% 1.32/0.54    spl10_26 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 1.32/0.54  fof(f456,plain,(
% 1.32/0.54    spl10_7 | ~spl10_16 | ~spl10_21 | ~spl10_27 | ~spl10_56),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f455])).
% 1.32/0.54  fof(f455,plain,(
% 1.32/0.54    $false | (spl10_7 | ~spl10_16 | ~spl10_21 | ~spl10_27 | ~spl10_56)),
% 1.32/0.54    inference(subsumption_resolution,[],[f454,f136])).
% 1.32/0.54  fof(f454,plain,(
% 1.32/0.54    v2_struct_0(sK2) | (~spl10_16 | ~spl10_21 | ~spl10_27 | ~spl10_56)),
% 1.32/0.54    inference(subsumption_resolution,[],[f453,f253])).
% 1.32/0.54  fof(f253,plain,(
% 1.32/0.54    v2_pre_topc(sK2) | ~spl10_27),
% 1.32/0.54    inference(avatar_component_clause,[],[f251])).
% 1.32/0.54  fof(f251,plain,(
% 1.32/0.54    spl10_27 <=> v2_pre_topc(sK2)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 1.32/0.54  fof(f453,plain,(
% 1.32/0.54    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_16 | ~spl10_21 | ~spl10_56)),
% 1.32/0.54    inference(subsumption_resolution,[],[f452,f209])).
% 1.32/0.54  fof(f209,plain,(
% 1.32/0.54    l1_pre_topc(sK2) | ~spl10_21),
% 1.32/0.54    inference(avatar_component_clause,[],[f207])).
% 1.32/0.54  fof(f207,plain,(
% 1.32/0.54    spl10_21 <=> l1_pre_topc(sK2)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 1.32/0.54  fof(f452,plain,(
% 1.32/0.54    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_16 | ~spl10_56)),
% 1.32/0.54    inference(subsumption_resolution,[],[f449,f182])).
% 1.32/0.54  fof(f449,plain,(
% 1.32/0.54    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~spl10_56),
% 1.32/0.54    inference(resolution,[],[f446,f73])).
% 1.32/0.54  fof(f73,plain,(
% 1.32/0.54    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f20])).
% 1.32/0.54  fof(f20,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.54    inference(flattening,[],[f19])).
% 1.32/0.54  fof(f19,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f7])).
% 1.32/0.54  fof(f7,axiom,(
% 1.32/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).
% 1.32/0.54  fof(f446,plain,(
% 1.32/0.54    ( ! [X0] : (~r2_hidden(X0,k1_connsp_2(sK2,sK5))) ) | ~spl10_56),
% 1.32/0.54    inference(avatar_component_clause,[],[f445])).
% 1.32/0.54  fof(f445,plain,(
% 1.32/0.54    spl10_56 <=> ! [X0] : ~r2_hidden(X0,k1_connsp_2(sK2,sK5))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).
% 1.32/0.54  fof(f447,plain,(
% 1.32/0.54    spl10_56 | ~spl10_55),
% 1.32/0.54    inference(avatar_split_clause,[],[f443,f439,f445])).
% 1.32/0.54  fof(f439,plain,(
% 1.32/0.54    spl10_55 <=> sP9(k1_connsp_2(sK2,sK5))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).
% 1.32/0.54  fof(f443,plain,(
% 1.32/0.54    ( ! [X0] : (~r2_hidden(X0,k1_connsp_2(sK2,sK5))) ) | ~spl10_55),
% 1.32/0.54    inference(resolution,[],[f441,f101])).
% 1.32/0.54  fof(f101,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~sP9(X1) | ~r2_hidden(X0,X1)) )),
% 1.32/0.54    inference(general_splitting,[],[f87,f100_D])).
% 1.32/0.54  fof(f100,plain,(
% 1.32/0.54    ( ! [X2,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP9(X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f100_D])).
% 1.32/0.54  fof(f100_D,plain,(
% 1.32/0.54    ( ! [X1] : (( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) ) <=> ~sP9(X1)) )),
% 1.32/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 1.32/0.54  fof(f87,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f35])).
% 1.32/0.54  fof(f35,plain,(
% 1.32/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.32/0.54    inference(ennf_transformation,[],[f3])).
% 1.32/0.54  fof(f3,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.32/0.54  fof(f441,plain,(
% 1.32/0.54    sP9(k1_connsp_2(sK2,sK5)) | ~spl10_55),
% 1.32/0.54    inference(avatar_component_clause,[],[f439])).
% 1.32/0.54  fof(f442,plain,(
% 1.32/0.54    spl10_55 | ~spl10_16 | ~spl10_54),
% 1.32/0.54    inference(avatar_split_clause,[],[f437,f419,f180,f439])).
% 1.32/0.54  fof(f419,plain,(
% 1.32/0.54    spl10_54 <=> ! [X1] : (sP9(k1_connsp_2(sK2,X1)) | ~m1_subset_1(X1,u1_struct_0(sK2)))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).
% 1.32/0.54  fof(f437,plain,(
% 1.32/0.54    sP9(k1_connsp_2(sK2,sK5)) | (~spl10_16 | ~spl10_54)),
% 1.32/0.54    inference(resolution,[],[f420,f182])).
% 1.32/0.54  fof(f420,plain,(
% 1.32/0.54    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK2)) | sP9(k1_connsp_2(sK2,X1))) ) | ~spl10_54),
% 1.32/0.54    inference(avatar_component_clause,[],[f419])).
% 1.32/0.54  fof(f428,plain,(
% 1.32/0.54    ~spl10_15 | ~spl10_16 | spl10_25 | ~spl10_26 | ~spl10_51),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f427])).
% 1.32/0.54  fof(f427,plain,(
% 1.32/0.54    $false | (~spl10_15 | ~spl10_16 | spl10_25 | ~spl10_26 | ~spl10_51)),
% 1.32/0.54    inference(subsumption_resolution,[],[f426,f246])).
% 1.32/0.54  fof(f246,plain,(
% 1.32/0.54    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~spl10_26),
% 1.32/0.54    inference(avatar_component_clause,[],[f244])).
% 1.32/0.54  fof(f426,plain,(
% 1.32/0.54    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | (~spl10_15 | ~spl10_16 | spl10_25 | ~spl10_51)),
% 1.32/0.54    inference(subsumption_resolution,[],[f425,f182])).
% 1.32/0.54  fof(f425,plain,(
% 1.32/0.54    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | (~spl10_15 | spl10_25 | ~spl10_51)),
% 1.32/0.54    inference(subsumption_resolution,[],[f423,f241])).
% 1.32/0.54  fof(f241,plain,(
% 1.32/0.54    ~r1_tmap_1(sK3,sK1,sK4,sK5) | spl10_25),
% 1.32/0.54    inference(avatar_component_clause,[],[f240])).
% 1.32/0.54  fof(f423,plain,(
% 1.32/0.54    r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | (~spl10_15 | ~spl10_51)),
% 1.32/0.54    inference(resolution,[],[f401,f176])).
% 1.32/0.54  fof(f401,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | r1_tmap_1(sK3,sK1,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0)) ) | ~spl10_51),
% 1.32/0.54    inference(avatar_component_clause,[],[f400])).
% 1.32/0.54  fof(f400,plain,(
% 1.32/0.54    spl10_51 <=> ! [X0] : (~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0) | r1_tmap_1(sK3,sK1,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK3)))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).
% 1.32/0.54  fof(f421,plain,(
% 1.32/0.54    spl10_54 | spl10_7 | ~spl10_21 | ~spl10_27 | ~spl10_52),
% 1.32/0.54    inference(avatar_split_clause,[],[f413,f405,f251,f207,f134,f419])).
% 1.32/0.54  fof(f405,plain,(
% 1.32/0.54    spl10_52 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP9(X0))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).
% 1.32/0.54  fof(f413,plain,(
% 1.32/0.54    ( ! [X1] : (sP9(k1_connsp_2(sK2,X1)) | ~m1_subset_1(X1,u1_struct_0(sK2))) ) | (spl10_7 | ~spl10_21 | ~spl10_27 | ~spl10_52)),
% 1.32/0.54    inference(subsumption_resolution,[],[f412,f136])).
% 1.32/0.54  fof(f412,plain,(
% 1.32/0.54    ( ! [X1] : (sP9(k1_connsp_2(sK2,X1)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | v2_struct_0(sK2)) ) | (~spl10_21 | ~spl10_27 | ~spl10_52)),
% 1.32/0.54    inference(subsumption_resolution,[],[f411,f253])).
% 1.32/0.54  fof(f411,plain,(
% 1.32/0.54    ( ! [X1] : (sP9(k1_connsp_2(sK2,X1)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl10_21 | ~spl10_52)),
% 1.32/0.54    inference(subsumption_resolution,[],[f409,f209])).
% 1.32/0.54  fof(f409,plain,(
% 1.32/0.54    ( ! [X1] : (sP9(k1_connsp_2(sK2,X1)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl10_52),
% 1.32/0.54    inference(resolution,[],[f406,f83])).
% 1.32/0.54  fof(f83,plain,(
% 1.32/0.54    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f34])).
% 1.32/0.54  fof(f34,plain,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.54    inference(flattening,[],[f33])).
% 1.32/0.54  fof(f33,plain,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f6])).
% 1.32/0.54  fof(f6,axiom,(
% 1.32/0.54    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).
% 1.32/0.54  fof(f406,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP9(X0)) ) | ~spl10_52),
% 1.32/0.54    inference(avatar_component_clause,[],[f405])).
% 1.32/0.54  fof(f407,plain,(
% 1.32/0.54    spl10_52 | ~spl10_50),
% 1.32/0.54    inference(avatar_split_clause,[],[f403,f396,f405])).
% 1.32/0.54  fof(f396,plain,(
% 1.32/0.54    spl10_50 <=> v1_xboole_0(u1_struct_0(sK2))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).
% 1.32/0.54  fof(f403,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP9(X0)) ) | ~spl10_50),
% 1.32/0.54    inference(resolution,[],[f398,f100])).
% 1.32/0.54  fof(f398,plain,(
% 1.32/0.54    v1_xboole_0(u1_struct_0(sK2)) | ~spl10_50),
% 1.32/0.54    inference(avatar_component_clause,[],[f396])).
% 1.32/0.54  fof(f402,plain,(
% 1.32/0.54    spl10_50 | spl10_51 | ~spl10_49),
% 1.32/0.54    inference(avatar_split_clause,[],[f394,f390,f400,f396])).
% 1.32/0.54  fof(f390,plain,(
% 1.32/0.54    spl10_49 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0) | ~r2_hidden(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK1,sK4,X0))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).
% 1.32/0.54  fof(f394,plain,(
% 1.32/0.54    ( ! [X0] : (~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK1,sK4,X0) | v1_xboole_0(u1_struct_0(sK2))) ) | ~spl10_49),
% 1.32/0.54    inference(duplicate_literal_removal,[],[f393])).
% 1.32/0.54  fof(f393,plain,(
% 1.32/0.54    ( ! [X0] : (~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK1,sK4,X0) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2))) ) | ~spl10_49),
% 1.32/0.54    inference(resolution,[],[f391,f82])).
% 1.32/0.54  fof(f82,plain,(
% 1.32/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f32])).
% 1.32/0.54  fof(f32,plain,(
% 1.32/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.32/0.54    inference(flattening,[],[f31])).
% 1.32/0.54  fof(f31,plain,(
% 1.32/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.32/0.54    inference(ennf_transformation,[],[f2])).
% 1.32/0.54  fof(f2,axiom,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.32/0.54  fof(f391,plain,(
% 1.32/0.54    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | ~spl10_49),
% 1.32/0.54    inference(avatar_component_clause,[],[f390])).
% 1.32/0.54  fof(f392,plain,(
% 1.32/0.54    spl10_49 | spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_11 | ~spl10_48),
% 1.32/0.54    inference(avatar_split_clause,[],[f388,f382,f154,f114,f109,f104,f390])).
% 1.32/0.54  fof(f382,plain,(
% 1.32/0.54    spl10_48 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),X0) | ~r2_hidden(X0,u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK3,sK1,sK4,X0))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).
% 1.32/0.54  fof(f388,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0) | ~r2_hidden(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_11 | ~spl10_48)),
% 1.32/0.54    inference(subsumption_resolution,[],[f387,f106])).
% 1.32/0.54  fof(f387,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0) | ~r2_hidden(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (~spl10_2 | ~spl10_3 | ~spl10_11 | ~spl10_48)),
% 1.32/0.54    inference(subsumption_resolution,[],[f386,f111])).
% 1.32/0.54  fof(f386,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0) | ~r2_hidden(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (~spl10_3 | ~spl10_11 | ~spl10_48)),
% 1.32/0.54    inference(subsumption_resolution,[],[f385,f116])).
% 1.32/0.54  fof(f385,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0) | ~r2_hidden(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (~spl10_11 | ~spl10_48)),
% 1.32/0.54    inference(resolution,[],[f383,f156])).
% 1.32/0.54  fof(f383,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_pre_topc(sK3,X1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),X0) | ~r2_hidden(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | ~spl10_48),
% 1.32/0.54    inference(avatar_component_clause,[],[f382])).
% 1.32/0.54  fof(f384,plain,(
% 1.32/0.54    spl10_48 | spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_17 | ~spl10_18 | ~spl10_47),
% 1.32/0.54    inference(avatar_split_clause,[],[f380,f373,f192,f185,f129,f124,f119,f382])).
% 1.32/0.54  fof(f373,plain,(
% 1.32/0.54    spl10_47 <=> ! [X1,X0,X2] : (~r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,sK3,sK2,sK4),X2) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK3,X0,sK4,X2))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).
% 1.32/0.54  fof(f380,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),X0) | ~r2_hidden(X0,u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_17 | ~spl10_18 | ~spl10_47)),
% 1.32/0.54    inference(subsumption_resolution,[],[f379,f121])).
% 1.32/0.54  fof(f379,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),X0) | ~r2_hidden(X0,u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (~spl10_5 | ~spl10_6 | ~spl10_17 | ~spl10_18 | ~spl10_47)),
% 1.32/0.54    inference(subsumption_resolution,[],[f378,f126])).
% 1.32/0.54  fof(f378,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),X0) | ~r2_hidden(X0,u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (~spl10_6 | ~spl10_17 | ~spl10_18 | ~spl10_47)),
% 1.32/0.54    inference(subsumption_resolution,[],[f377,f131])).
% 1.32/0.54  fof(f377,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),X0) | ~r2_hidden(X0,u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (~spl10_17 | ~spl10_18 | ~spl10_47)),
% 1.32/0.54    inference(subsumption_resolution,[],[f376,f194])).
% 1.32/0.54  fof(f376,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),X0) | ~r2_hidden(X0,u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK3,sK1,sK4,X0)) ) | (~spl10_17 | ~spl10_47)),
% 1.32/0.54    inference(resolution,[],[f374,f187])).
% 1.32/0.54  fof(f374,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,sK3,sK2,sK4),X2) | ~r2_hidden(X2,u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK3,X0,sK4,X2)) ) | ~spl10_47),
% 1.32/0.54    inference(avatar_component_clause,[],[f373])).
% 1.32/0.54  fof(f375,plain,(
% 1.32/0.54    spl10_47 | ~spl10_9 | ~spl10_46),
% 1.32/0.54    inference(avatar_split_clause,[],[f371,f368,f144,f373])).
% 1.32/0.54  fof(f368,plain,(
% 1.32/0.54    spl10_46 <=> ! [X1,X3,X0,X2] : (~r2_hidden(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,X1,k3_tmap_1(X2,X1,sK3,sK2,X3),X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK3,X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | r1_tmap_1(sK3,X1,X3,X0))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).
% 1.32/0.54  fof(f371,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,sK3,sK2,sK4),X2) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK3,X0,sK4,X2)) ) | (~spl10_9 | ~spl10_46)),
% 1.32/0.54    inference(resolution,[],[f369,f146])).
% 1.32/0.55  fof(f369,plain,(
% 1.32/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~r1_tmap_1(sK2,X1,k3_tmap_1(X2,X1,sK3,sK2,X3),X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~r2_hidden(X0,u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | r1_tmap_1(sK3,X1,X3,X0)) ) | ~spl10_46),
% 1.32/0.55    inference(avatar_component_clause,[],[f368])).
% 1.32/0.55  fof(f370,plain,(
% 1.32/0.55    spl10_46 | spl10_7 | spl10_8 | ~spl10_13 | ~spl10_44),
% 1.32/0.55    inference(avatar_split_clause,[],[f361,f355,f164,f139,f134,f368])).
% 1.32/0.55  fof(f355,plain,(
% 1.32/0.55    spl10_44 <=> ! [X0] : (~r2_hidden(X0,u1_struct_0(sK2)) | sP7(sK3,sK2,X0))),
% 1.32/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).
% 1.32/0.55  fof(f361,plain,(
% 1.32/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,X1,k3_tmap_1(X2,X1,sK3,sK2,X3),X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK3,X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | r1_tmap_1(sK3,X1,X3,X0)) ) | (spl10_7 | spl10_8 | ~spl10_13 | ~spl10_44)),
% 1.32/0.55    inference(subsumption_resolution,[],[f360,f136])).
% 1.32/0.55  fof(f360,plain,(
% 1.32/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,X1,k3_tmap_1(X2,X1,sK3,sK2,X3),X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK3,X2) | v2_struct_0(sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | r1_tmap_1(sK3,X1,X3,X0)) ) | (spl10_8 | ~spl10_13 | ~spl10_44)),
% 1.32/0.55    inference(subsumption_resolution,[],[f359,f141])).
% 1.32/0.55  fof(f359,plain,(
% 1.32/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,X1,k3_tmap_1(X2,X1,sK3,sK2,X3),X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK3,X2) | v2_struct_0(sK3) | v2_struct_0(sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | r1_tmap_1(sK3,X1,X3,X0)) ) | (~spl10_13 | ~spl10_44)),
% 1.32/0.55    inference(subsumption_resolution,[],[f358,f166])).
% 1.32/0.55  fof(f358,plain,(
% 1.32/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,X1,k3_tmap_1(X2,X1,sK3,sK2,X3),X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(sK3,X2) | v2_struct_0(sK3) | v2_struct_0(sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | r1_tmap_1(sK3,X1,X3,X0)) ) | ~spl10_44),
% 1.32/0.55    inference(resolution,[],[f356,f295])).
% 1.32/0.55  fof(f295,plain,(
% 1.32/0.55    ( ! [X4,X2,X0,X7,X3,X1] : (~sP7(X3,X2,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r1_tmap_1(X3,X1,X4,X7)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f97,f78])).
% 1.32/0.55  fof(f97,plain,(
% 1.32/0.55    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP7(X3,X2,X7)) )),
% 1.32/0.55    inference(general_splitting,[],[f88,f96_D])).
% 1.32/0.55  fof(f96,plain,(
% 1.32/0.55    ( ! [X2,X7,X5,X3] : (~v3_pre_topc(X5,X3) | ~r2_hidden(X7,X5) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | sP7(X3,X2,X7)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f96_D])).
% 1.32/0.55  fof(f96_D,plain,(
% 1.32/0.55    ( ! [X7,X2,X3] : (( ! [X5] : (~v3_pre_topc(X5,X3) | ~r2_hidden(X7,X5) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) ) <=> ~sP7(X3,X2,X7)) )),
% 1.32/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 1.32/0.55  fof(f88,plain,(
% 1.32/0.55    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(equality_resolution,[],[f75])).
% 1.32/0.55  fof(f75,plain,(
% 1.32/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f46])).
% 1.32/0.55  fof(f46,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.55    inference(nnf_transformation,[],[f22])).
% 1.32/0.55  fof(f22,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.55    inference(flattening,[],[f21])).
% 1.32/0.55  fof(f21,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f12])).
% 1.32/0.55  fof(f12,axiom,(
% 1.32/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).
% 1.32/0.55  fof(f356,plain,(
% 1.32/0.55    ( ! [X0] : (sP7(sK3,sK2,X0) | ~r2_hidden(X0,u1_struct_0(sK2))) ) | ~spl10_44),
% 1.32/0.55    inference(avatar_component_clause,[],[f355])).
% 1.32/0.55  fof(f357,plain,(
% 1.32/0.55    spl10_44 | ~spl10_42),
% 1.32/0.55    inference(avatar_split_clause,[],[f353,f346,f355])).
% 1.32/0.55  fof(f346,plain,(
% 1.32/0.55    spl10_42 <=> ! [X3,X2] : (~r2_hidden(X2,u1_struct_0(sK2)) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X3)) | sP7(sK3,X3,X2))),
% 1.32/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).
% 1.32/0.55  fof(f353,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK2)) | sP7(sK3,sK2,X0)) ) | ~spl10_42),
% 1.32/0.55    inference(resolution,[],[f347,f94])).
% 1.32/0.55  fof(f94,plain,(
% 1.32/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.32/0.55    inference(equality_resolution,[],[f85])).
% 1.32/0.55  fof(f85,plain,(
% 1.32/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.32/0.55    inference(cnf_transformation,[],[f50])).
% 1.32/0.55  fof(f50,plain,(
% 1.32/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.32/0.55    inference(flattening,[],[f49])).
% 1.32/0.55  fof(f49,plain,(
% 1.32/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.32/0.55    inference(nnf_transformation,[],[f1])).
% 1.32/0.55  fof(f1,axiom,(
% 1.32/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.32/0.55  fof(f347,plain,(
% 1.32/0.55    ( ! [X2,X3] : (~r1_tarski(u1_struct_0(sK2),u1_struct_0(X3)) | ~r2_hidden(X2,u1_struct_0(sK2)) | sP7(sK3,X3,X2)) ) | ~spl10_42),
% 1.32/0.55    inference(avatar_component_clause,[],[f346])).
% 1.32/0.55  fof(f348,plain,(
% 1.32/0.55    spl10_42 | ~spl10_32 | ~spl10_38),
% 1.32/0.55    inference(avatar_split_clause,[],[f344,f322,f287,f346])).
% 1.32/0.55  fof(f287,plain,(
% 1.32/0.55    spl10_32 <=> v3_pre_topc(u1_struct_0(sK2),sK3)),
% 1.32/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).
% 1.32/0.55  fof(f322,plain,(
% 1.32/0.55    spl10_38 <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.32/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).
% 1.32/0.55  fof(f344,plain,(
% 1.32/0.55    ( ! [X2,X3] : (~r2_hidden(X2,u1_struct_0(sK2)) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X3)) | sP7(sK3,X3,X2)) ) | (~spl10_32 | ~spl10_38)),
% 1.32/0.55    inference(subsumption_resolution,[],[f294,f323])).
% 1.32/0.55  fof(f323,plain,(
% 1.32/0.55    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~spl10_38),
% 1.32/0.55    inference(avatar_component_clause,[],[f322])).
% 1.32/0.55  fof(f294,plain,(
% 1.32/0.55    ( ! [X2,X3] : (~r2_hidden(X2,u1_struct_0(sK2)) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X3)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | sP7(sK3,X3,X2)) ) | ~spl10_32),
% 1.32/0.55    inference(resolution,[],[f289,f96])).
% 1.32/0.55  fof(f289,plain,(
% 1.32/0.55    v3_pre_topc(u1_struct_0(sK2),sK3) | ~spl10_32),
% 1.32/0.55    inference(avatar_component_clause,[],[f287])).
% 1.32/0.55  fof(f334,plain,(
% 1.32/0.55    ~spl10_13 | ~spl10_22 | spl10_38),
% 1.32/0.55    inference(avatar_contradiction_clause,[],[f333])).
% 1.32/0.55  fof(f333,plain,(
% 1.32/0.55    $false | (~spl10_13 | ~spl10_22 | spl10_38)),
% 1.32/0.55    inference(subsumption_resolution,[],[f332,f218])).
% 1.32/0.55  fof(f218,plain,(
% 1.32/0.55    l1_pre_topc(sK3) | ~spl10_22),
% 1.32/0.55    inference(avatar_component_clause,[],[f216])).
% 1.32/0.55  fof(f216,plain,(
% 1.32/0.55    spl10_22 <=> l1_pre_topc(sK3)),
% 1.32/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 1.32/0.55  fof(f332,plain,(
% 1.32/0.55    ~l1_pre_topc(sK3) | (~spl10_13 | spl10_38)),
% 1.32/0.55    inference(subsumption_resolution,[],[f330,f166])).
% 1.32/0.55  fof(f330,plain,(
% 1.32/0.55    ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK3) | spl10_38),
% 1.32/0.55    inference(resolution,[],[f324,f72])).
% 1.32/0.55  fof(f72,plain,(
% 1.32/0.55    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f18])).
% 1.32/0.55  fof(f18,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.32/0.55    inference(ennf_transformation,[],[f9])).
% 1.32/0.55  fof(f9,axiom,(
% 1.32/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.32/0.55  fof(f324,plain,(
% 1.32/0.55    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | spl10_38),
% 1.32/0.55    inference(avatar_component_clause,[],[f322])).
% 1.32/0.55  fof(f290,plain,(
% 1.32/0.55    spl10_32 | ~spl10_12 | ~spl10_13 | ~spl10_22 | ~spl10_28),
% 1.32/0.55    inference(avatar_split_clause,[],[f285,f257,f216,f164,f159,f287])).
% 1.32/0.55  fof(f159,plain,(
% 1.32/0.55    spl10_12 <=> v1_tsep_1(sK2,sK3)),
% 1.32/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 1.32/0.55  fof(f257,plain,(
% 1.32/0.55    spl10_28 <=> v2_pre_topc(sK3)),
% 1.32/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).
% 1.32/0.55  fof(f285,plain,(
% 1.32/0.55    v3_pre_topc(u1_struct_0(sK2),sK3) | (~spl10_12 | ~spl10_13 | ~spl10_22 | ~spl10_28)),
% 1.32/0.55    inference(subsumption_resolution,[],[f284,f259])).
% 1.32/0.55  fof(f259,plain,(
% 1.32/0.55    v2_pre_topc(sK3) | ~spl10_28),
% 1.32/0.55    inference(avatar_component_clause,[],[f257])).
% 1.32/0.55  fof(f284,plain,(
% 1.32/0.55    v3_pre_topc(u1_struct_0(sK2),sK3) | ~v2_pre_topc(sK3) | (~spl10_12 | ~spl10_13 | ~spl10_22)),
% 1.32/0.55    inference(subsumption_resolution,[],[f283,f218])).
% 1.32/0.55  fof(f283,plain,(
% 1.32/0.55    v3_pre_topc(u1_struct_0(sK2),sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl10_12 | ~spl10_13)),
% 1.32/0.55    inference(subsumption_resolution,[],[f282,f166])).
% 1.32/0.55  fof(f282,plain,(
% 1.32/0.55    ~m1_pre_topc(sK2,sK3) | v3_pre_topc(u1_struct_0(sK2),sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~spl10_12),
% 1.32/0.55    inference(resolution,[],[f277,f161])).
% 1.32/0.55  fof(f161,plain,(
% 1.32/0.55    v1_tsep_1(sK2,sK3) | ~spl10_12),
% 1.32/0.55    inference(avatar_component_clause,[],[f159])).
% 1.32/0.55  fof(f277,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f102,f72])).
% 1.32/0.55  fof(f102,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.32/0.55    inference(duplicate_literal_removal,[],[f93])).
% 1.32/0.55  fof(f93,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.32/0.55    inference(equality_resolution,[],[f79])).
% 1.32/0.55  fof(f79,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f48])).
% 1.32/0.55  fof(f48,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.32/0.55    inference(flattening,[],[f47])).
% 1.32/0.55  fof(f47,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.32/0.55    inference(nnf_transformation,[],[f30])).
% 1.32/0.55  fof(f30,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.32/0.55    inference(flattening,[],[f29])).
% 1.32/0.55  fof(f29,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f8])).
% 1.32/0.55  fof(f8,axiom,(
% 1.32/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.32/0.55  fof(f261,plain,(
% 1.32/0.55    ~spl10_25 | ~spl10_14 | ~spl10_26),
% 1.32/0.55    inference(avatar_split_clause,[],[f255,f244,f169,f240])).
% 1.32/0.55  fof(f169,plain,(
% 1.32/0.55    spl10_14 <=> sK5 = sK6),
% 1.32/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 1.32/0.55  fof(f255,plain,(
% 1.32/0.55    ~r1_tmap_1(sK3,sK1,sK4,sK5) | (~spl10_14 | ~spl10_26)),
% 1.32/0.55    inference(subsumption_resolution,[],[f234,f246])).
% 1.32/0.55  fof(f234,plain,(
% 1.32/0.55    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~spl10_14),
% 1.32/0.55    inference(forward_demodulation,[],[f70,f171])).
% 1.32/0.55  fof(f171,plain,(
% 1.32/0.55    sK5 = sK6 | ~spl10_14),
% 1.32/0.55    inference(avatar_component_clause,[],[f169])).
% 1.32/0.55  fof(f70,plain,(
% 1.32/0.55    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f45,plain,(
% 1.32/0.55    (((((((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & v1_tsep_1(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f37,f44,f43,f42,f41,f40,f39,f38])).
% 1.32/0.55  fof(f38,plain,(
% 1.32/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f39,plain,(
% 1.32/0.55    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f40,plain,(
% 1.32/0.55    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & v1_tsep_1(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f41,plain,(
% 1.32/0.55    ? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & v1_tsep_1(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) | ~r1_tmap_1(sK3,sK1,X4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) | r1_tmap_1(sK3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & v1_tsep_1(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f42,plain,(
% 1.32/0.55    ? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) | ~r1_tmap_1(sK3,sK1,X4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) | r1_tmap_1(sK3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & v1_tsep_1(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK1,sK4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK1,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & v1_tsep_1(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f43,plain,(
% 1.32/0.55    ? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK1,sK4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK1,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK1,sK4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f44,plain,(
% 1.32/0.55    ? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK1,sK4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f37,plain,(
% 1.32/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.32/0.55    inference(flattening,[],[f36])).
% 1.32/0.55  fof(f36,plain,(
% 1.32/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.32/0.55    inference(nnf_transformation,[],[f16])).
% 1.32/0.55  fof(f16,plain,(
% 1.32/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.32/0.55    inference(flattening,[],[f15])).
% 1.32/0.55  fof(f15,plain,(
% 1.32/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f14])).
% 1.32/0.55  fof(f14,negated_conjecture,(
% 1.32/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 1.32/0.55    inference(negated_conjecture,[],[f13])).
% 1.32/0.55  fof(f13,conjecture,(
% 1.32/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).
% 1.32/0.55  fof(f260,plain,(
% 1.32/0.55    spl10_28 | ~spl10_11 | ~spl10_23),
% 1.32/0.55    inference(avatar_split_clause,[],[f249,f231,f154,f257])).
% 1.32/0.55  fof(f231,plain,(
% 1.32/0.55    spl10_23 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0))),
% 1.32/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 1.32/0.55  fof(f249,plain,(
% 1.32/0.55    v2_pre_topc(sK3) | (~spl10_11 | ~spl10_23)),
% 1.32/0.55    inference(resolution,[],[f232,f156])).
% 1.32/0.55  fof(f232,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) ) | ~spl10_23),
% 1.32/0.55    inference(avatar_component_clause,[],[f231])).
% 1.32/0.55  fof(f254,plain,(
% 1.32/0.55    spl10_27 | ~spl10_10 | ~spl10_23),
% 1.32/0.55    inference(avatar_split_clause,[],[f248,f231,f149,f251])).
% 1.32/0.55  fof(f149,plain,(
% 1.32/0.55    spl10_10 <=> m1_pre_topc(sK2,sK0)),
% 1.32/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 1.32/0.55  fof(f248,plain,(
% 1.32/0.55    v2_pre_topc(sK2) | (~spl10_10 | ~spl10_23)),
% 1.32/0.55    inference(resolution,[],[f232,f151])).
% 1.32/0.55  fof(f151,plain,(
% 1.32/0.55    m1_pre_topc(sK2,sK0) | ~spl10_10),
% 1.32/0.55    inference(avatar_component_clause,[],[f149])).
% 1.32/0.55  fof(f247,plain,(
% 1.32/0.55    spl10_25 | spl10_26 | ~spl10_14),
% 1.32/0.55    inference(avatar_split_clause,[],[f229,f169,f244,f240])).
% 1.32/0.55  fof(f229,plain,(
% 1.32/0.55    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~spl10_14),
% 1.32/0.55    inference(forward_demodulation,[],[f69,f171])).
% 1.32/0.55  fof(f69,plain,(
% 1.32/0.55    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f233,plain,(
% 1.32/0.55    spl10_23 | ~spl10_2 | ~spl10_3),
% 1.32/0.55    inference(avatar_split_clause,[],[f213,f114,f109,f231])).
% 1.32/0.55  fof(f213,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) ) | (~spl10_2 | ~spl10_3)),
% 1.32/0.55    inference(subsumption_resolution,[],[f211,f111])).
% 1.32/0.55  fof(f211,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0) | ~v2_pre_topc(sK0)) ) | ~spl10_3),
% 1.32/0.55    inference(resolution,[],[f77,f116])).
% 1.32/0.55  fof(f77,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~v2_pre_topc(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f26])).
% 1.32/0.55  fof(f26,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.32/0.55    inference(flattening,[],[f25])).
% 1.32/0.55  fof(f25,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f4])).
% 1.32/0.55  fof(f4,axiom,(
% 1.32/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.32/0.55  fof(f219,plain,(
% 1.32/0.55    spl10_22 | ~spl10_11 | ~spl10_19),
% 1.32/0.55    inference(avatar_split_clause,[],[f205,f197,f154,f216])).
% 1.32/0.55  fof(f197,plain,(
% 1.32/0.55    spl10_19 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0))),
% 1.32/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 1.32/0.55  fof(f205,plain,(
% 1.32/0.55    l1_pre_topc(sK3) | (~spl10_11 | ~spl10_19)),
% 1.32/0.55    inference(resolution,[],[f198,f156])).
% 1.32/0.55  fof(f198,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) ) | ~spl10_19),
% 1.32/0.55    inference(avatar_component_clause,[],[f197])).
% 1.32/0.55  fof(f210,plain,(
% 1.32/0.55    spl10_21 | ~spl10_10 | ~spl10_19),
% 1.32/0.55    inference(avatar_split_clause,[],[f204,f197,f149,f207])).
% 1.32/0.55  fof(f204,plain,(
% 1.32/0.55    l1_pre_topc(sK2) | (~spl10_10 | ~spl10_19)),
% 1.32/0.55    inference(resolution,[],[f198,f151])).
% 1.32/0.55  fof(f199,plain,(
% 1.32/0.55    spl10_19 | ~spl10_3),
% 1.32/0.55    inference(avatar_split_clause,[],[f189,f114,f197])).
% 1.32/0.55  fof(f189,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) ) | ~spl10_3),
% 1.32/0.55    inference(resolution,[],[f71,f116])).
% 1.32/0.55  fof(f71,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f17])).
% 1.32/0.55  fof(f17,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.32/0.55    inference(ennf_transformation,[],[f5])).
% 1.32/0.55  fof(f5,axiom,(
% 1.32/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.32/0.55  fof(f195,plain,(
% 1.32/0.55    spl10_18),
% 1.32/0.55    inference(avatar_split_clause,[],[f63,f192])).
% 1.32/0.55  fof(f63,plain,(
% 1.32/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f188,plain,(
% 1.32/0.55    spl10_17),
% 1.32/0.55    inference(avatar_split_clause,[],[f62,f185])).
% 1.32/0.55  fof(f62,plain,(
% 1.32/0.55    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f183,plain,(
% 1.32/0.55    spl10_16 | ~spl10_14),
% 1.32/0.55    inference(avatar_split_clause,[],[f178,f169,f180])).
% 1.32/0.55  fof(f178,plain,(
% 1.32/0.55    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl10_14),
% 1.32/0.55    inference(forward_demodulation,[],[f67,f171])).
% 1.32/0.55  fof(f67,plain,(
% 1.32/0.55    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f177,plain,(
% 1.32/0.55    spl10_15),
% 1.32/0.55    inference(avatar_split_clause,[],[f66,f174])).
% 1.32/0.55  fof(f66,plain,(
% 1.32/0.55    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f172,plain,(
% 1.32/0.55    spl10_14),
% 1.32/0.55    inference(avatar_split_clause,[],[f68,f169])).
% 1.32/0.55  fof(f68,plain,(
% 1.32/0.55    sK5 = sK6),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f167,plain,(
% 1.32/0.55    spl10_13),
% 1.32/0.55    inference(avatar_split_clause,[],[f65,f164])).
% 1.32/0.55  fof(f65,plain,(
% 1.32/0.55    m1_pre_topc(sK2,sK3)),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f162,plain,(
% 1.32/0.55    spl10_12),
% 1.32/0.55    inference(avatar_split_clause,[],[f64,f159])).
% 1.32/0.55  fof(f64,plain,(
% 1.32/0.55    v1_tsep_1(sK2,sK3)),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f157,plain,(
% 1.32/0.55    spl10_11),
% 1.32/0.55    inference(avatar_split_clause,[],[f60,f154])).
% 1.32/0.55  fof(f60,plain,(
% 1.32/0.55    m1_pre_topc(sK3,sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f152,plain,(
% 1.32/0.55    spl10_10),
% 1.32/0.55    inference(avatar_split_clause,[],[f58,f149])).
% 1.32/0.55  fof(f58,plain,(
% 1.32/0.55    m1_pre_topc(sK2,sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f147,plain,(
% 1.32/0.55    spl10_9),
% 1.32/0.55    inference(avatar_split_clause,[],[f61,f144])).
% 1.32/0.55  fof(f61,plain,(
% 1.32/0.55    v1_funct_1(sK4)),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f142,plain,(
% 1.32/0.55    ~spl10_8),
% 1.32/0.55    inference(avatar_split_clause,[],[f59,f139])).
% 1.32/0.55  fof(f59,plain,(
% 1.32/0.55    ~v2_struct_0(sK3)),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f137,plain,(
% 1.32/0.55    ~spl10_7),
% 1.32/0.55    inference(avatar_split_clause,[],[f57,f134])).
% 1.32/0.55  fof(f57,plain,(
% 1.32/0.55    ~v2_struct_0(sK2)),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f132,plain,(
% 1.32/0.55    spl10_6),
% 1.32/0.55    inference(avatar_split_clause,[],[f56,f129])).
% 1.32/0.55  fof(f56,plain,(
% 1.32/0.55    l1_pre_topc(sK1)),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f127,plain,(
% 1.32/0.55    spl10_5),
% 1.32/0.55    inference(avatar_split_clause,[],[f55,f124])).
% 1.32/0.55  fof(f55,plain,(
% 1.32/0.55    v2_pre_topc(sK1)),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f122,plain,(
% 1.32/0.55    ~spl10_4),
% 1.32/0.55    inference(avatar_split_clause,[],[f54,f119])).
% 1.32/0.55  fof(f54,plain,(
% 1.32/0.55    ~v2_struct_0(sK1)),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f117,plain,(
% 1.32/0.55    spl10_3),
% 1.32/0.55    inference(avatar_split_clause,[],[f53,f114])).
% 1.32/0.55  fof(f53,plain,(
% 1.32/0.55    l1_pre_topc(sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f112,plain,(
% 1.32/0.55    spl10_2),
% 1.32/0.55    inference(avatar_split_clause,[],[f52,f109])).
% 1.32/0.55  fof(f52,plain,(
% 1.32/0.55    v2_pre_topc(sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  fof(f107,plain,(
% 1.32/0.55    ~spl10_1),
% 1.32/0.55    inference(avatar_split_clause,[],[f51,f104])).
% 1.32/0.55  fof(f51,plain,(
% 1.32/0.55    ~v2_struct_0(sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f45])).
% 1.32/0.55  % SZS output end Proof for theBenchmark
% 1.32/0.55  % (13726)------------------------------
% 1.32/0.55  % (13726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (13726)Termination reason: Refutation
% 1.32/0.55  
% 1.32/0.55  % (13726)Memory used [KB]: 6524
% 1.32/0.55  % (13726)Time elapsed: 0.100 s
% 1.32/0.55  % (13726)------------------------------
% 1.32/0.55  % (13726)------------------------------
% 1.32/0.55  % (13723)Success in time 0.186 s
%------------------------------------------------------------------------------
