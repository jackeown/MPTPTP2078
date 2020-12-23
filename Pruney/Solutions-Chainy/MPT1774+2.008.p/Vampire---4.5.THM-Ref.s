%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:52 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  247 ( 553 expanded)
%              Number of leaves         :   42 ( 209 expanded)
%              Depth                    :   26
%              Number of atoms          : 1821 (4466 expanded)
%              Number of equality atoms :   49 ( 157 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f474,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f83,f87,f91,f95,f99,f103,f107,f111,f115,f119,f127,f131,f182,f186,f194,f198,f202,f212,f229,f239,f270,f277,f310,f340,f372,f397,f426,f434,f458,f473])).

fof(f473,plain,
    ( ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | spl8_29
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(avatar_contradiction_clause,[],[f472])).

fof(f472,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | spl8_29
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f471,f273])).

fof(f273,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | spl8_29 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl8_29
  <=> r1_tmap_1(sK3,sK0,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f471,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f470,f106])).

fof(f106,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl8_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f470,plain,
    ( ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_6
    | spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f469,f185])).

fof(f185,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl8_17
  <=> r1_tarski(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f469,plain,
    ( ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_6
    | spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f468,f118])).

fof(f118,plain,
    ( r2_hidden(sK6,sK5)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl8_11
  <=> r2_hidden(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f468,plain,
    ( ~ r2_hidden(sK6,sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_6
    | spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f467,f201])).

fof(f201,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl8_21
  <=> m1_subset_1(sK6,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f467,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ r2_hidden(sK6,sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_6
    | spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f466,f193])).

fof(f193,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl8_19
  <=> m1_subset_1(sK6,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f466,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ r2_hidden(sK6,sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_6
    | spl8_7
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f465,f102])).

fof(f102,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl8_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f465,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ r2_hidden(sK6,sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f464,f126])).

fof(f126,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_13
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f464,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ r2_hidden(sK6,sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f463,f86])).

fof(f86,plain,
    ( ~ v2_struct_0(sK2)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl8_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f463,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ r2_hidden(sK6,sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f462,f238])).

fof(f238,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl8_27
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f462,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ r2_hidden(sK6,sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f461,f228])).

fof(f228,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl8_25
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f461,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ r2_hidden(sK6,sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f460,f78])).

fof(f78,plain,
    ( v1_funct_1(sK4)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl8_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f460,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ r2_hidden(sK6,sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6)
    | spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f459,f110])).

fof(f110,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl8_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f459,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ r2_hidden(sK6,sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6)
    | spl8_2
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_40
    | ~ spl8_50 ),
    inference(resolution,[],[f457,f386])).

fof(f386,plain,
    ( ! [X6,X4,X5,X3] :
        ( ~ r1_tmap_1(X5,X3,k2_tmap_1(sK3,X3,X4,X5),X6)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X3))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3))))
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK3)
        | v2_struct_0(X3)
        | ~ m1_subset_1(X6,u1_struct_0(sK3))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ r2_hidden(X6,sK5)
        | ~ r1_tarski(sK5,u1_struct_0(X5))
        | ~ v2_pre_topc(X3)
        | r1_tmap_1(sK3,X3,X4,X6) )
    | spl8_2
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f385,f379])).

fof(f379,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_23
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f373,f130])).

fof(f130,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl8_14
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f373,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v3_pre_topc(sK5,sK3)
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_23
    | ~ spl8_40 ),
    inference(resolution,[],[f371,f217])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK1)
        | v3_pre_topc(sK5,X0) )
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f216,f114])).

fof(f114,plain,
    ( v3_pre_topc(sK5,sK1)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl8_10
  <=> v3_pre_topc(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK1)
        | ~ v3_pre_topc(sK5,sK1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(sK5,X0) )
    | ~ spl8_6
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f213,f98])).

fof(f98,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl8_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK1)
        | ~ v3_pre_topc(sK5,sK1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(sK5,X0) )
    | ~ spl8_23 ),
    inference(resolution,[],[f211,f72])).

fof(f72,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | X1 != X3
      | v3_pre_topc(X3,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

fof(f211,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl8_23
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f371,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl8_40
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f385,plain,
    ( ! [X6,X4,X5,X3] :
        ( ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X3))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3))))
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK3)
        | v2_struct_0(X3)
        | ~ m1_subset_1(X6,u1_struct_0(sK3))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v3_pre_topc(sK5,sK3)
        | ~ r2_hidden(X6,sK5)
        | ~ r1_tarski(sK5,u1_struct_0(X5))
        | ~ r1_tmap_1(X5,X3,k2_tmap_1(sK3,X3,X4,X5),X6)
        | r1_tmap_1(sK3,X3,X4,X6) )
    | spl8_2
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f384,f181])).

fof(f181,plain,
    ( l1_pre_topc(sK3)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl8_16
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f384,plain,
    ( ! [X6,X4,X5,X3] :
        ( ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X3))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3))))
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK3)
        | v2_struct_0(X3)
        | ~ m1_subset_1(X6,u1_struct_0(sK3))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v3_pre_topc(sK5,sK3)
        | ~ r2_hidden(X6,sK5)
        | ~ r1_tarski(sK5,u1_struct_0(X5))
        | ~ r1_tmap_1(X5,X3,k2_tmap_1(sK3,X3,X4,X5),X6)
        | r1_tmap_1(sK3,X3,X4,X6) )
    | spl8_2
    | ~ spl8_20
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f383,f197])).

fof(f197,plain,
    ( v2_pre_topc(sK3)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl8_20
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f383,plain,
    ( ! [X6,X4,X5,X3] :
        ( ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X3))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3))))
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK3)
        | v2_struct_0(X3)
        | ~ m1_subset_1(X6,u1_struct_0(sK3))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v3_pre_topc(sK5,sK3)
        | ~ r2_hidden(X6,sK5)
        | ~ r1_tarski(sK5,u1_struct_0(X5))
        | ~ r1_tmap_1(X5,X3,k2_tmap_1(sK3,X3,X4,X5),X6)
        | r1_tmap_1(sK3,X3,X4,X6) )
    | spl8_2
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f377,f82])).

fof(f82,plain,
    ( ~ v2_struct_0(sK3)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl8_2
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f377,plain,
    ( ! [X6,X4,X5,X3] :
        ( ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X3))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3))))
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK3)
        | v2_struct_0(X3)
        | ~ m1_subset_1(X6,u1_struct_0(sK3))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v3_pre_topc(sK5,sK3)
        | ~ r2_hidden(X6,sK5)
        | ~ r1_tarski(sK5,u1_struct_0(X5))
        | ~ r1_tmap_1(X5,X3,k2_tmap_1(sK3,X3,X4,X5),X6)
        | r1_tmap_1(sK3,X3,X4,X6) )
    | ~ spl8_40 ),
    inference(resolution,[],[f371,f71])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v3_pre_topc(X4,X1)
      | ~ r2_hidden(X6,X4)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
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
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v3_pre_topc(X4,X1)
      | ~ r2_hidden(X5,X4)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | X5 != X6
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & r1_tarski(X4,u1_struct_0(X3))
                                  & r2_hidden(X5,X4)
                                  & v3_pre_topc(X4,X1) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).

fof(f457,plain,
    ( r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f432])).

fof(f432,plain,
    ( spl8_50
  <=> r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f458,plain,
    ( spl8_50
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40
    | ~ spl8_49 ),
    inference(avatar_split_clause,[],[f455,f424,f370,f237,f227,f210,f200,f196,f184,f180,f129,f125,f117,f113,f109,f105,f101,f97,f85,f81,f77,f432])).

fof(f424,plain,
    ( spl8_49
  <=> k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f455,plain,
    ( r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40
    | ~ spl8_49 ),
    inference(subsumption_resolution,[],[f445,f454])).

fof(f454,plain,
    ( r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_49 ),
    inference(forward_demodulation,[],[f75,f425])).

fof(f425,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2)
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f424])).

fof(f75,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(forward_demodulation,[],[f34,f40])).

fof(f40,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X2))
                                     => ( ( X6 = X7
                                          & r1_tarski(X5,u1_struct_0(X2))
                                          & r2_hidden(X6,X5)
                                          & v3_pre_topc(X5,X1) )
                                       => ( r1_tmap_1(X3,X0,X4,X6)
                                        <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

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
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X1) )
                                     => ( r1_tmap_1(X3,X0,X4,X6)
                                      <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).

fof(f34,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f15])).

fof(f445,plain,
    ( r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f444,f185])).

fof(f444,plain,
    ( ~ r1_tarski(sK5,u1_struct_0(sK2))
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f443,f118])).

fof(f443,plain,
    ( ~ r2_hidden(sK6,sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f442,f126])).

fof(f442,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ r2_hidden(sK6,sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f436,f86])).

fof(f436,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r2_hidden(sK6,sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40 ),
    inference(resolution,[],[f380,f201])).

fof(f380,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ r2_hidden(X1,sK5)
        | ~ r1_tarski(sK5,u1_struct_0(X0))
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),X1)
        | ~ r1_tmap_1(sK3,sK0,sK4,X1) )
    | ~ spl8_1
    | spl8_2
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f375,f379])).

fof(f375,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v3_pre_topc(sK5,sK3)
        | ~ r2_hidden(X1,sK5)
        | ~ r1_tarski(sK5,u1_struct_0(X0))
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),X1)
        | ~ r1_tmap_1(sK3,sK0,sK4,X1) )
    | ~ spl8_1
    | spl8_2
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_40 ),
    inference(resolution,[],[f371,f266])).

fof(f266,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(X1)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ v3_pre_topc(X2,sK3)
        | ~ r2_hidden(X3,X2)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3)
        | ~ r1_tmap_1(sK3,sK0,sK4,X3) )
    | ~ spl8_1
    | spl8_2
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_25
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f265,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f265,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ v3_pre_topc(X2,sK3)
        | ~ r2_hidden(X3,X2)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3)
        | ~ r1_tmap_1(sK3,sK0,sK4,X3) )
    | ~ spl8_1
    | spl8_2
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_25
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f264,f102])).

fof(f264,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ v3_pre_topc(X2,sK3)
        | ~ r2_hidden(X3,X2)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3)
        | ~ r1_tmap_1(sK3,sK0,sK4,X3) )
    | ~ spl8_1
    | spl8_2
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_25
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f263,f228])).

fof(f263,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ v3_pre_topc(X2,sK3)
        | ~ r2_hidden(X3,X2)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3)
        | ~ r1_tmap_1(sK3,sK0,sK4,X3) )
    | ~ spl8_1
    | spl8_2
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f262,f78])).

fof(f262,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ v3_pre_topc(X2,sK3)
        | ~ r2_hidden(X3,X2)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3)
        | ~ r1_tmap_1(sK3,sK0,sK4,X3) )
    | spl8_2
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f261,f181])).

fof(f261,plain,
    ( ! [X2,X3,X1] :
        ( ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ v3_pre_topc(X2,sK3)
        | ~ r2_hidden(X3,X2)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3)
        | ~ r1_tmap_1(sK3,sK0,sK4,X3) )
    | spl8_2
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_20
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f260,f197])).

fof(f260,plain,
    ( ! [X2,X3,X1] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ v3_pre_topc(X2,sK3)
        | ~ r2_hidden(X3,X2)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3)
        | ~ r1_tmap_1(sK3,sK0,sK4,X3) )
    | spl8_2
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f259,f82])).

fof(f259,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ v3_pre_topc(X2,sK3)
        | ~ r2_hidden(X3,X2)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3)
        | ~ r1_tmap_1(sK3,sK0,sK4,X3) )
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f258,f110])).

fof(f258,plain,
    ( ! [X2,X3,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ v3_pre_topc(X2,sK3)
        | ~ r2_hidden(X3,X2)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3)
        | ~ r1_tmap_1(sK3,sK0,sK4,X3) )
    | ~ spl8_8
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f248,f106])).

fof(f248,plain,
    ( ! [X2,X3,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ v3_pre_topc(X2,sK3)
        | ~ r2_hidden(X3,X2)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3)
        | ~ r1_tmap_1(sK3,sK0,sK4,X3) )
    | ~ spl8_27 ),
    inference(resolution,[],[f238,f70])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
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
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v3_pre_topc(X4,X1)
      | ~ r2_hidden(X6,X4)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
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
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v3_pre_topc(X4,X1)
      | ~ r2_hidden(X5,X4)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | X5 != X6
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f434,plain,
    ( ~ spl8_50
    | spl8_30
    | ~ spl8_49 ),
    inference(avatar_split_clause,[],[f430,f424,f275,f432])).

fof(f275,plain,
    ( spl8_30
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f430,plain,
    ( ~ r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | spl8_30
    | ~ spl8_49 ),
    inference(superposition,[],[f276,f425])).

fof(f276,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | spl8_30 ),
    inference(avatar_component_clause,[],[f275])).

fof(f426,plain,
    ( spl8_49
    | ~ spl8_1
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f422,f395,f237,f227,f129,f125,f109,f105,f101,f97,f93,f89,f77,f424])).

fof(f89,plain,
    ( spl8_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f93,plain,
    ( spl8_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f395,plain,
    ( spl8_42
  <=> k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f422,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2)
    | ~ spl8_1
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_42 ),
    inference(forward_demodulation,[],[f421,f396])).

fof(f396,plain,
    ( k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f395])).

fof(f421,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | ~ spl8_1
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_25
    | ~ spl8_27 ),
    inference(resolution,[],[f363,f126])).

fof(f363,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | ~ spl8_1
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_25
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f362,f102])).

fof(f362,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | ~ spl8_1
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_25
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f361,f228])).

fof(f361,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | ~ spl8_1
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f360,f78])).

fof(f360,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f359,f110])).

fof(f359,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f358,f106])).

fof(f358,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_27 ),
    inference(resolution,[],[f166,f238])).

fof(f166,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,sK3)
        | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2)) )
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f165,f161])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | m1_pre_topc(X0,sK1) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f160,f94])).

fof(f94,plain,
    ( v2_pre_topc(sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK3)
        | m1_pre_topc(X0,sK1) )
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f146,f98])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK3)
        | m1_pre_topc(X0,sK1) )
    | ~ spl8_14 ),
    inference(resolution,[],[f130,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f165,plain,
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
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f164,f90])).

fof(f90,plain,
    ( ~ v2_struct_0(sK1)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f164,plain,
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
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f163,f98])).

fof(f163,plain,
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
    | ~ spl8_5
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f148,f94])).

fof(f148,plain,
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
    | ~ spl8_14 ),
    inference(resolution,[],[f130,f57])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f397,plain,
    ( spl8_42
    | ~ spl8_1
    | spl8_2
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_25
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f350,f237,f227,f196,f180,f125,f109,f105,f101,f81,f77,f395])).

fof(f350,plain,
    ( k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | ~ spl8_1
    | spl8_2
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_25
    | ~ spl8_27 ),
    inference(resolution,[],[f257,f126])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | ~ spl8_1
    | spl8_2
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_25
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f256,f82])).

fof(f256,plain,
    ( ! [X0] :
        ( v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | ~ spl8_1
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_25
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f255,f228])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | ~ spl8_1
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f254,f78])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f253,f110])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | spl8_7
    | ~ spl8_8
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f252,f106])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | spl8_7
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f251,f102])).

fof(f251,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f250,f181])).

fof(f250,plain,
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
    | ~ spl8_20
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f247,f197])).

fof(f247,plain,
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
    | ~ spl8_27 ),
    inference(resolution,[],[f238,f66])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f372,plain,
    ( spl8_40
    | ~ spl8_37 ),
    inference(avatar_split_clause,[],[f352,f338,f370])).

fof(f338,plain,
    ( spl8_37
  <=> r1_tarski(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f352,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl8_37 ),
    inference(resolution,[],[f339,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f339,plain,
    ( r1_tarski(sK5,u1_struct_0(sK3))
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f338])).

fof(f340,plain,
    ( spl8_37
    | ~ spl8_17
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f332,f308,f184,f338])).

fof(f308,plain,
    ( spl8_33
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f332,plain,
    ( r1_tarski(sK5,u1_struct_0(sK3))
    | ~ spl8_17
    | ~ spl8_33 ),
    inference(resolution,[],[f309,f208])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK2),X0)
        | r1_tarski(sK5,X0) )
    | ~ spl8_17 ),
    inference(resolution,[],[f185,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f309,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f308])).

fof(f310,plain,
    ( spl8_33
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f295,f268,f308])).

fof(f268,plain,
    ( spl8_28
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f295,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl8_28 ),
    inference(resolution,[],[f269,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f269,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f268])).

fof(f277,plain,
    ( ~ spl8_29
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f74,f275,f272])).

fof(f74,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(forward_demodulation,[],[f35,f40])).

fof(f35,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f15])).

fof(f270,plain,
    ( spl8_28
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f151,f129,f125,f97,f268])).

fof(f151,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f140,f149])).

fof(f149,plain,
    ( l1_pre_topc(sK3)
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f144,f98])).

fof(f144,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3)
    | ~ spl8_14 ),
    inference(resolution,[],[f130,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f140,plain,
    ( ~ l1_pre_topc(sK3)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl8_13 ),
    inference(resolution,[],[f126,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f239,plain,(
    spl8_27 ),
    inference(avatar_split_clause,[],[f45,f237])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f229,plain,(
    spl8_25 ),
    inference(avatar_split_clause,[],[f44,f227])).

fof(f44,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f212,plain,(
    spl8_23 ),
    inference(avatar_split_clause,[],[f42,f210])).

fof(f42,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f202,plain,(
    spl8_21 ),
    inference(avatar_split_clause,[],[f73,f200])).

fof(f73,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f36,f40])).

fof(f36,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f198,plain,
    ( spl8_20
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f156,f129,f97,f93,f196])).

fof(f156,plain,
    ( v2_pre_topc(sK3)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f155,f94])).

fof(f155,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK3)
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f145,f98])).

fof(f145,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK3)
    | ~ spl8_14 ),
    inference(resolution,[],[f130,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f194,plain,(
    spl8_19 ),
    inference(avatar_split_clause,[],[f41,f192])).

fof(f41,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f186,plain,(
    spl8_17 ),
    inference(avatar_split_clause,[],[f39,f184])).

fof(f39,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f182,plain,
    ( spl8_16
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f149,f129,f97,f180])).

fof(f131,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f48,f129])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f127,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f46,f125])).

fof(f46,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f119,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f38,f117])).

fof(f38,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f15])).

fof(f115,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f37,f113])).

fof(f37,plain,(
    v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f111,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f56,f109])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f107,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f55,f105])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f103,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f54,f101])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f99,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f53,f97])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f95,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f52,f93])).

fof(f52,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f51,f89])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f49,f85])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f47,f81])).

fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f43,f77])).

fof(f43,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:48:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (25604)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (25598)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (25609)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (25596)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (25603)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (25590)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (25592)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (25595)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (25602)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (25606)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.43/0.54  % (25590)Refutation found. Thanks to Tanya!
% 1.43/0.54  % SZS status Theorem for theBenchmark
% 1.43/0.54  % SZS output start Proof for theBenchmark
% 1.43/0.54  fof(f474,plain,(
% 1.43/0.54    $false),
% 1.43/0.54    inference(avatar_sat_refutation,[],[f79,f83,f87,f91,f95,f99,f103,f107,f111,f115,f119,f127,f131,f182,f186,f194,f198,f202,f212,f229,f239,f270,f277,f310,f340,f372,f397,f426,f434,f458,f473])).
% 1.43/0.54  fof(f473,plain,(
% 1.43/0.54    ~spl8_1 | spl8_2 | spl8_3 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_17 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_23 | ~spl8_25 | ~spl8_27 | spl8_29 | ~spl8_40 | ~spl8_50),
% 1.43/0.54    inference(avatar_contradiction_clause,[],[f472])).
% 1.43/0.54  fof(f472,plain,(
% 1.43/0.54    $false | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_17 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_23 | ~spl8_25 | ~spl8_27 | spl8_29 | ~spl8_40 | ~spl8_50)),
% 1.43/0.54    inference(subsumption_resolution,[],[f471,f273])).
% 1.43/0.54  fof(f273,plain,(
% 1.43/0.54    ~r1_tmap_1(sK3,sK0,sK4,sK6) | spl8_29),
% 1.43/0.54    inference(avatar_component_clause,[],[f272])).
% 1.43/0.54  fof(f272,plain,(
% 1.43/0.54    spl8_29 <=> r1_tmap_1(sK3,sK0,sK4,sK6)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 1.43/0.54  fof(f471,plain,(
% 1.43/0.54    r1_tmap_1(sK3,sK0,sK4,sK6) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_17 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_23 | ~spl8_25 | ~spl8_27 | ~spl8_40 | ~spl8_50)),
% 1.43/0.54    inference(subsumption_resolution,[],[f470,f106])).
% 1.43/0.54  fof(f106,plain,(
% 1.43/0.54    v2_pre_topc(sK0) | ~spl8_8),
% 1.43/0.54    inference(avatar_component_clause,[],[f105])).
% 1.43/0.54  fof(f105,plain,(
% 1.43/0.54    spl8_8 <=> v2_pre_topc(sK0)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.43/0.54  fof(f470,plain,(
% 1.43/0.54    ~v2_pre_topc(sK0) | r1_tmap_1(sK3,sK0,sK4,sK6) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_6 | spl8_7 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_17 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_23 | ~spl8_25 | ~spl8_27 | ~spl8_40 | ~spl8_50)),
% 1.43/0.54    inference(subsumption_resolution,[],[f469,f185])).
% 1.43/0.54  fof(f185,plain,(
% 1.43/0.54    r1_tarski(sK5,u1_struct_0(sK2)) | ~spl8_17),
% 1.43/0.54    inference(avatar_component_clause,[],[f184])).
% 1.43/0.54  fof(f184,plain,(
% 1.43/0.54    spl8_17 <=> r1_tarski(sK5,u1_struct_0(sK2))),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.43/0.54  fof(f469,plain,(
% 1.43/0.54    ~r1_tarski(sK5,u1_struct_0(sK2)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK3,sK0,sK4,sK6) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_6 | spl8_7 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_23 | ~spl8_25 | ~spl8_27 | ~spl8_40 | ~spl8_50)),
% 1.43/0.54    inference(subsumption_resolution,[],[f468,f118])).
% 1.43/0.54  fof(f118,plain,(
% 1.43/0.54    r2_hidden(sK6,sK5) | ~spl8_11),
% 1.43/0.54    inference(avatar_component_clause,[],[f117])).
% 1.43/0.54  fof(f117,plain,(
% 1.43/0.54    spl8_11 <=> r2_hidden(sK6,sK5)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.43/0.54  fof(f468,plain,(
% 1.43/0.54    ~r2_hidden(sK6,sK5) | ~r1_tarski(sK5,u1_struct_0(sK2)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK3,sK0,sK4,sK6) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_6 | spl8_7 | ~spl8_9 | ~spl8_10 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_19 | ~spl8_20 | ~spl8_21 | ~spl8_23 | ~spl8_25 | ~spl8_27 | ~spl8_40 | ~spl8_50)),
% 1.43/0.54    inference(subsumption_resolution,[],[f467,f201])).
% 1.43/0.54  fof(f201,plain,(
% 1.43/0.54    m1_subset_1(sK6,u1_struct_0(sK2)) | ~spl8_21),
% 1.43/0.54    inference(avatar_component_clause,[],[f200])).
% 1.43/0.54  fof(f200,plain,(
% 1.43/0.54    spl8_21 <=> m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.43/0.54  fof(f467,plain,(
% 1.43/0.54    ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r2_hidden(sK6,sK5) | ~r1_tarski(sK5,u1_struct_0(sK2)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK3,sK0,sK4,sK6) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_6 | spl8_7 | ~spl8_9 | ~spl8_10 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_19 | ~spl8_20 | ~spl8_23 | ~spl8_25 | ~spl8_27 | ~spl8_40 | ~spl8_50)),
% 1.43/0.54    inference(subsumption_resolution,[],[f466,f193])).
% 1.43/0.54  fof(f193,plain,(
% 1.43/0.54    m1_subset_1(sK6,u1_struct_0(sK3)) | ~spl8_19),
% 1.43/0.54    inference(avatar_component_clause,[],[f192])).
% 1.43/0.54  fof(f192,plain,(
% 1.43/0.54    spl8_19 <=> m1_subset_1(sK6,u1_struct_0(sK3))),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.43/0.54  fof(f466,plain,(
% 1.43/0.54    ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r2_hidden(sK6,sK5) | ~r1_tarski(sK5,u1_struct_0(sK2)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK3,sK0,sK4,sK6) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_6 | spl8_7 | ~spl8_9 | ~spl8_10 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_20 | ~spl8_23 | ~spl8_25 | ~spl8_27 | ~spl8_40 | ~spl8_50)),
% 1.43/0.54    inference(subsumption_resolution,[],[f465,f102])).
% 1.43/0.54  fof(f102,plain,(
% 1.43/0.54    ~v2_struct_0(sK0) | spl8_7),
% 1.43/0.54    inference(avatar_component_clause,[],[f101])).
% 1.43/0.54  fof(f101,plain,(
% 1.43/0.54    spl8_7 <=> v2_struct_0(sK0)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.43/0.54  fof(f465,plain,(
% 1.43/0.54    v2_struct_0(sK0) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r2_hidden(sK6,sK5) | ~r1_tarski(sK5,u1_struct_0(sK2)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK3,sK0,sK4,sK6) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_6 | ~spl8_9 | ~spl8_10 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_20 | ~spl8_23 | ~spl8_25 | ~spl8_27 | ~spl8_40 | ~spl8_50)),
% 1.43/0.54    inference(subsumption_resolution,[],[f464,f126])).
% 1.43/0.54  fof(f126,plain,(
% 1.43/0.54    m1_pre_topc(sK2,sK3) | ~spl8_13),
% 1.43/0.54    inference(avatar_component_clause,[],[f125])).
% 1.43/0.54  fof(f125,plain,(
% 1.43/0.54    spl8_13 <=> m1_pre_topc(sK2,sK3)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.43/0.54  fof(f464,plain,(
% 1.43/0.54    ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK0) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r2_hidden(sK6,sK5) | ~r1_tarski(sK5,u1_struct_0(sK2)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK3,sK0,sK4,sK6) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_6 | ~spl8_9 | ~spl8_10 | ~spl8_14 | ~spl8_16 | ~spl8_20 | ~spl8_23 | ~spl8_25 | ~spl8_27 | ~spl8_40 | ~spl8_50)),
% 1.43/0.54    inference(subsumption_resolution,[],[f463,f86])).
% 1.43/0.54  fof(f86,plain,(
% 1.43/0.54    ~v2_struct_0(sK2) | spl8_3),
% 1.43/0.54    inference(avatar_component_clause,[],[f85])).
% 1.43/0.54  fof(f85,plain,(
% 1.43/0.54    spl8_3 <=> v2_struct_0(sK2)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.43/0.54  fof(f463,plain,(
% 1.43/0.54    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK0) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r2_hidden(sK6,sK5) | ~r1_tarski(sK5,u1_struct_0(sK2)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK3,sK0,sK4,sK6) | (~spl8_1 | spl8_2 | ~spl8_6 | ~spl8_9 | ~spl8_10 | ~spl8_14 | ~spl8_16 | ~spl8_20 | ~spl8_23 | ~spl8_25 | ~spl8_27 | ~spl8_40 | ~spl8_50)),
% 1.43/0.54    inference(subsumption_resolution,[],[f462,f238])).
% 1.43/0.54  fof(f238,plain,(
% 1.43/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~spl8_27),
% 1.43/0.54    inference(avatar_component_clause,[],[f237])).
% 1.43/0.54  fof(f237,plain,(
% 1.43/0.54    spl8_27 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 1.43/0.54  fof(f462,plain,(
% 1.43/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK0) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r2_hidden(sK6,sK5) | ~r1_tarski(sK5,u1_struct_0(sK2)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK3,sK0,sK4,sK6) | (~spl8_1 | spl8_2 | ~spl8_6 | ~spl8_9 | ~spl8_10 | ~spl8_14 | ~spl8_16 | ~spl8_20 | ~spl8_23 | ~spl8_25 | ~spl8_40 | ~spl8_50)),
% 1.43/0.54    inference(subsumption_resolution,[],[f461,f228])).
% 1.43/0.54  fof(f228,plain,(
% 1.43/0.54    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~spl8_25),
% 1.43/0.54    inference(avatar_component_clause,[],[f227])).
% 1.43/0.54  fof(f227,plain,(
% 1.43/0.54    spl8_25 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 1.43/0.54  fof(f461,plain,(
% 1.43/0.54    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK0) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r2_hidden(sK6,sK5) | ~r1_tarski(sK5,u1_struct_0(sK2)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK3,sK0,sK4,sK6) | (~spl8_1 | spl8_2 | ~spl8_6 | ~spl8_9 | ~spl8_10 | ~spl8_14 | ~spl8_16 | ~spl8_20 | ~spl8_23 | ~spl8_40 | ~spl8_50)),
% 1.43/0.54    inference(subsumption_resolution,[],[f460,f78])).
% 1.43/0.54  fof(f78,plain,(
% 1.43/0.54    v1_funct_1(sK4) | ~spl8_1),
% 1.43/0.54    inference(avatar_component_clause,[],[f77])).
% 1.43/0.54  fof(f77,plain,(
% 1.43/0.54    spl8_1 <=> v1_funct_1(sK4)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.43/0.54  fof(f460,plain,(
% 1.43/0.54    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK0) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r2_hidden(sK6,sK5) | ~r1_tarski(sK5,u1_struct_0(sK2)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK3,sK0,sK4,sK6) | (spl8_2 | ~spl8_6 | ~spl8_9 | ~spl8_10 | ~spl8_14 | ~spl8_16 | ~spl8_20 | ~spl8_23 | ~spl8_40 | ~spl8_50)),
% 1.43/0.54    inference(subsumption_resolution,[],[f459,f110])).
% 1.43/0.54  fof(f110,plain,(
% 1.43/0.54    l1_pre_topc(sK0) | ~spl8_9),
% 1.43/0.54    inference(avatar_component_clause,[],[f109])).
% 1.43/0.54  fof(f109,plain,(
% 1.43/0.54    spl8_9 <=> l1_pre_topc(sK0)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.43/0.54  fof(f459,plain,(
% 1.43/0.54    ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK0) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r2_hidden(sK6,sK5) | ~r1_tarski(sK5,u1_struct_0(sK2)) | ~v2_pre_topc(sK0) | r1_tmap_1(sK3,sK0,sK4,sK6) | (spl8_2 | ~spl8_6 | ~spl8_10 | ~spl8_14 | ~spl8_16 | ~spl8_20 | ~spl8_23 | ~spl8_40 | ~spl8_50)),
% 1.43/0.54    inference(resolution,[],[f457,f386])).
% 1.43/0.54  fof(f386,plain,(
% 1.43/0.54    ( ! [X6,X4,X5,X3] : (~r1_tmap_1(X5,X3,k2_tmap_1(sK3,X3,X4,X5),X6) | ~l1_pre_topc(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3)))) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | v2_struct_0(X3) | ~m1_subset_1(X6,u1_struct_0(sK3)) | ~m1_subset_1(X6,u1_struct_0(X5)) | ~r2_hidden(X6,sK5) | ~r1_tarski(sK5,u1_struct_0(X5)) | ~v2_pre_topc(X3) | r1_tmap_1(sK3,X3,X4,X6)) ) | (spl8_2 | ~spl8_6 | ~spl8_10 | ~spl8_14 | ~spl8_16 | ~spl8_20 | ~spl8_23 | ~spl8_40)),
% 1.43/0.54    inference(subsumption_resolution,[],[f385,f379])).
% 1.43/0.54  fof(f379,plain,(
% 1.43/0.54    v3_pre_topc(sK5,sK3) | (~spl8_6 | ~spl8_10 | ~spl8_14 | ~spl8_23 | ~spl8_40)),
% 1.43/0.54    inference(subsumption_resolution,[],[f373,f130])).
% 1.43/0.54  fof(f130,plain,(
% 1.43/0.54    m1_pre_topc(sK3,sK1) | ~spl8_14),
% 1.43/0.54    inference(avatar_component_clause,[],[f129])).
% 1.43/0.54  fof(f129,plain,(
% 1.43/0.54    spl8_14 <=> m1_pre_topc(sK3,sK1)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.43/0.54  fof(f373,plain,(
% 1.43/0.54    ~m1_pre_topc(sK3,sK1) | v3_pre_topc(sK5,sK3) | (~spl8_6 | ~spl8_10 | ~spl8_23 | ~spl8_40)),
% 1.43/0.54    inference(resolution,[],[f371,f217])).
% 1.43/0.54  fof(f217,plain,(
% 1.43/0.54    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK1) | v3_pre_topc(sK5,X0)) ) | (~spl8_6 | ~spl8_10 | ~spl8_23)),
% 1.43/0.54    inference(subsumption_resolution,[],[f216,f114])).
% 1.43/0.54  fof(f114,plain,(
% 1.43/0.54    v3_pre_topc(sK5,sK1) | ~spl8_10),
% 1.43/0.54    inference(avatar_component_clause,[],[f113])).
% 1.43/0.54  fof(f113,plain,(
% 1.43/0.54    spl8_10 <=> v3_pre_topc(sK5,sK1)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.43/0.54  fof(f216,plain,(
% 1.43/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK1) | ~v3_pre_topc(sK5,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK5,X0)) ) | (~spl8_6 | ~spl8_23)),
% 1.43/0.54    inference(subsumption_resolution,[],[f213,f98])).
% 1.43/0.54  fof(f98,plain,(
% 1.43/0.54    l1_pre_topc(sK1) | ~spl8_6),
% 1.43/0.54    inference(avatar_component_clause,[],[f97])).
% 1.43/0.54  fof(f97,plain,(
% 1.43/0.54    spl8_6 <=> l1_pre_topc(sK1)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.43/0.54  fof(f213,plain,(
% 1.43/0.54    ( ! [X0] : (~l1_pre_topc(sK1) | ~m1_pre_topc(X0,sK1) | ~v3_pre_topc(sK5,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK5,X0)) ) | ~spl8_23),
% 1.43/0.54    inference(resolution,[],[f211,f72])).
% 1.43/0.54  fof(f72,plain,(
% 1.43/0.54    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2)) )),
% 1.43/0.54    inference(equality_resolution,[],[f60])).
% 1.43/0.54  fof(f60,plain,(
% 1.43/0.54    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | X1 != X3 | v3_pre_topc(X3,X2)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f21])).
% 1.43/0.54  fof(f21,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.54    inference(flattening,[],[f20])).
% 1.43/0.54  fof(f20,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.54    inference(ennf_transformation,[],[f6])).
% 1.43/0.54  fof(f6,axiom,(
% 1.43/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).
% 1.43/0.54  fof(f211,plain,(
% 1.43/0.54    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl8_23),
% 1.43/0.54    inference(avatar_component_clause,[],[f210])).
% 1.43/0.54  fof(f210,plain,(
% 1.43/0.54    spl8_23 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 1.43/0.54  fof(f371,plain,(
% 1.43/0.54    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~spl8_40),
% 1.43/0.54    inference(avatar_component_clause,[],[f370])).
% 1.43/0.54  fof(f370,plain,(
% 1.43/0.54    spl8_40 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 1.43/0.54  fof(f385,plain,(
% 1.43/0.54    ( ! [X6,X4,X5,X3] : (~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3)))) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | v2_struct_0(X3) | ~m1_subset_1(X6,u1_struct_0(sK3)) | ~m1_subset_1(X6,u1_struct_0(X5)) | ~v3_pre_topc(sK5,sK3) | ~r2_hidden(X6,sK5) | ~r1_tarski(sK5,u1_struct_0(X5)) | ~r1_tmap_1(X5,X3,k2_tmap_1(sK3,X3,X4,X5),X6) | r1_tmap_1(sK3,X3,X4,X6)) ) | (spl8_2 | ~spl8_16 | ~spl8_20 | ~spl8_40)),
% 1.43/0.54    inference(subsumption_resolution,[],[f384,f181])).
% 1.43/0.54  fof(f181,plain,(
% 1.43/0.54    l1_pre_topc(sK3) | ~spl8_16),
% 1.43/0.54    inference(avatar_component_clause,[],[f180])).
% 1.43/0.54  fof(f180,plain,(
% 1.43/0.54    spl8_16 <=> l1_pre_topc(sK3)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.43/0.54  fof(f384,plain,(
% 1.43/0.54    ( ! [X6,X4,X5,X3] : (~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~l1_pre_topc(sK3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3)))) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | v2_struct_0(X3) | ~m1_subset_1(X6,u1_struct_0(sK3)) | ~m1_subset_1(X6,u1_struct_0(X5)) | ~v3_pre_topc(sK5,sK3) | ~r2_hidden(X6,sK5) | ~r1_tarski(sK5,u1_struct_0(X5)) | ~r1_tmap_1(X5,X3,k2_tmap_1(sK3,X3,X4,X5),X6) | r1_tmap_1(sK3,X3,X4,X6)) ) | (spl8_2 | ~spl8_20 | ~spl8_40)),
% 1.43/0.54    inference(subsumption_resolution,[],[f383,f197])).
% 1.43/0.54  fof(f197,plain,(
% 1.43/0.54    v2_pre_topc(sK3) | ~spl8_20),
% 1.43/0.54    inference(avatar_component_clause,[],[f196])).
% 1.43/0.54  fof(f196,plain,(
% 1.43/0.54    spl8_20 <=> v2_pre_topc(sK3)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.43/0.54  fof(f383,plain,(
% 1.43/0.54    ( ! [X6,X4,X5,X3] : (~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3)))) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | v2_struct_0(X3) | ~m1_subset_1(X6,u1_struct_0(sK3)) | ~m1_subset_1(X6,u1_struct_0(X5)) | ~v3_pre_topc(sK5,sK3) | ~r2_hidden(X6,sK5) | ~r1_tarski(sK5,u1_struct_0(X5)) | ~r1_tmap_1(X5,X3,k2_tmap_1(sK3,X3,X4,X5),X6) | r1_tmap_1(sK3,X3,X4,X6)) ) | (spl8_2 | ~spl8_40)),
% 1.43/0.54    inference(subsumption_resolution,[],[f377,f82])).
% 1.43/0.54  fof(f82,plain,(
% 1.43/0.54    ~v2_struct_0(sK3) | spl8_2),
% 1.43/0.54    inference(avatar_component_clause,[],[f81])).
% 1.43/0.54  fof(f81,plain,(
% 1.43/0.54    spl8_2 <=> v2_struct_0(sK3)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.43/0.54  fof(f377,plain,(
% 1.43/0.54    ( ! [X6,X4,X5,X3] : (~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X3)))) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | v2_struct_0(X3) | ~m1_subset_1(X6,u1_struct_0(sK3)) | ~m1_subset_1(X6,u1_struct_0(X5)) | ~v3_pre_topc(sK5,sK3) | ~r2_hidden(X6,sK5) | ~r1_tarski(sK5,u1_struct_0(X5)) | ~r1_tmap_1(X5,X3,k2_tmap_1(sK3,X3,X4,X5),X6) | r1_tmap_1(sK3,X3,X4,X6)) ) | ~spl8_40),
% 1.43/0.54    inference(resolution,[],[f371,f71])).
% 1.43/0.54  fof(f71,plain,(
% 1.43/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | v2_struct_0(X0) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X6,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 1.43/0.54    inference(equality_resolution,[],[f58])).
% 1.43/0.54  fof(f58,plain,(
% 1.43/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X5,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f19])).
% 1.43/0.54  fof(f19,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.43/0.54    inference(flattening,[],[f18])).
% 1.43/0.54  fof(f18,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.43/0.54    inference(ennf_transformation,[],[f10])).
% 1.43/0.54  fof(f10,axiom,(
% 1.43/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).
% 1.43/0.54  fof(f457,plain,(
% 1.43/0.54    r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) | ~spl8_50),
% 1.43/0.54    inference(avatar_component_clause,[],[f432])).
% 1.43/0.54  fof(f432,plain,(
% 1.43/0.54    spl8_50 <=> r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 1.43/0.54  fof(f458,plain,(
% 1.43/0.54    spl8_50 | ~spl8_1 | spl8_2 | spl8_3 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_17 | ~spl8_20 | ~spl8_21 | ~spl8_23 | ~spl8_25 | ~spl8_27 | ~spl8_40 | ~spl8_49),
% 1.43/0.54    inference(avatar_split_clause,[],[f455,f424,f370,f237,f227,f210,f200,f196,f184,f180,f129,f125,f117,f113,f109,f105,f101,f97,f85,f81,f77,f432])).
% 1.43/0.54  fof(f424,plain,(
% 1.43/0.54    spl8_49 <=> k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 1.43/0.54  fof(f455,plain,(
% 1.43/0.54    r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_17 | ~spl8_20 | ~spl8_21 | ~spl8_23 | ~spl8_25 | ~spl8_27 | ~spl8_40 | ~spl8_49)),
% 1.43/0.54    inference(subsumption_resolution,[],[f445,f454])).
% 1.43/0.54  fof(f454,plain,(
% 1.43/0.54    r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6) | ~spl8_49),
% 1.43/0.54    inference(forward_demodulation,[],[f75,f425])).
% 1.43/0.54  fof(f425,plain,(
% 1.43/0.54    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2) | ~spl8_49),
% 1.43/0.54    inference(avatar_component_clause,[],[f424])).
% 1.43/0.54  fof(f75,plain,(
% 1.43/0.54    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 1.43/0.54    inference(forward_demodulation,[],[f34,f40])).
% 1.43/0.54  fof(f40,plain,(
% 1.43/0.54    sK6 = sK7),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f15,plain,(
% 1.43/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.43/0.54    inference(flattening,[],[f14])).
% 1.43/0.54  fof(f14,plain,(
% 1.43/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.43/0.54    inference(ennf_transformation,[],[f13])).
% 1.43/0.54  fof(f13,negated_conjecture,(
% 1.43/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 1.43/0.54    inference(negated_conjecture,[],[f12])).
% 1.43/0.54  fof(f12,conjecture,(
% 1.43/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).
% 1.43/0.54  fof(f34,plain,(
% 1.43/0.54    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f445,plain,(
% 1.43/0.54    r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_17 | ~spl8_20 | ~spl8_21 | ~spl8_23 | ~spl8_25 | ~spl8_27 | ~spl8_40)),
% 1.43/0.54    inference(subsumption_resolution,[],[f444,f185])).
% 1.43/0.54  fof(f444,plain,(
% 1.43/0.54    ~r1_tarski(sK5,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_20 | ~spl8_21 | ~spl8_23 | ~spl8_25 | ~spl8_27 | ~spl8_40)),
% 1.43/0.54    inference(subsumption_resolution,[],[f443,f118])).
% 1.43/0.54  fof(f443,plain,(
% 1.43/0.54    ~r2_hidden(sK6,sK5) | ~r1_tarski(sK5,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_20 | ~spl8_21 | ~spl8_23 | ~spl8_25 | ~spl8_27 | ~spl8_40)),
% 1.43/0.54    inference(subsumption_resolution,[],[f442,f126])).
% 1.43/0.54  fof(f442,plain,(
% 1.43/0.54    ~m1_pre_topc(sK2,sK3) | ~r2_hidden(sK6,sK5) | ~r1_tarski(sK5,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_14 | ~spl8_16 | ~spl8_20 | ~spl8_21 | ~spl8_23 | ~spl8_25 | ~spl8_27 | ~spl8_40)),
% 1.43/0.54    inference(subsumption_resolution,[],[f436,f86])).
% 1.43/0.54  fof(f436,plain,(
% 1.43/0.54    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK3) | ~r2_hidden(sK6,sK5) | ~r1_tarski(sK5,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK6) | (~spl8_1 | spl8_2 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_14 | ~spl8_16 | ~spl8_20 | ~spl8_21 | ~spl8_23 | ~spl8_25 | ~spl8_27 | ~spl8_40)),
% 1.43/0.54    inference(resolution,[],[f380,f201])).
% 1.43/0.54  fof(f380,plain,(
% 1.43/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~r2_hidden(X1,sK5) | ~r1_tarski(sK5,u1_struct_0(X0)) | r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),X1) | ~r1_tmap_1(sK3,sK0,sK4,X1)) ) | (~spl8_1 | spl8_2 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_14 | ~spl8_16 | ~spl8_20 | ~spl8_23 | ~spl8_25 | ~spl8_27 | ~spl8_40)),
% 1.43/0.54    inference(subsumption_resolution,[],[f375,f379])).
% 1.43/0.54  fof(f375,plain,(
% 1.43/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_pre_topc(sK5,sK3) | ~r2_hidden(X1,sK5) | ~r1_tarski(sK5,u1_struct_0(X0)) | r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),X1) | ~r1_tmap_1(sK3,sK0,sK4,X1)) ) | (~spl8_1 | spl8_2 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_16 | ~spl8_20 | ~spl8_25 | ~spl8_27 | ~spl8_40)),
% 1.43/0.54    inference(resolution,[],[f371,f266])).
% 1.43/0.54  fof(f266,plain,(
% 1.43/0.54    ( ! [X2,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3) | ~r1_tmap_1(sK3,sK0,sK4,X3)) ) | (~spl8_1 | spl8_2 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_16 | ~spl8_20 | ~spl8_25 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f265,f64])).
% 1.43/0.54  fof(f64,plain,(
% 1.43/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f25])).
% 1.43/0.54  fof(f25,plain,(
% 1.43/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.43/0.54    inference(flattening,[],[f24])).
% 1.43/0.54  fof(f24,plain,(
% 1.43/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.43/0.54    inference(ennf_transformation,[],[f3])).
% 1.43/0.54  fof(f3,axiom,(
% 1.43/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.43/0.54  fof(f265,plain,(
% 1.43/0.54    ( ! [X2,X3,X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3) | ~r1_tmap_1(sK3,sK0,sK4,X3)) ) | (~spl8_1 | spl8_2 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_16 | ~spl8_20 | ~spl8_25 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f264,f102])).
% 1.43/0.54  fof(f264,plain,(
% 1.43/0.54    ( ! [X2,X3,X1] : (v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3) | ~r1_tmap_1(sK3,sK0,sK4,X3)) ) | (~spl8_1 | spl8_2 | ~spl8_8 | ~spl8_9 | ~spl8_16 | ~spl8_20 | ~spl8_25 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f263,f228])).
% 1.43/0.54  fof(f263,plain,(
% 1.43/0.54    ( ! [X2,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3) | ~r1_tmap_1(sK3,sK0,sK4,X3)) ) | (~spl8_1 | spl8_2 | ~spl8_8 | ~spl8_9 | ~spl8_16 | ~spl8_20 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f262,f78])).
% 1.43/0.54  fof(f262,plain,(
% 1.43/0.54    ( ! [X2,X3,X1] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3) | ~r1_tmap_1(sK3,sK0,sK4,X3)) ) | (spl8_2 | ~spl8_8 | ~spl8_9 | ~spl8_16 | ~spl8_20 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f261,f181])).
% 1.43/0.54  fof(f261,plain,(
% 1.43/0.54    ( ! [X2,X3,X1] : (~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3) | ~r1_tmap_1(sK3,sK0,sK4,X3)) ) | (spl8_2 | ~spl8_8 | ~spl8_9 | ~spl8_20 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f260,f197])).
% 1.43/0.54  fof(f260,plain,(
% 1.43/0.54    ( ! [X2,X3,X1] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3) | ~r1_tmap_1(sK3,sK0,sK4,X3)) ) | (spl8_2 | ~spl8_8 | ~spl8_9 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f259,f82])).
% 1.43/0.54  fof(f259,plain,(
% 1.43/0.54    ( ! [X2,X3,X1] : (v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3) | ~r1_tmap_1(sK3,sK0,sK4,X3)) ) | (~spl8_8 | ~spl8_9 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f258,f110])).
% 1.43/0.54  fof(f258,plain,(
% 1.43/0.54    ( ! [X2,X3,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3) | ~r1_tmap_1(sK3,sK0,sK4,X3)) ) | (~spl8_8 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f248,f106])).
% 1.43/0.54  fof(f248,plain,(
% 1.43/0.54    ( ! [X2,X3,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X3) | ~r1_tmap_1(sK3,sK0,sK4,X3)) ) | ~spl8_27),
% 1.43/0.54    inference(resolution,[],[f238,f70])).
% 1.43/0.54  fof(f70,plain,(
% 1.43/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | v2_struct_0(X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X6,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6)) )),
% 1.43/0.54    inference(equality_resolution,[],[f59])).
% 1.43/0.54  fof(f59,plain,(
% 1.43/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X5,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | X5 != X6 | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f19])).
% 1.43/0.54  fof(f434,plain,(
% 1.43/0.54    ~spl8_50 | spl8_30 | ~spl8_49),
% 1.43/0.54    inference(avatar_split_clause,[],[f430,f424,f275,f432])).
% 1.43/0.54  fof(f275,plain,(
% 1.43/0.54    spl8_30 <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 1.43/0.54  fof(f430,plain,(
% 1.43/0.54    ~r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) | (spl8_30 | ~spl8_49)),
% 1.43/0.54    inference(superposition,[],[f276,f425])).
% 1.43/0.54  fof(f276,plain,(
% 1.43/0.54    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | spl8_30),
% 1.43/0.54    inference(avatar_component_clause,[],[f275])).
% 1.43/0.54  fof(f426,plain,(
% 1.43/0.54    spl8_49 | ~spl8_1 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_13 | ~spl8_14 | ~spl8_25 | ~spl8_27 | ~spl8_42),
% 1.43/0.54    inference(avatar_split_clause,[],[f422,f395,f237,f227,f129,f125,f109,f105,f101,f97,f93,f89,f77,f424])).
% 1.43/0.54  fof(f89,plain,(
% 1.43/0.54    spl8_4 <=> v2_struct_0(sK1)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.43/0.54  fof(f93,plain,(
% 1.43/0.54    spl8_5 <=> v2_pre_topc(sK1)),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.43/0.54  fof(f395,plain,(
% 1.43/0.54    spl8_42 <=> k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 1.43/0.54  fof(f422,plain,(
% 1.43/0.54    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2) | (~spl8_1 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_13 | ~spl8_14 | ~spl8_25 | ~spl8_27 | ~spl8_42)),
% 1.43/0.54    inference(forward_demodulation,[],[f421,f396])).
% 1.43/0.54  fof(f396,plain,(
% 1.43/0.54    k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) | ~spl8_42),
% 1.43/0.54    inference(avatar_component_clause,[],[f395])).
% 1.43/0.54  fof(f421,plain,(
% 1.43/0.54    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) | (~spl8_1 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_13 | ~spl8_14 | ~spl8_25 | ~spl8_27)),
% 1.43/0.54    inference(resolution,[],[f363,f126])).
% 1.43/0.54  fof(f363,plain,(
% 1.43/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (~spl8_1 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_14 | ~spl8_25 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f362,f102])).
% 1.43/0.54  fof(f362,plain,(
% 1.43/0.54    ( ! [X0] : (v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (~spl8_1 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_9 | ~spl8_14 | ~spl8_25 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f361,f228])).
% 1.43/0.54  fof(f361,plain,(
% 1.43/0.54    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (~spl8_1 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_9 | ~spl8_14 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f360,f78])).
% 1.43/0.54  fof(f360,plain,(
% 1.43/0.54    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_9 | ~spl8_14 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f359,f110])).
% 1.43/0.54  fof(f359,plain,(
% 1.43/0.54    ( ! [X0] : (~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_14 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f358,f106])).
% 1.43/0.54  fof(f358,plain,(
% 1.43/0.54    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_14 | ~spl8_27)),
% 1.43/0.54    inference(resolution,[],[f166,f238])).
% 1.43/0.54  fof(f166,plain,(
% 1.43/0.54    ( ! [X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2))) ) | (spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_14)),
% 1.43/0.54    inference(subsumption_resolution,[],[f165,f161])).
% 1.43/0.54  fof(f161,plain,(
% 1.43/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK1)) ) | (~spl8_5 | ~spl8_6 | ~spl8_14)),
% 1.43/0.54    inference(subsumption_resolution,[],[f160,f94])).
% 1.43/0.54  fof(f94,plain,(
% 1.43/0.54    v2_pre_topc(sK1) | ~spl8_5),
% 1.43/0.54    inference(avatar_component_clause,[],[f93])).
% 1.43/0.54  fof(f160,plain,(
% 1.43/0.54    ( ! [X0] : (~v2_pre_topc(sK1) | ~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK1)) ) | (~spl8_6 | ~spl8_14)),
% 1.43/0.54    inference(subsumption_resolution,[],[f146,f98])).
% 1.43/0.54  fof(f146,plain,(
% 1.43/0.54    ( ! [X0] : (~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK1)) ) | ~spl8_14),
% 1.43/0.54    inference(resolution,[],[f130,f67])).
% 1.43/0.54  fof(f67,plain,(
% 1.43/0.54    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f30])).
% 1.43/0.54  fof(f30,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.43/0.54    inference(flattening,[],[f29])).
% 1.43/0.54  fof(f29,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.43/0.54    inference(ennf_transformation,[],[f11])).
% 1.43/0.54  fof(f11,axiom,(
% 1.43/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.43/0.54  fof(f165,plain,(
% 1.43/0.54    ( ! [X2,X3,X1] : (v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2))) ) | (spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_14)),
% 1.43/0.54    inference(subsumption_resolution,[],[f164,f90])).
% 1.43/0.54  fof(f90,plain,(
% 1.43/0.54    ~v2_struct_0(sK1) | spl8_4),
% 1.43/0.54    inference(avatar_component_clause,[],[f89])).
% 1.43/0.54  fof(f164,plain,(
% 1.43/0.54    ( ! [X2,X3,X1] : (v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK1) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2))) ) | (~spl8_5 | ~spl8_6 | ~spl8_14)),
% 1.43/0.54    inference(subsumption_resolution,[],[f163,f98])).
% 1.43/0.54  fof(f163,plain,(
% 1.43/0.54    ( ! [X2,X3,X1] : (~l1_pre_topc(sK1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK1) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2))) ) | (~spl8_5 | ~spl8_14)),
% 1.43/0.54    inference(subsumption_resolution,[],[f148,f94])).
% 1.43/0.54  fof(f148,plain,(
% 1.43/0.54    ( ! [X2,X3,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK1) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2))) ) | ~spl8_14),
% 1.43/0.54    inference(resolution,[],[f130,f57])).
% 1.43/0.54  fof(f57,plain,(
% 1.43/0.54    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 1.43/0.54    inference(cnf_transformation,[],[f17])).
% 1.43/0.54  fof(f17,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.43/0.54    inference(flattening,[],[f16])).
% 1.43/0.54  fof(f16,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.43/0.54    inference(ennf_transformation,[],[f8])).
% 1.43/0.54  fof(f8,axiom,(
% 1.43/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.43/0.54  fof(f397,plain,(
% 1.43/0.54    spl8_42 | ~spl8_1 | spl8_2 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_13 | ~spl8_16 | ~spl8_20 | ~spl8_25 | ~spl8_27),
% 1.43/0.54    inference(avatar_split_clause,[],[f350,f237,f227,f196,f180,f125,f109,f105,f101,f81,f77,f395])).
% 1.43/0.54  fof(f350,plain,(
% 1.43/0.54    k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) | (~spl8_1 | spl8_2 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_13 | ~spl8_16 | ~spl8_20 | ~spl8_25 | ~spl8_27)),
% 1.43/0.54    inference(resolution,[],[f257,f126])).
% 1.43/0.54  fof(f257,plain,(
% 1.43/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (~spl8_1 | spl8_2 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_16 | ~spl8_20 | ~spl8_25 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f256,f82])).
% 1.43/0.54  fof(f256,plain,(
% 1.43/0.54    ( ! [X0] : (v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (~spl8_1 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_16 | ~spl8_20 | ~spl8_25 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f255,f228])).
% 1.43/0.54  fof(f255,plain,(
% 1.43/0.54    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (~spl8_1 | spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_16 | ~spl8_20 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f254,f78])).
% 1.43/0.54  fof(f254,plain,(
% 1.43/0.54    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_16 | ~spl8_20 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f253,f110])).
% 1.43/0.54  fof(f253,plain,(
% 1.43/0.54    ( ! [X0] : (~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (spl8_7 | ~spl8_8 | ~spl8_16 | ~spl8_20 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f252,f106])).
% 1.43/0.54  fof(f252,plain,(
% 1.43/0.54    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (spl8_7 | ~spl8_16 | ~spl8_20 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f251,f102])).
% 1.43/0.54  fof(f251,plain,(
% 1.43/0.54    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (~spl8_16 | ~spl8_20 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f250,f181])).
% 1.43/0.54  fof(f250,plain,(
% 1.43/0.54    ( ! [X0] : (~l1_pre_topc(sK3) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (~spl8_20 | ~spl8_27)),
% 1.43/0.54    inference(subsumption_resolution,[],[f247,f197])).
% 1.43/0.54  fof(f247,plain,(
% 1.43/0.54    ( ! [X0] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | ~spl8_27),
% 1.43/0.54    inference(resolution,[],[f238,f66])).
% 1.43/0.54  fof(f66,plain,(
% 1.43/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 1.43/0.54    inference(cnf_transformation,[],[f28])).
% 1.43/0.54  fof(f28,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.43/0.54    inference(flattening,[],[f27])).
% 1.43/0.54  fof(f27,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.43/0.54    inference(ennf_transformation,[],[f7])).
% 1.43/0.54  fof(f7,axiom,(
% 1.43/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.43/0.54  fof(f372,plain,(
% 1.43/0.54    spl8_40 | ~spl8_37),
% 1.43/0.54    inference(avatar_split_clause,[],[f352,f338,f370])).
% 1.43/0.54  fof(f338,plain,(
% 1.43/0.54    spl8_37 <=> r1_tarski(sK5,u1_struct_0(sK3))),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 1.43/0.54  fof(f352,plain,(
% 1.43/0.54    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~spl8_37),
% 1.43/0.54    inference(resolution,[],[f339,f62])).
% 1.43/0.54  fof(f62,plain,(
% 1.43/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.43/0.54    inference(cnf_transformation,[],[f2])).
% 1.43/0.54  fof(f2,axiom,(
% 1.43/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.43/0.54  fof(f339,plain,(
% 1.43/0.54    r1_tarski(sK5,u1_struct_0(sK3)) | ~spl8_37),
% 1.43/0.54    inference(avatar_component_clause,[],[f338])).
% 1.43/0.54  fof(f340,plain,(
% 1.43/0.54    spl8_37 | ~spl8_17 | ~spl8_33),
% 1.43/0.54    inference(avatar_split_clause,[],[f332,f308,f184,f338])).
% 1.43/0.54  fof(f308,plain,(
% 1.43/0.54    spl8_33 <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 1.43/0.54  fof(f332,plain,(
% 1.43/0.54    r1_tarski(sK5,u1_struct_0(sK3)) | (~spl8_17 | ~spl8_33)),
% 1.43/0.54    inference(resolution,[],[f309,f208])).
% 1.43/0.54  fof(f208,plain,(
% 1.43/0.54    ( ! [X0] : (~r1_tarski(u1_struct_0(sK2),X0) | r1_tarski(sK5,X0)) ) | ~spl8_17),
% 1.43/0.54    inference(resolution,[],[f185,f61])).
% 1.43/0.54  fof(f61,plain,(
% 1.43/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f23])).
% 1.43/0.54  fof(f23,plain,(
% 1.43/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.43/0.54    inference(flattening,[],[f22])).
% 1.43/0.54  fof(f22,plain,(
% 1.43/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.43/0.54    inference(ennf_transformation,[],[f1])).
% 1.43/0.54  fof(f1,axiom,(
% 1.43/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.43/0.54  fof(f309,plain,(
% 1.43/0.54    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl8_33),
% 1.43/0.54    inference(avatar_component_clause,[],[f308])).
% 1.43/0.54  fof(f310,plain,(
% 1.43/0.54    spl8_33 | ~spl8_28),
% 1.43/0.54    inference(avatar_split_clause,[],[f295,f268,f308])).
% 1.43/0.54  fof(f268,plain,(
% 1.43/0.54    spl8_28 <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.43/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 1.43/0.54  fof(f295,plain,(
% 1.43/0.54    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl8_28),
% 1.43/0.54    inference(resolution,[],[f269,f63])).
% 1.43/0.54  fof(f63,plain,(
% 1.43/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f2])).
% 1.43/0.54  fof(f269,plain,(
% 1.43/0.54    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~spl8_28),
% 1.43/0.54    inference(avatar_component_clause,[],[f268])).
% 1.43/0.54  fof(f277,plain,(
% 1.43/0.54    ~spl8_29 | ~spl8_30),
% 1.43/0.54    inference(avatar_split_clause,[],[f74,f275,f272])).
% 1.43/0.54  fof(f74,plain,(
% 1.43/0.54    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 1.43/0.54    inference(forward_demodulation,[],[f35,f40])).
% 1.43/0.54  fof(f35,plain,(
% 1.43/0.54    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f270,plain,(
% 1.43/0.54    spl8_28 | ~spl8_6 | ~spl8_13 | ~spl8_14),
% 1.43/0.54    inference(avatar_split_clause,[],[f151,f129,f125,f97,f268])).
% 1.43/0.54  fof(f151,plain,(
% 1.43/0.54    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | (~spl8_6 | ~spl8_13 | ~spl8_14)),
% 1.43/0.54    inference(subsumption_resolution,[],[f140,f149])).
% 1.43/0.54  fof(f149,plain,(
% 1.43/0.54    l1_pre_topc(sK3) | (~spl8_6 | ~spl8_14)),
% 1.43/0.54    inference(subsumption_resolution,[],[f144,f98])).
% 1.43/0.54  fof(f144,plain,(
% 1.43/0.54    ~l1_pre_topc(sK1) | l1_pre_topc(sK3) | ~spl8_14),
% 1.43/0.54    inference(resolution,[],[f130,f69])).
% 1.43/0.54  fof(f69,plain,(
% 1.43/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f33])).
% 1.43/0.54  fof(f33,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.43/0.54    inference(ennf_transformation,[],[f5])).
% 1.43/0.54  fof(f5,axiom,(
% 1.43/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.43/0.54  fof(f140,plain,(
% 1.43/0.54    ~l1_pre_topc(sK3) | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~spl8_13),
% 1.43/0.54    inference(resolution,[],[f126,f65])).
% 1.43/0.54  fof(f65,plain,(
% 1.43/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.43/0.54    inference(cnf_transformation,[],[f26])).
% 1.43/0.54  fof(f26,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.43/0.54    inference(ennf_transformation,[],[f9])).
% 1.43/0.54  fof(f9,axiom,(
% 1.43/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.43/0.54  fof(f239,plain,(
% 1.43/0.54    spl8_27),
% 1.43/0.54    inference(avatar_split_clause,[],[f45,f237])).
% 1.43/0.54  fof(f45,plain,(
% 1.43/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f229,plain,(
% 1.43/0.54    spl8_25),
% 1.43/0.54    inference(avatar_split_clause,[],[f44,f227])).
% 1.43/0.54  fof(f44,plain,(
% 1.43/0.54    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f212,plain,(
% 1.43/0.54    spl8_23),
% 1.43/0.54    inference(avatar_split_clause,[],[f42,f210])).
% 1.43/0.54  fof(f42,plain,(
% 1.43/0.54    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f202,plain,(
% 1.43/0.54    spl8_21),
% 1.43/0.54    inference(avatar_split_clause,[],[f73,f200])).
% 1.43/0.54  fof(f73,plain,(
% 1.43/0.54    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.43/0.54    inference(forward_demodulation,[],[f36,f40])).
% 1.43/0.54  fof(f36,plain,(
% 1.43/0.54    m1_subset_1(sK7,u1_struct_0(sK2))),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f198,plain,(
% 1.43/0.54    spl8_20 | ~spl8_5 | ~spl8_6 | ~spl8_14),
% 1.43/0.54    inference(avatar_split_clause,[],[f156,f129,f97,f93,f196])).
% 1.43/0.54  fof(f156,plain,(
% 1.43/0.54    v2_pre_topc(sK3) | (~spl8_5 | ~spl8_6 | ~spl8_14)),
% 1.43/0.54    inference(subsumption_resolution,[],[f155,f94])).
% 1.43/0.54  fof(f155,plain,(
% 1.43/0.54    ~v2_pre_topc(sK1) | v2_pre_topc(sK3) | (~spl8_6 | ~spl8_14)),
% 1.43/0.54    inference(subsumption_resolution,[],[f145,f98])).
% 1.43/0.54  fof(f145,plain,(
% 1.43/0.54    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_pre_topc(sK3) | ~spl8_14),
% 1.43/0.54    inference(resolution,[],[f130,f68])).
% 1.43/0.54  fof(f68,plain,(
% 1.43/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f32])).
% 1.43/0.54  fof(f32,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.43/0.54    inference(flattening,[],[f31])).
% 1.43/0.54  fof(f31,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.43/0.54    inference(ennf_transformation,[],[f4])).
% 1.43/0.54  fof(f4,axiom,(
% 1.43/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.43/0.54  fof(f194,plain,(
% 1.43/0.54    spl8_19),
% 1.43/0.54    inference(avatar_split_clause,[],[f41,f192])).
% 1.43/0.54  fof(f41,plain,(
% 1.43/0.54    m1_subset_1(sK6,u1_struct_0(sK3))),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f186,plain,(
% 1.43/0.54    spl8_17),
% 1.43/0.54    inference(avatar_split_clause,[],[f39,f184])).
% 1.43/0.54  fof(f39,plain,(
% 1.43/0.54    r1_tarski(sK5,u1_struct_0(sK2))),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f182,plain,(
% 1.43/0.54    spl8_16 | ~spl8_6 | ~spl8_14),
% 1.43/0.54    inference(avatar_split_clause,[],[f149,f129,f97,f180])).
% 1.43/0.54  fof(f131,plain,(
% 1.43/0.54    spl8_14),
% 1.43/0.54    inference(avatar_split_clause,[],[f48,f129])).
% 1.43/0.54  fof(f48,plain,(
% 1.43/0.54    m1_pre_topc(sK3,sK1)),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f127,plain,(
% 1.43/0.54    spl8_13),
% 1.43/0.54    inference(avatar_split_clause,[],[f46,f125])).
% 1.43/0.54  fof(f46,plain,(
% 1.43/0.54    m1_pre_topc(sK2,sK3)),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f119,plain,(
% 1.43/0.54    spl8_11),
% 1.43/0.54    inference(avatar_split_clause,[],[f38,f117])).
% 1.43/0.54  fof(f38,plain,(
% 1.43/0.54    r2_hidden(sK6,sK5)),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f115,plain,(
% 1.43/0.54    spl8_10),
% 1.43/0.54    inference(avatar_split_clause,[],[f37,f113])).
% 1.43/0.54  fof(f37,plain,(
% 1.43/0.54    v3_pre_topc(sK5,sK1)),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f111,plain,(
% 1.43/0.54    spl8_9),
% 1.43/0.54    inference(avatar_split_clause,[],[f56,f109])).
% 1.43/0.54  fof(f56,plain,(
% 1.43/0.54    l1_pre_topc(sK0)),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f107,plain,(
% 1.43/0.54    spl8_8),
% 1.43/0.54    inference(avatar_split_clause,[],[f55,f105])).
% 1.43/0.54  fof(f55,plain,(
% 1.43/0.54    v2_pre_topc(sK0)),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f103,plain,(
% 1.43/0.54    ~spl8_7),
% 1.43/0.54    inference(avatar_split_clause,[],[f54,f101])).
% 1.43/0.54  fof(f54,plain,(
% 1.43/0.54    ~v2_struct_0(sK0)),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f99,plain,(
% 1.43/0.54    spl8_6),
% 1.43/0.54    inference(avatar_split_clause,[],[f53,f97])).
% 1.43/0.54  fof(f53,plain,(
% 1.43/0.54    l1_pre_topc(sK1)),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f95,plain,(
% 1.43/0.54    spl8_5),
% 1.43/0.54    inference(avatar_split_clause,[],[f52,f93])).
% 1.43/0.54  fof(f52,plain,(
% 1.43/0.54    v2_pre_topc(sK1)),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f91,plain,(
% 1.43/0.54    ~spl8_4),
% 1.43/0.54    inference(avatar_split_clause,[],[f51,f89])).
% 1.43/0.54  fof(f51,plain,(
% 1.43/0.54    ~v2_struct_0(sK1)),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f87,plain,(
% 1.43/0.54    ~spl8_3),
% 1.43/0.54    inference(avatar_split_clause,[],[f49,f85])).
% 1.43/0.54  fof(f49,plain,(
% 1.43/0.54    ~v2_struct_0(sK2)),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f83,plain,(
% 1.43/0.54    ~spl8_2),
% 1.43/0.54    inference(avatar_split_clause,[],[f47,f81])).
% 1.43/0.54  fof(f47,plain,(
% 1.43/0.54    ~v2_struct_0(sK3)),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  fof(f79,plain,(
% 1.43/0.54    spl8_1),
% 1.43/0.54    inference(avatar_split_clause,[],[f43,f77])).
% 1.43/0.54  fof(f43,plain,(
% 1.43/0.54    v1_funct_1(sK4)),
% 1.43/0.54    inference(cnf_transformation,[],[f15])).
% 1.43/0.54  % SZS output end Proof for theBenchmark
% 1.43/0.54  % (25590)------------------------------
% 1.43/0.54  % (25590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (25590)Termination reason: Refutation
% 1.43/0.54  
% 1.43/0.54  % (25590)Memory used [KB]: 6524
% 1.43/0.54  % (25590)Time elapsed: 0.141 s
% 1.43/0.54  % (25590)------------------------------
% 1.43/0.54  % (25590)------------------------------
% 1.43/0.54  % (25597)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.43/0.55  % (25586)Success in time 0.191 s
%------------------------------------------------------------------------------
