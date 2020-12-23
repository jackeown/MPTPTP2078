%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1756+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:29 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 305 expanded)
%              Number of leaves         :   24 ( 104 expanded)
%              Depth                    :   24
%              Number of atoms          : 1042 (2878 expanded)
%              Number of equality atoms :   13 (  99 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f63,f67,f71,f75,f79,f83,f91,f95,f99,f103,f107,f120,f124,f143,f148,f166,f181])).

fof(f181,plain,
    ( spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | spl7_19
    | ~ spl7_20
    | ~ spl7_21 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | spl7_19
    | ~ spl7_20
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f179,f139])).

fof(f139,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl7_19
  <=> r1_tmap_1(sK1,sK0,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f179,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f178,f70])).

fof(f70,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl7_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f178,plain,
    ( ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f177,f147])).

fof(f147,plain,
    ( m1_connsp_2(sK4,sK1,sK5)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl7_21
  <=> m1_connsp_2(sK4,sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f177,plain,
    ( ~ m1_connsp_2(sK4,sK1,sK5)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f176,f94])).

fof(f94,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_13
  <=> r1_tarski(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f176,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ m1_connsp_2(sK4,sK1,sK5)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f175,f102])).

fof(f102,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl7_15
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f175,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ m1_connsp_2(sK4,sK1,sK5)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f174,f98])).

fof(f98,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl7_14
  <=> m1_subset_1(sK5,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f174,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ m1_connsp_2(sK4,sK1,sK5)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f173,f66])).

fof(f66,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl7_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f173,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ m1_connsp_2(sK4,sK1,sK5)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f172,f90])).

fof(f90,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl7_12
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f172,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ m1_connsp_2(sK4,sK1,sK5)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f171,f46])).

fof(f46,plain,
    ( ~ v2_struct_0(sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl7_1
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f171,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ m1_connsp_2(sK4,sK1,sK5)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f170,f123])).

fof(f123,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl7_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f170,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ m1_connsp_2(sK4,sK1,sK5)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f169,f119])).

fof(f119,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl7_17
  <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f169,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ m1_connsp_2(sK4,sK1,sK5)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_16
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f168,f50])).

fof(f50,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl7_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f168,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ m1_connsp_2(sK4,sK1,sK5)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_16
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f167,f74])).

fof(f74,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl7_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f167,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ m1_connsp_2(sK4,sK1,sK5)
    | ~ v2_pre_topc(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_16
    | ~ spl7_20 ),
    inference(resolution,[],[f116,f149])).

fof(f149,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl7_20
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f116,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X4)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK1)
        | v2_struct_0(X1)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ r1_tarski(sK4,u1_struct_0(X3))
        | ~ m1_connsp_2(sK4,sK1,X4)
        | ~ v2_pre_topc(X1)
        | r1_tmap_1(sK1,X1,X2,X4) )
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f115,f62])).

fof(f62,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl7_5
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f115,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK1)
        | v2_struct_0(X1)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ r1_tarski(sK4,u1_struct_0(X3))
        | ~ m1_connsp_2(sK4,sK1,X4)
        | ~ r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X4)
        | r1_tmap_1(sK1,X1,X2,X4) )
    | spl7_3
    | ~ spl7_4
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f114,f58])).

fof(f58,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl7_4
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f114,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK1)
        | v2_struct_0(X1)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ r1_tarski(sK4,u1_struct_0(X3))
        | ~ m1_connsp_2(sK4,sK1,X4)
        | ~ r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X4)
        | r1_tmap_1(sK1,X1,X2,X4) )
    | spl7_3
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f109,f54])).

fof(f54,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl7_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f109,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK1)
        | v2_struct_0(X1)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ r1_tarski(sK4,u1_struct_0(X3))
        | ~ m1_connsp_2(sK4,sK1,X4)
        | ~ r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X4)
        | r1_tmap_1(sK1,X1,X2,X4) )
    | ~ spl7_16 ),
    inference(resolution,[],[f106,f39])).

fof(f39,plain,(
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
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
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
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X5)
      | X5 != X6
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
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
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

fof(f106,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_16
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f166,plain,
    ( spl7_20
    | spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f165,f122,f118,f101,f97,f89,f73,f69,f65,f61,f57,f53,f49,f45,f141])).

fof(f165,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f43,f161])).

fof(f161,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f160,f46])).

fof(f160,plain,
    ( v2_struct_0(sK3)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f159,f98])).

fof(f159,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | v2_struct_0(sK3)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f155,f90])).

fof(f155,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | v2_struct_0(sK3)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(resolution,[],[f134,f102])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | v2_struct_0(X0)
        | ~ r1_tmap_1(sK1,sK0,sK2,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) )
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f133,f66])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(sK1,sK0,sK2,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) )
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f132,f119])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(sK1,sK0,sK2,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) )
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f131,f50])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(sK1,sK0,sK2,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) )
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f130,f62])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(sK1,sK0,sK2,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) )
    | spl7_3
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f129,f58])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(sK1,sK0,sK2,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) )
    | spl7_3
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f128,f54])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(sK1,sK0,sK2,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) )
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f127,f74])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(sK1,sK0,sK2,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) )
    | ~ spl7_7
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f125,f70])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tmap_1(sK1,sK0,sK2,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) )
    | ~ spl7_18 ),
    inference(resolution,[],[f123,f40])).

fof(f40,plain,(
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
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
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
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | X4 != X5
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f43,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(forward_demodulation,[],[f14,f20])).

fof(f20,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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

fof(f14,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f7])).

fof(f148,plain,
    ( spl7_21
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f136,f105,f97,f81,f77,f61,f57,f53,f146])).

fof(f77,plain,
    ( spl7_9
  <=> v3_pre_topc(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f81,plain,
    ( spl7_10
  <=> r2_hidden(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f136,plain,
    ( m1_connsp_2(sK4,sK1,sK5)
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f135,f82])).

fof(f82,plain,
    ( r2_hidden(sK5,sK4)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f135,plain,
    ( ~ r2_hidden(sK5,sK4)
    | m1_connsp_2(sK4,sK1,sK5)
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(resolution,[],[f113,f98])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,sK4)
        | m1_connsp_2(sK4,sK1,X0) )
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f112,f78])).

fof(f78,plain,
    ( v3_pre_topc(sK4,sK1)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v3_pre_topc(sK4,sK1)
        | ~ r2_hidden(X0,sK4)
        | m1_connsp_2(sK4,sK1,X0) )
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f111,f54])).

fof(f111,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v3_pre_topc(sK4,sK1)
        | ~ r2_hidden(X0,sK4)
        | m1_connsp_2(sK4,sK1,X0) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f110,f62])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v3_pre_topc(sK4,sK1)
        | ~ r2_hidden(X0,sK4)
        | m1_connsp_2(sK4,sK1,X0) )
    | ~ spl7_4
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f108,f58])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v3_pre_topc(sK4,sK1)
        | ~ r2_hidden(X0,sK4)
        | m1_connsp_2(sK4,sK1,X0) )
    | ~ spl7_16 ),
    inference(resolution,[],[f106,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f143,plain,
    ( ~ spl7_19
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f42,f141,f138])).

fof(f42,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(forward_demodulation,[],[f15,f20])).

fof(f15,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f7])).

fof(f124,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f27,f122])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f7])).

fof(f120,plain,(
    spl7_17 ),
    inference(avatar_split_clause,[],[f26,f118])).

fof(f26,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f107,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f22,f105])).

fof(f22,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f7])).

fof(f103,plain,(
    spl7_15 ),
    inference(avatar_split_clause,[],[f41,f101])).

fof(f41,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f16,f20])).

fof(f16,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f99,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f21,f97])).

fof(f21,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f95,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f19,f93])).

fof(f19,plain,(
    r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f91,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f24,f89])).

fof(f24,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f83,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f18,f81])).

fof(f18,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f7])).

fof(f79,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f17,f77])).

fof(f17,plain,(
    v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f75,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f33,f73])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f71,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f32,f69])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f67,plain,(
    ~ spl7_6 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f63,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f59,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f29,f57])).

fof(f29,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f28,f53])).

fof(f28,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f51,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f47,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
