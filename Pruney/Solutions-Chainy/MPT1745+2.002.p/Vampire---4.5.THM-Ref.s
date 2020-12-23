%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 329 expanded)
%              Number of leaves         :   37 ( 130 expanded)
%              Depth                    :   13
%              Number of atoms          : 1162 (2909 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   32 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f232,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f56,f60,f64,f68,f72,f76,f80,f84,f88,f92,f96,f100,f104,f108,f112,f116,f120,f124,f128,f132,f145,f149,f153,f163,f172,f190,f194,f202,f216,f223,f226])).

fof(f226,plain,
    ( ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_18
    | spl8_19
    | ~ spl8_36 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_18
    | spl8_19
    | ~ spl8_36 ),
    inference(unit_resulting_resolution,[],[f59,f55,f63,f67,f95,f103,f111,f119,f123,f222])).

fof(f222,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,X1,X2)
        | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2)
        | v2_struct_0(X0) )
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl8_36
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,X1,X2)
        | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f123,plain,
    ( ~ r1_tmap_1(sK2,sK1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),sK5)
    | spl8_19 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_19
  <=> r1_tmap_1(sK2,sK1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f119,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl8_18
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f111,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl8_16
  <=> v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f103,plain,
    ( r1_tmap_1(sK2,sK0,sK3,sK5)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl8_14
  <=> r1_tmap_1(sK2,sK0,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f95,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl8_12
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f67,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl8_5
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f63,plain,
    ( v2_pre_topc(sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl8_4
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f55,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl8_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f59,plain,
    ( ~ v2_struct_0(sK2)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl8_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f223,plain,
    ( spl8_36
    | ~ spl8_26
    | ~ spl8_28
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f219,f214,f161,f151,f221])).

fof(f151,plain,
    ( spl8_26
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,X0)
        | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f161,plain,
    ( spl8_28
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f214,plain,
    ( spl8_35
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,X1,X2)
        | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2)
        | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f219,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,X1,X2)
        | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2)
        | v2_struct_0(X0) )
    | ~ spl8_26
    | ~ spl8_28
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f218,f162])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f161])).

fof(f218,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,X1,X2)
        | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2)
        | v2_struct_0(X0)
        | v1_xboole_0(u1_struct_0(X0)) )
    | ~ spl8_26
    | ~ spl8_35 ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,X1,X2)
        | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2)
        | v2_struct_0(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v1_xboole_0(u1_struct_0(X0)) )
    | ~ spl8_26
    | ~ spl8_35 ),
    inference(resolution,[],[f215,f152])).

fof(f152,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,X0)
        | v1_xboole_0(X0) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f151])).

fof(f215,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,X1,X2)
        | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2)
        | v2_struct_0(X0) )
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f214])).

fof(f216,plain,
    ( spl8_35
    | ~ spl8_1
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_15
    | ~ spl8_17
    | ~ spl8_32
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f212,f200,f188,f114,f106,f90,f86,f82,f78,f74,f70,f50,f214])).

fof(f50,plain,
    ( spl8_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f70,plain,
    ( spl8_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f74,plain,
    ( spl8_7
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f78,plain,
    ( spl8_8
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f82,plain,
    ( spl8_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f86,plain,
    ( spl8_10
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f90,plain,
    ( spl8_11
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f106,plain,
    ( spl8_15
  <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f114,plain,
    ( spl8_17
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f188,plain,
    ( spl8_32
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f200,plain,
    ( spl8_34
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ v2_pre_topc(X0)
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
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f212,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,X1,X2)
        | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2)
        | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0)) )
    | ~ spl8_1
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_15
    | ~ spl8_17
    | ~ spl8_32
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f211,f75])).

fof(f75,plain,
    ( v2_pre_topc(sK1)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f211,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,X1,X2)
        | ~ v2_pre_topc(sK1)
        | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2)
        | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0)) )
    | ~ spl8_1
    | spl8_6
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_15
    | ~ spl8_17
    | ~ spl8_32
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f210,f71])).

fof(f71,plain,
    ( ~ v2_struct_0(sK1)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f210,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(sK1)
        | ~ r1_tmap_1(X0,sK0,X1,X2)
        | ~ v2_pre_topc(sK1)
        | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2)
        | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0)) )
    | ~ spl8_1
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_15
    | ~ spl8_17
    | ~ spl8_32
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f209,f115])).

fof(f115,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f114])).

fof(f209,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(sK1)
        | ~ r1_tmap_1(X0,sK0,X1,X2)
        | ~ v2_pre_topc(sK1)
        | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2)
        | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0)) )
    | ~ spl8_1
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_15
    | ~ spl8_32
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f208,f107])).

fof(f107,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f106])).

fof(f208,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(sK1)
        | ~ r1_tmap_1(X0,sK0,X1,X2)
        | ~ v2_pre_topc(sK1)
        | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2)
        | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0)) )
    | ~ spl8_1
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_32
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f207,f51])).

fof(f51,plain,
    ( v1_funct_1(sK4)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f207,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(sK1)
        | ~ r1_tmap_1(X0,sK0,X1,X2)
        | ~ v2_pre_topc(sK1)
        | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2)
        | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0)) )
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_32
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f206,f91])).

fof(f91,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f206,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(sK1)
        | ~ r1_tmap_1(X0,sK0,X1,X2)
        | ~ v2_pre_topc(sK1)
        | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2)
        | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0)) )
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_32
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f205,f87])).

fof(f87,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f205,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(sK1)
        | ~ r1_tmap_1(X0,sK0,X1,X2)
        | ~ v2_pre_topc(sK1)
        | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2)
        | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0)) )
    | ~ spl8_8
    | spl8_9
    | ~ spl8_32
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f204,f83])).

fof(f83,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f204,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(sK1)
        | ~ r1_tmap_1(X0,sK0,X1,X2)
        | ~ v2_pre_topc(sK1)
        | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2)
        | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0)) )
    | ~ spl8_8
    | ~ spl8_32
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f203,f79])).

fof(f79,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f203,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | v2_struct_0(sK1)
        | ~ r1_tmap_1(X0,sK0,X1,X2)
        | ~ v2_pre_topc(sK1)
        | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2)
        | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0)) )
    | ~ spl8_32
    | ~ spl8_34 ),
    inference(resolution,[],[f201,f189])).

fof(f189,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK0,sK1,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f188])).

% (16141)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f201,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5))
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
        | ~ v2_pre_topc(X0)
        | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) )
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f200])).

fof(f202,plain,
    ( spl8_34
    | ~ spl8_26
    | ~ spl8_28
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f198,f192,f161,f151,f200])).

fof(f192,plain,
    ( spl8_33
  <=> ! [X1,X3,X5,X0,X2,X4] :
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
        | ~ m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2))
        | ~ r1_tmap_1(X1,X2,X3,X5)
        | ~ r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5))
        | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f198,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v2_pre_topc(X0)
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
        | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) )
    | ~ spl8_26
    | ~ spl8_28
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f197,f162])).

fof(f197,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v2_pre_topc(X0)
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
        | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
        | v1_xboole_0(u1_struct_0(X1)) )
    | ~ spl8_26
    | ~ spl8_33 ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v2_pre_topc(X0)
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
        | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ m1_subset_1(X5,u1_struct_0(X1))
        | v1_xboole_0(u1_struct_0(X1)) )
    | ~ spl8_26
    | ~ spl8_33 ),
    inference(resolution,[],[f193,f152])).

fof(f193,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
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
        | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) )
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f192])).

fof(f194,plain,(
    spl8_33 ),
    inference(avatar_split_clause,[],[f48,f192])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
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
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2))
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

fof(f190,plain,
    ( spl8_32
    | ~ spl8_1
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_17
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f186,f170,f114,f106,f98,f90,f86,f82,f78,f74,f70,f50,f188])).

fof(f98,plain,
    ( spl8_13
  <=> v5_pre_topc(sK4,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f170,plain,
    ( spl8_30
  <=> ! [X1,X3,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
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
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0) )
    | ~ spl8_1
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_17
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f185,f71])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | v2_struct_0(sK1) )
    | ~ spl8_1
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_17
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f184,f115])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | v2_struct_0(sK1) )
    | ~ spl8_1
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f183,f107])).

fof(f183,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | v2_struct_0(sK1) )
    | ~ spl8_1
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f182,f51])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | v2_struct_0(sK1) )
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f181,f91])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | v2_struct_0(sK1) )
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_10
    | ~ spl8_13
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f180,f87])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | v2_struct_0(sK1) )
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_13
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f179,f83])).

fof(f179,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | v2_struct_0(sK1) )
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_13
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f178,f79])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | v2_struct_0(sK1) )
    | ~ spl8_7
    | ~ spl8_13
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f177,f75])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK4,X0)
        | v2_struct_0(sK1) )
    | ~ spl8_13
    | ~ spl8_30 ),
    inference(resolution,[],[f171,f99])).

fof(f99,plain,
    ( v5_pre_topc(sK4,sK0,sK1)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f98])).

fof(f171,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v5_pre_topc(X2,X1,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | r1_tmap_1(X1,X0,X2,X3)
        | v2_struct_0(X0) )
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f170])).

fof(f172,plain,(
    spl8_30 ),
    inference(avatar_split_clause,[],[f40,f170])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
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

fof(f163,plain,
    ( spl8_28
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f155,f147,f143,f161])).

fof(f143,plain,
    ( spl8_24
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f147,plain,
    ( spl8_25
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK7(X0),k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_xboole_0(u1_struct_0(X0)) )
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_xboole_0(u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(resolution,[],[f148,f144])).

fof(f144,plain,
    ( ! [X0] :
        ( m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f143])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK7(X0),k1_zfmisc_1(X1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_xboole_0(X1) )
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f147])).

fof(f153,plain,(
    spl8_26 ),
    inference(avatar_split_clause,[],[f47,f151])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_funct_1(X2)
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

% (16136)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

% (16141)Refutation not found, incomplete strategy% (16141)------------------------------
% (16141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16141)Termination reason: Refutation not found, incomplete strategy

% (16141)Memory used [KB]: 10618
% (16141)Time elapsed: 0.064 s
% (16141)------------------------------
% (16141)------------------------------
fof(f149,plain,
    ( spl8_25
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f141,f130,f126,f147])).

fof(f126,plain,
    ( spl8_20
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f130,plain,
    ( spl8_21
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_xboole_0(sK7(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK7(X0),k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(resolution,[],[f131,f127])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f126])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(sK7(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f130])).

fof(f145,plain,(
    spl8_24 ),
    inference(avatar_split_clause,[],[f43,f143])).

fof(f43,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
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
          & v3_pre_topc(X1,X0)
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
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).

fof(f132,plain,(
    spl8_21 ),
    inference(avatar_split_clause,[],[f44,f130])).

fof(f44,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(sK7(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f128,plain,(
    spl8_20 ),
    inference(avatar_split_clause,[],[f38,f126])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
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

fof(f124,plain,(
    ~ spl8_19 ),
    inference(avatar_split_clause,[],[f22,f122])).

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

fof(f120,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f28,f118])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f116,plain,(
    spl8_17 ),
    inference(avatar_split_clause,[],[f25,f114])).

fof(f25,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f112,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f27,f110])).

fof(f27,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f108,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f24,f106])).

fof(f24,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f104,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f20,f102])).

fof(f20,plain,(
    r1_tmap_1(sK2,sK0,sK3,sK5) ),
    inference(cnf_transformation,[],[f9])).

fof(f100,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f21,f98])).

fof(f21,plain,(
    v5_pre_topc(sK4,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f96,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f19,f94])).

fof(f19,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f92,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f37,f90])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f88,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f36,f86])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f84,plain,(
    ~ spl8_9 ),
    inference(avatar_split_clause,[],[f35,f82])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f80,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f34,f78])).

fof(f34,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f76,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f33,f74])).

fof(f33,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f72,plain,(
    ~ spl8_6 ),
    inference(avatar_split_clause,[],[f32,f70])).

fof(f32,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f31,f66])).

fof(f31,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f64,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f60,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f29,f58])).

fof(f29,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f56,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:47:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (16129)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.47  % (16123)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (16138)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.47  % (16129)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f232,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f52,f56,f60,f64,f68,f72,f76,f80,f84,f88,f92,f96,f100,f104,f108,f112,f116,f120,f124,f128,f132,f145,f149,f153,f163,f172,f190,f194,f202,f216,f223,f226])).
% 0.22/0.48  fof(f226,plain,(
% 0.22/0.48    ~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_12 | ~spl8_14 | ~spl8_16 | ~spl8_18 | spl8_19 | ~spl8_36),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f224])).
% 0.22/0.48  fof(f224,plain,(
% 0.22/0.48    $false | (~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_12 | ~spl8_14 | ~spl8_16 | ~spl8_18 | spl8_19 | ~spl8_36)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f59,f55,f63,f67,f95,f103,f111,f119,f123,f222])).
% 0.22/0.48  fof(f222,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,X1,X2) | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2) | v2_struct_0(X0)) ) | ~spl8_36),
% 0.22/0.48    inference(avatar_component_clause,[],[f221])).
% 0.22/0.48  fof(f221,plain,(
% 0.22/0.48    spl8_36 <=> ! [X1,X0,X2] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,X1,X2) | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2) | v2_struct_0(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    ~r1_tmap_1(sK2,sK1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),sK5) | spl8_19),
% 0.22/0.48    inference(avatar_component_clause,[],[f122])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    spl8_19 <=> r1_tmap_1(sK2,sK1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),sK5)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~spl8_18),
% 0.22/0.48    inference(avatar_component_clause,[],[f118])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    spl8_18 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0)) | ~spl8_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f110])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    spl8_16 <=> v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    r1_tmap_1(sK2,sK0,sK3,sK5) | ~spl8_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f102])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    spl8_14 <=> r1_tmap_1(sK2,sK0,sK3,sK5)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl8_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f94])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    spl8_12 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    l1_pre_topc(sK2) | ~spl8_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f66])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl8_5 <=> l1_pre_topc(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    v2_pre_topc(sK2) | ~spl8_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f62])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl8_4 <=> v2_pre_topc(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    v1_funct_1(sK3) | ~spl8_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f54])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    spl8_2 <=> v1_funct_1(sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ~v2_struct_0(sK2) | spl8_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    spl8_3 <=> v2_struct_0(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.48  fof(f223,plain,(
% 0.22/0.48    spl8_36 | ~spl8_26 | ~spl8_28 | ~spl8_35),
% 0.22/0.48    inference(avatar_split_clause,[],[f219,f214,f161,f151,f221])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    spl8_26 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.22/0.48  fof(f161,plain,(
% 0.22/0.48    spl8_28 <=> ! [X0] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.22/0.48  fof(f214,plain,(
% 0.22/0.48    spl8_35 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,X1,X2) | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2) | ~m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.22/0.48  fof(f219,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,X1,X2) | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2) | v2_struct_0(X0)) ) | (~spl8_26 | ~spl8_28 | ~spl8_35)),
% 0.22/0.48    inference(subsumption_resolution,[],[f218,f162])).
% 0.22/0.48  fof(f162,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl8_28),
% 0.22/0.48    inference(avatar_component_clause,[],[f161])).
% 0.22/0.48  fof(f218,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,X1,X2) | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2) | v2_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) ) | (~spl8_26 | ~spl8_35)),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f217])).
% 0.22/0.48  fof(f217,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,X1,X2) | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2) | v2_struct_0(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v1_xboole_0(u1_struct_0(X0))) ) | (~spl8_26 | ~spl8_35)),
% 0.22/0.48    inference(resolution,[],[f215,f152])).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | v1_xboole_0(X0)) ) | ~spl8_26),
% 0.22/0.48    inference(avatar_component_clause,[],[f151])).
% 0.22/0.48  fof(f215,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,X1,X2) | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2) | v2_struct_0(X0)) ) | ~spl8_35),
% 0.22/0.48    inference(avatar_component_clause,[],[f214])).
% 0.22/0.48  fof(f216,plain,(
% 0.22/0.48    spl8_35 | ~spl8_1 | spl8_6 | ~spl8_7 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_15 | ~spl8_17 | ~spl8_32 | ~spl8_34),
% 0.22/0.48    inference(avatar_split_clause,[],[f212,f200,f188,f114,f106,f90,f86,f82,f78,f74,f70,f50,f214])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    spl8_1 <=> v1_funct_1(sK4)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    spl8_6 <=> v2_struct_0(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    spl8_7 <=> v2_pre_topc(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    spl8_8 <=> l1_pre_topc(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    spl8_9 <=> v2_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    spl8_10 <=> v2_pre_topc(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    spl8_11 <=> l1_pre_topc(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    spl8_15 <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    spl8_17 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.22/0.48  fof(f188,plain,(
% 0.22/0.48    spl8_32 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK4,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.22/0.48  fof(f200,plain,(
% 0.22/0.48    spl8_34 <=> ! [X1,X3,X5,X0,X2,X4] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~m1_subset_1(X5,u1_struct_0(X1)) | v2_struct_0(X0) | ~r1_tmap_1(X1,X2,X3,X5) | ~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 0.22/0.48  fof(f212,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,X1,X2) | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2) | ~m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0))) ) | (~spl8_1 | spl8_6 | ~spl8_7 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_15 | ~spl8_17 | ~spl8_32 | ~spl8_34)),
% 0.22/0.48    inference(subsumption_resolution,[],[f211,f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    v2_pre_topc(sK1) | ~spl8_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f74])).
% 0.22/0.48  fof(f211,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,X1,X2) | ~v2_pre_topc(sK1) | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2) | ~m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0))) ) | (~spl8_1 | spl8_6 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_15 | ~spl8_17 | ~spl8_32 | ~spl8_34)),
% 0.22/0.48    inference(subsumption_resolution,[],[f210,f71])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ~v2_struct_0(sK1) | spl8_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f70])).
% 0.22/0.48  fof(f210,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(sK1) | ~r1_tmap_1(X0,sK0,X1,X2) | ~v2_pre_topc(sK1) | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2) | ~m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0))) ) | (~spl8_1 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_15 | ~spl8_17 | ~spl8_32 | ~spl8_34)),
% 0.22/0.48    inference(subsumption_resolution,[],[f209,f115])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl8_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f114])).
% 0.22/0.48  fof(f209,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(sK1) | ~r1_tmap_1(X0,sK0,X1,X2) | ~v2_pre_topc(sK1) | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2) | ~m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0))) ) | (~spl8_1 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_15 | ~spl8_32 | ~spl8_34)),
% 0.22/0.48    inference(subsumption_resolution,[],[f208,f107])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl8_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f106])).
% 0.22/0.48  fof(f208,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(sK1) | ~r1_tmap_1(X0,sK0,X1,X2) | ~v2_pre_topc(sK1) | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2) | ~m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0))) ) | (~spl8_1 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_32 | ~spl8_34)),
% 0.22/0.48    inference(subsumption_resolution,[],[f207,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    v1_funct_1(sK4) | ~spl8_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f50])).
% 0.22/0.48  fof(f207,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(sK1) | ~r1_tmap_1(X0,sK0,X1,X2) | ~v2_pre_topc(sK1) | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2) | ~m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0))) ) | (~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_32 | ~spl8_34)),
% 0.22/0.48    inference(subsumption_resolution,[],[f206,f91])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    l1_pre_topc(sK0) | ~spl8_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f90])).
% 0.22/0.48  fof(f206,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(sK1) | ~r1_tmap_1(X0,sK0,X1,X2) | ~v2_pre_topc(sK1) | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2) | ~m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0))) ) | (~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_32 | ~spl8_34)),
% 0.22/0.48    inference(subsumption_resolution,[],[f205,f87])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    v2_pre_topc(sK0) | ~spl8_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f86])).
% 0.22/0.48  fof(f205,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(sK1) | ~r1_tmap_1(X0,sK0,X1,X2) | ~v2_pre_topc(sK1) | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2) | ~m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0))) ) | (~spl8_8 | spl8_9 | ~spl8_32 | ~spl8_34)),
% 0.22/0.48    inference(subsumption_resolution,[],[f204,f83])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    ~v2_struct_0(sK0) | spl8_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f82])).
% 0.22/0.48  fof(f204,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(sK1) | ~r1_tmap_1(X0,sK0,X1,X2) | ~v2_pre_topc(sK1) | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2) | ~m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0))) ) | (~spl8_8 | ~spl8_32 | ~spl8_34)),
% 0.22/0.48    inference(subsumption_resolution,[],[f203,f79])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    l1_pre_topc(sK1) | ~spl8_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f78])).
% 0.22/0.48  fof(f203,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(sK1) | ~r1_tmap_1(X0,sK0,X1,X2) | ~v2_pre_topc(sK1) | r1_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1,sK4),X2) | ~m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),X1,X2),u1_struct_0(sK0))) ) | (~spl8_32 | ~spl8_34)),
% 0.22/0.48    inference(resolution,[],[f201,f189])).
% 0.22/0.48  fof(f189,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tmap_1(sK0,sK1,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_32),
% 0.22/0.48    inference(avatar_component_clause,[],[f188])).
% 0.22/0.48  % (16141)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.48  fof(f201,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~m1_subset_1(X5,u1_struct_0(X1)) | v2_struct_0(X0) | ~r1_tmap_1(X1,X2,X3,X5) | ~v2_pre_topc(X0) | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)) ) | ~spl8_34),
% 0.22/0.48    inference(avatar_component_clause,[],[f200])).
% 0.22/0.48  fof(f202,plain,(
% 0.22/0.48    spl8_34 | ~spl8_26 | ~spl8_28 | ~spl8_33),
% 0.22/0.48    inference(avatar_split_clause,[],[f198,f192,f161,f151,f200])).
% 0.22/0.48  fof(f192,plain,(
% 0.22/0.48    spl8_33 <=> ! [X1,X3,X5,X0,X2,X4] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2)) | ~r1_tmap_1(X1,X2,X3,X5) | ~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.22/0.48  fof(f198,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~m1_subset_1(X5,u1_struct_0(X1)) | v2_struct_0(X0) | ~r1_tmap_1(X1,X2,X3,X5) | ~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)) ) | (~spl8_26 | ~spl8_28 | ~spl8_33)),
% 0.22/0.48    inference(subsumption_resolution,[],[f197,f162])).
% 0.22/0.48  fof(f197,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~m1_subset_1(X5,u1_struct_0(X1)) | v2_struct_0(X0) | ~r1_tmap_1(X1,X2,X3,X5) | ~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | v1_xboole_0(u1_struct_0(X1))) ) | (~spl8_26 | ~spl8_33)),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f196])).
% 0.22/0.48  fof(f196,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~m1_subset_1(X5,u1_struct_0(X1)) | v2_struct_0(X0) | ~r1_tmap_1(X1,X2,X3,X5) | ~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_subset_1(X5,u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X1))) ) | (~spl8_26 | ~spl8_33)),
% 0.22/0.48    inference(resolution,[],[f193,f152])).
% 0.22/0.48  fof(f193,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~m1_subset_1(X5,u1_struct_0(X1)) | v2_struct_0(X0) | ~r1_tmap_1(X1,X2,X3,X5) | ~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)) ) | ~spl8_33),
% 0.22/0.48    inference(avatar_component_clause,[],[f192])).
% 0.22/0.48  fof(f194,plain,(
% 0.22/0.48    spl8_33),
% 0.22/0.48    inference(avatar_split_clause,[],[f48,f192])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2)) | ~r1_tmap_1(X1,X2,X3,X5) | ~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)) )),
% 0.22/0.48    inference(equality_resolution,[],[f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X2)) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~r1_tmap_1(X1,X2,X3,X5) | ~r1_tmap_1(X2,X0,X4,X6) | r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | (~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6)) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X0,X4,X6) & r1_tmap_1(X1,X2,X3,X5) & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6) => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)))))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tmap_1)).
% 0.22/0.48  fof(f190,plain,(
% 0.22/0.48    spl8_32 | ~spl8_1 | spl8_6 | ~spl8_7 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_15 | ~spl8_17 | ~spl8_30),
% 0.22/0.48    inference(avatar_split_clause,[],[f186,f170,f114,f106,f98,f90,f86,f82,f78,f74,f70,f50,f188])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    spl8_13 <=> v5_pre_topc(sK4,sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.22/0.48  fof(f170,plain,(
% 0.22/0.48    spl8_30 <=> ! [X1,X3,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X1)) | r1_tmap_1(X1,X0,X2,X3) | ~v5_pre_topc(X2,X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.22/0.48  fof(f186,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK4,X0)) ) | (~spl8_1 | spl8_6 | ~spl8_7 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_15 | ~spl8_17 | ~spl8_30)),
% 0.22/0.48    inference(subsumption_resolution,[],[f185,f71])).
% 0.22/0.48  fof(f185,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK4,X0) | v2_struct_0(sK1)) ) | (~spl8_1 | ~spl8_7 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_15 | ~spl8_17 | ~spl8_30)),
% 0.22/0.48    inference(subsumption_resolution,[],[f184,f115])).
% 0.22/0.48  fof(f184,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK4,X0) | v2_struct_0(sK1)) ) | (~spl8_1 | ~spl8_7 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_15 | ~spl8_30)),
% 0.22/0.48    inference(subsumption_resolution,[],[f183,f107])).
% 0.22/0.48  fof(f183,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK4,X0) | v2_struct_0(sK1)) ) | (~spl8_1 | ~spl8_7 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_30)),
% 0.22/0.48    inference(subsumption_resolution,[],[f182,f51])).
% 0.22/0.48  fof(f182,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK4,X0) | v2_struct_0(sK1)) ) | (~spl8_7 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_11 | ~spl8_13 | ~spl8_30)),
% 0.22/0.48    inference(subsumption_resolution,[],[f181,f91])).
% 0.22/0.48  fof(f181,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK4,X0) | v2_struct_0(sK1)) ) | (~spl8_7 | ~spl8_8 | spl8_9 | ~spl8_10 | ~spl8_13 | ~spl8_30)),
% 0.22/0.48    inference(subsumption_resolution,[],[f180,f87])).
% 0.22/0.48  fof(f180,plain,(
% 0.22/0.48    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK4,X0) | v2_struct_0(sK1)) ) | (~spl8_7 | ~spl8_8 | spl8_9 | ~spl8_13 | ~spl8_30)),
% 0.22/0.48    inference(subsumption_resolution,[],[f179,f83])).
% 0.22/0.48  fof(f179,plain,(
% 0.22/0.48    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK4,X0) | v2_struct_0(sK1)) ) | (~spl8_7 | ~spl8_8 | ~spl8_13 | ~spl8_30)),
% 0.22/0.48    inference(subsumption_resolution,[],[f178,f79])).
% 0.22/0.48  fof(f178,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK4,X0) | v2_struct_0(sK1)) ) | (~spl8_7 | ~spl8_13 | ~spl8_30)),
% 0.22/0.48    inference(subsumption_resolution,[],[f177,f75])).
% 0.22/0.48  fof(f177,plain,(
% 0.22/0.48    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK4,X0) | v2_struct_0(sK1)) ) | (~spl8_13 | ~spl8_30)),
% 0.22/0.48    inference(resolution,[],[f171,f99])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    v5_pre_topc(sK4,sK0,sK1) | ~spl8_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f98])).
% 0.22/0.48  fof(f171,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~v5_pre_topc(X2,X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X1)) | r1_tmap_1(X1,X0,X2,X3) | v2_struct_0(X0)) ) | ~spl8_30),
% 0.22/0.48    inference(avatar_component_clause,[],[f170])).
% 0.22/0.48  fof(f172,plain,(
% 0.22/0.48    spl8_30),
% 0.22/0.48    inference(avatar_split_clause,[],[f40,f170])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X1)) | r1_tmap_1(X1,X0,X2,X3) | ~v5_pre_topc(X2,X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).
% 0.22/0.48  fof(f163,plain,(
% 0.22/0.48    spl8_28 | ~spl8_24 | ~spl8_25),
% 0.22/0.48    inference(avatar_split_clause,[],[f155,f147,f143,f161])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    spl8_24 <=> ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.22/0.48  fof(f147,plain,(
% 0.22/0.48    spl8_25 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK7(X0),k1_zfmisc_1(X1)) | ~v1_xboole_0(X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_xboole_0(u1_struct_0(X0))) ) | (~spl8_24 | ~spl8_25)),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f154])).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl8_24 | ~spl8_25)),
% 0.22/0.48    inference(resolution,[],[f148,f144])).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl8_24),
% 0.22/0.48    inference(avatar_component_clause,[],[f143])).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(sK7(X0),k1_zfmisc_1(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_xboole_0(X1)) ) | ~spl8_25),
% 0.22/0.48    inference(avatar_component_clause,[],[f147])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    spl8_26),
% 0.22/0.48    inference(avatar_split_clause,[],[f47,f151])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.48    inference(flattening,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  % (16136)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 0.22/0.48  % (16141)Refutation not found, incomplete strategy% (16141)------------------------------
% 0.22/0.48  % (16141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (16141)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (16141)Memory used [KB]: 10618
% 0.22/0.48  % (16141)Time elapsed: 0.064 s
% 0.22/0.48  % (16141)------------------------------
% 0.22/0.48  % (16141)------------------------------
% 0.22/0.48  fof(f149,plain,(
% 0.22/0.48    spl8_25 | ~spl8_20 | ~spl8_21),
% 0.22/0.48    inference(avatar_split_clause,[],[f141,f130,f126,f147])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    spl8_20 <=> ! [X1,X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    spl8_21 <=> ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(sK7(X0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK7(X0),k1_zfmisc_1(X1)) | ~v1_xboole_0(X1)) ) | (~spl8_20 | ~spl8_21)),
% 0.22/0.48    inference(resolution,[],[f131,f127])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) ) | ~spl8_20),
% 0.22/0.48    inference(avatar_component_clause,[],[f126])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(sK7(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl8_21),
% 0.22/0.48    inference(avatar_component_clause,[],[f130])).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    spl8_24),
% 0.22/0.48    inference(avatar_split_clause,[],[f43,f143])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    spl8_21),
% 0.22/0.48    inference(avatar_split_clause,[],[f44,f130])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(sK7(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    spl8_20),
% 0.22/0.48    inference(avatar_split_clause,[],[f38,f126])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    ~spl8_19),
% 0.22/0.48    inference(avatar_split_clause,[],[f22,f122])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ~r1_tmap_1(sK2,sK1,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),sK5)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & (v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5))) & m1_subset_1(X5,u1_struct_0(X2))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3))) & (l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5)) => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5))))))))),
% 0.22/0.48    inference(negated_conjecture,[],[f6])).
% 0.22/0.48  fof(f6,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5)) => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5))))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tmap_1)).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    spl8_18),
% 0.22/0.48    inference(avatar_split_clause,[],[f28,f118])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    spl8_17),
% 0.22/0.48    inference(avatar_split_clause,[],[f25,f114])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    spl8_16),
% 0.22/0.48    inference(avatar_split_clause,[],[f27,f110])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    spl8_15),
% 0.22/0.48    inference(avatar_split_clause,[],[f24,f106])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    spl8_14),
% 0.22/0.48    inference(avatar_split_clause,[],[f20,f102])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    r1_tmap_1(sK2,sK0,sK3,sK5)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    spl8_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f21,f98])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    v5_pre_topc(sK4,sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    spl8_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f94])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    spl8_11),
% 0.22/0.48    inference(avatar_split_clause,[],[f37,f90])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    l1_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    spl8_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f36,f86])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    v2_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    ~spl8_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f82])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ~v2_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    spl8_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f78])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    l1_pre_topc(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    spl8_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f33,f74])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    v2_pre_topc(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ~spl8_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f32,f70])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ~v2_struct_0(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl8_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f31,f66])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    l1_pre_topc(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl8_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f30,f62])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    v2_pre_topc(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ~spl8_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f29,f58])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ~v2_struct_0(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    spl8_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f26,f54])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    v1_funct_1(sK3)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    spl8_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f23,f50])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    v1_funct_1(sK4)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (16129)------------------------------
% 0.22/0.48  % (16129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (16129)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (16129)Memory used [KB]: 10746
% 0.22/0.48  % (16129)Time elapsed: 0.063 s
% 0.22/0.48  % (16129)------------------------------
% 0.22/0.48  % (16129)------------------------------
% 0.22/0.48  % (16133)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (16119)Success in time 0.121 s
%------------------------------------------------------------------------------
