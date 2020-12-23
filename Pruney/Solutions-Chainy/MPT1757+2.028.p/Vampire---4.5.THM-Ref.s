%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  252 ( 509 expanded)
%              Number of leaves         :   54 ( 213 expanded)
%              Depth                    :   10
%              Number of atoms          : 1609 (3560 expanded)
%              Number of equality atoms :   17 (  91 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f369,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f87,f91,f95,f99,f103,f107,f111,f119,f123,f127,f131,f135,f139,f143,f150,f153,f157,f161,f165,f169,f177,f183,f199,f207,f211,f218,f223,f227,f235,f239,f244,f248,f270,f287,f295,f302,f310,f319,f330,f336,f353,f359,f364,f368])).

fof(f368,plain,
    ( ~ spl8_5
    | ~ spl8_11
    | ~ spl8_19
    | spl8_52 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_19
    | spl8_52 ),
    inference(unit_resulting_resolution,[],[f98,f122,f363,f156])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl8_19
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f363,plain,
    ( ~ l1_pre_topc(sK3)
    | spl8_52 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl8_52
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f122,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl8_11
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f98,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl8_5
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f364,plain,
    ( ~ spl8_52
    | ~ spl8_16
    | spl8_51 ),
    inference(avatar_split_clause,[],[f360,f357,f141,f362])).

fof(f141,plain,
    ( spl8_16
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f357,plain,
    ( spl8_51
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f360,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl8_16
    | spl8_51 ),
    inference(resolution,[],[f358,f142])).

fof(f142,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f141])).

fof(f358,plain,
    ( ~ l1_struct_0(sK3)
    | spl8_51 ),
    inference(avatar_component_clause,[],[f357])).

fof(f359,plain,
    ( ~ spl8_51
    | spl8_1
    | ~ spl8_20
    | ~ spl8_49 ),
    inference(avatar_split_clause,[],[f355,f334,f159,f81,f357])).

fof(f81,plain,
    ( spl8_1
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f159,plain,
    ( spl8_20
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f334,plain,
    ( spl8_49
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f355,plain,
    ( ~ l1_struct_0(sK3)
    | spl8_1
    | ~ spl8_20
    | ~ spl8_49 ),
    inference(subsumption_resolution,[],[f354,f82])).

fof(f82,plain,
    ( ~ v2_struct_0(sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f354,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl8_20
    | ~ spl8_49 ),
    inference(resolution,[],[f335,f160])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f159])).

fof(f335,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f334])).

fof(f353,plain,
    ( ~ spl8_42
    | ~ spl8_47
    | ~ spl8_43
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_32
    | spl8_48 ),
    inference(avatar_split_clause,[],[f342,f328,f209,f125,f97,f93,f89,f282,f325,f279])).

fof(f279,plain,
    ( spl8_42
  <=> v3_pre_topc(u1_struct_0(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f325,plain,
    ( spl8_47
  <=> r2_hidden(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f282,plain,
    ( spl8_43
  <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f89,plain,
    ( spl8_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f93,plain,
    ( spl8_4
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f125,plain,
    ( spl8_12
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f209,plain,
    ( spl8_32
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_hidden(X2,X1)
        | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f328,plain,
    ( spl8_48
  <=> m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f342,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_32
    | spl8_48 ),
    inference(subsumption_resolution,[],[f341,f90])).

fof(f90,plain,
    ( ~ v2_struct_0(sK1)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f341,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_32
    | spl8_48 ),
    inference(subsumption_resolution,[],[f340,f126])).

fof(f126,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f340,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_32
    | spl8_48 ),
    inference(subsumption_resolution,[],[f339,f98])).

fof(f339,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ spl8_4
    | ~ spl8_32
    | spl8_48 ),
    inference(subsumption_resolution,[],[f337,f94])).

fof(f94,plain,
    ( v2_pre_topc(sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f337,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ spl8_32
    | spl8_48 ),
    inference(resolution,[],[f329,f210])).

fof(f210,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_hidden(X2,X1)
        | v2_struct_0(X0)
        | ~ v3_pre_topc(X1,X0) )
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f209])).

fof(f329,plain,
    ( ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl8_48 ),
    inference(avatar_component_clause,[],[f328])).

fof(f336,plain,
    ( spl8_49
    | ~ spl8_13
    | ~ spl8_21
    | spl8_47 ),
    inference(avatar_split_clause,[],[f332,f325,f163,f129,f334])).

fof(f129,plain,
    ( spl8_13
  <=> m1_subset_1(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f163,plain,
    ( spl8_21
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f332,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl8_13
    | ~ spl8_21
    | spl8_47 ),
    inference(subsumption_resolution,[],[f331,f130])).

fof(f130,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f331,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl8_21
    | spl8_47 ),
    inference(resolution,[],[f326,f164])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f163])).

fof(f326,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | spl8_47 ),
    inference(avatar_component_clause,[],[f325])).

fof(f330,plain,
    ( ~ spl8_47
    | ~ spl8_48
    | ~ spl8_12
    | ~ spl8_13
    | spl8_17
    | ~ spl8_18
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f323,f317,f148,f145,f129,f125,f328,f325])).

fof(f145,plain,
    ( spl8_17
  <=> r1_tmap_1(sK1,sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f148,plain,
    ( spl8_18
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f317,plain,
    ( spl8_46
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f323,plain,
    ( ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ spl8_12
    | ~ spl8_13
    | spl8_17
    | ~ spl8_18
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f322,f146])).

fof(f146,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | spl8_17 ),
    inference(avatar_component_clause,[],[f145])).

fof(f322,plain,
    ( ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_18
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f321,f126])).

fof(f321,plain,
    ( ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ spl8_13
    | ~ spl8_18
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f320,f130])).

fof(f320,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ spl8_18
    | ~ spl8_46 ),
    inference(resolution,[],[f318,f152])).

fof(f152,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f148])).

fof(f318,plain,
    ( ! [X0] :
        ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ r2_hidden(X0,u1_struct_0(sK3)) )
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f317])).

fof(f319,plain,
    ( spl8_46
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_45 ),
    inference(avatar_split_clause,[],[f315,f308,f137,f133,f109,f105,f101,f317])).

fof(f101,plain,
    ( spl8_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f105,plain,
    ( spl8_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f109,plain,
    ( spl8_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f133,plain,
    ( spl8_14
  <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f137,plain,
    ( spl8_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f308,plain,
    ( spl8_45
  <=> ! [X1,X0] :
        ( r1_tmap_1(sK1,X0,sK2,X1)
        | ~ r2_hidden(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f315,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) )
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f314,f110])).

fof(f110,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f314,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(sK0) )
    | spl8_6
    | ~ spl8_7
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f313,f138])).

fof(f138,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f137])).

fof(f313,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | spl8_6
    | ~ spl8_7
    | ~ spl8_14
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f312,f102])).

fof(f102,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f312,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl8_7
    | ~ spl8_14
    | ~ spl8_45 ),
    inference(subsumption_resolution,[],[f311,f106])).

fof(f106,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f311,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ v2_pre_topc(sK0)
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl8_14
    | ~ spl8_45 ),
    inference(resolution,[],[f309,f134])).

fof(f134,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f309,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(X0))
        | ~ r2_hidden(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_tmap_1(sK1,X0,sK2,X1)
        | ~ v2_pre_topc(X0)
        | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f308])).

fof(f310,plain,
    ( spl8_45
    | ~ spl8_2
    | ~ spl8_44 ),
    inference(avatar_split_clause,[],[f306,f285,f85,f308])).

fof(f85,plain,
    ( spl8_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f285,plain,
    ( spl8_44
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tmap_1(sK1,X1,X2,X0)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0)
        | v2_struct_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f306,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(sK1,X0,sK2,X1)
        | ~ r2_hidden(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl8_2
    | ~ spl8_44 ),
    inference(resolution,[],[f286,f86])).

fof(f86,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f286,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | r1_tmap_1(sK1,X1,X2,X0)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0)
        | v2_struct_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ l1_pre_topc(X1) )
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f285])).

fof(f302,plain,
    ( ~ spl8_5
    | ~ spl8_11
    | ~ spl8_22
    | spl8_43 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_22
    | spl8_43 ),
    inference(subsumption_resolution,[],[f300,f98])).

fof(f300,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl8_11
    | ~ spl8_22
    | spl8_43 ),
    inference(subsumption_resolution,[],[f297,f122])).

fof(f297,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl8_22
    | spl8_43 ),
    inference(resolution,[],[f283,f168])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl8_22
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f283,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl8_43 ),
    inference(avatar_component_clause,[],[f282])).

fof(f295,plain,
    ( ~ spl8_4
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_24
    | spl8_42 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_24
    | spl8_42 ),
    inference(subsumption_resolution,[],[f293,f122])).

fof(f293,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_24
    | spl8_42 ),
    inference(subsumption_resolution,[],[f292,f118])).

fof(f118,plain,
    ( v1_tsep_1(sK3,sK1)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl8_10
  <=> v1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f292,plain,
    ( ~ v1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_24
    | spl8_42 ),
    inference(subsumption_resolution,[],[f291,f94])).

fof(f291,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ v1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl8_5
    | ~ spl8_24
    | spl8_42 ),
    inference(subsumption_resolution,[],[f289,f98])).

fof(f289,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl8_24
    | spl8_42 ),
    inference(resolution,[],[f280,f176])).

fof(f176,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(u1_struct_0(X1),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,X0) )
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl8_24
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v3_pre_topc(u1_struct_0(X1),X0)
        | ~ v1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f280,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | spl8_42 ),
    inference(avatar_component_clause,[],[f279])).

fof(f287,plain,
    ( ~ spl8_42
    | ~ spl8_43
    | spl8_44
    | spl8_1
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_29
    | ~ spl8_41 ),
    inference(avatar_split_clause,[],[f277,f268,f197,f121,f97,f93,f89,f81,f285,f282,f279])).

fof(f197,plain,
    ( spl8_29
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_hidden(X2,X1)
        | r1_tarski(sK7(X0,X1,X2),X1)
        | ~ v3_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f268,plain,
    ( spl8_41
  <=> ! [X1,X3,X2,X4] :
        ( ~ r2_hidden(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(X4))
        | ~ r1_tarski(sK7(sK1,u1_struct_0(sK3),X1),u1_struct_0(X4))
        | v2_struct_0(X2)
        | ~ r1_tmap_1(X4,X2,k2_tmap_1(sK1,X2,X3,X4),X1)
        | r1_tmap_1(sK1,X2,X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f277,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0)
        | r1_tmap_1(sK1,X1,X2,X0)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(u1_struct_0(sK3),sK1) )
    | spl8_1
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_29
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f276,f90])).

fof(f276,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0)
        | r1_tmap_1(sK1,X1,X2,X0)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | v2_struct_0(sK1)
        | ~ v3_pre_topc(u1_struct_0(sK3),sK1) )
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_29
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f275,f98])).

fof(f275,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0)
        | r1_tmap_1(sK1,X1,X2,X0)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | v2_struct_0(sK1)
        | ~ v3_pre_topc(u1_struct_0(sK3),sK1) )
    | spl8_1
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_29
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f274,f94])).

fof(f274,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0)
        | r1_tmap_1(sK1,X1,X2,X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | v2_struct_0(sK1)
        | ~ v3_pre_topc(u1_struct_0(sK3),sK1) )
    | spl8_1
    | ~ spl8_11
    | ~ spl8_29
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f273,f122])).

fof(f273,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0)
        | r1_tmap_1(sK1,X1,X2,X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | v2_struct_0(sK1)
        | ~ v3_pre_topc(u1_struct_0(sK3),sK1) )
    | spl8_1
    | ~ spl8_29
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f272,f82])).

fof(f272,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0)
        | r1_tmap_1(sK1,X1,X2,X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | v2_struct_0(sK1)
        | ~ v3_pre_topc(u1_struct_0(sK3),sK1) )
    | ~ spl8_29
    | ~ spl8_41 ),
    inference(duplicate_literal_removal,[],[f271])).

fof(f271,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0)
        | r1_tmap_1(sK1,X1,X2,X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | v2_struct_0(sK1)
        | ~ v3_pre_topc(u1_struct_0(sK3),sK1) )
    | ~ spl8_29
    | ~ spl8_41 ),
    inference(resolution,[],[f269,f198])).

fof(f198,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(sK7(X0,X1,X2),X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_hidden(X2,X1)
        | v2_struct_0(X0)
        | ~ v3_pre_topc(X1,X0) )
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f197])).

fof(f269,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ r1_tarski(sK7(sK1,u1_struct_0(sK3),X1),u1_struct_0(X4))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(X4))
        | ~ r2_hidden(X1,u1_struct_0(sK3))
        | v2_struct_0(X2)
        | ~ r1_tmap_1(X4,X2,k2_tmap_1(sK1,X2,X3,X4),X1)
        | r1_tmap_1(sK1,X2,X3,X1) )
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f268])).

fof(f270,plain,
    ( spl8_41
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_37
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f256,f246,f242,f97,f93,f89,f268])).

fof(f242,plain,
    ( spl8_37
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X0),sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f246,plain,
    ( spl8_38
  <=> ! [X1,X3,X0,X2,X4,X6] :
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
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ r1_tarski(X4,u1_struct_0(X3))
        | ~ m1_connsp_2(X4,X1,X6)
        | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
        | r1_tmap_1(X1,X0,X2,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f256,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ r2_hidden(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(X4))
        | ~ r1_tarski(sK7(sK1,u1_struct_0(sK3),X1),u1_struct_0(X4))
        | v2_struct_0(X2)
        | ~ r1_tmap_1(X4,X2,k2_tmap_1(sK1,X2,X3,X4),X1)
        | r1_tmap_1(sK1,X2,X3,X1) )
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_37
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f255,f98])).

fof(f255,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ r2_hidden(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(X4))
        | ~ r1_tarski(sK7(sK1,u1_struct_0(sK3),X1),u1_struct_0(X4))
        | v2_struct_0(X2)
        | ~ r1_tmap_1(X4,X2,k2_tmap_1(sK1,X2,X3,X4),X1)
        | r1_tmap_1(sK1,X2,X3,X1) )
    | spl8_3
    | ~ spl8_4
    | ~ spl8_37
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f254,f94])).

fof(f254,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ r2_hidden(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(X4))
        | ~ r1_tarski(sK7(sK1,u1_struct_0(sK3),X1),u1_struct_0(X4))
        | v2_struct_0(X2)
        | ~ r1_tmap_1(X4,X2,k2_tmap_1(sK1,X2,X3,X4),X1)
        | r1_tmap_1(sK1,X2,X3,X1) )
    | spl8_3
    | ~ spl8_37
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f250,f90])).

fof(f250,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ r2_hidden(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK1)
        | ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(X4))
        | ~ r1_tarski(sK7(sK1,u1_struct_0(sK3),X1),u1_struct_0(X4))
        | v2_struct_0(X2)
        | ~ r1_tmap_1(X4,X2,k2_tmap_1(sK1,X2,X3,X4),X1)
        | r1_tmap_1(sK1,X2,X3,X1) )
    | ~ spl8_37
    | ~ spl8_38 ),
    inference(resolution,[],[f243,f247])).

% (26226)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f247,plain,
    ( ! [X6,X4,X2,X0,X3,X1] :
        ( ~ m1_connsp_2(X4,X1,X6)
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
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ r1_tarski(X4,u1_struct_0(X3))
        | v2_struct_0(X0)
        | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
        | r1_tmap_1(X1,X0,X2,X6) )
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f246])).

fof(f243,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X0),sK1,X0)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f242])).

fof(f248,plain,
    ( spl8_38
    | ~ spl8_25
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f240,f237,f181,f246])).

fof(f181,plain,
    ( spl8_25
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f237,plain,
    ( spl8_36
  <=> ! [X1,X3,X0,X2,X4,X6] :
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
        | ~ m1_subset_1(X6,u1_struct_0(X1))
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ r1_tarski(X4,u1_struct_0(X3))
        | ~ m1_connsp_2(X4,X1,X6)
        | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
        | r1_tmap_1(X1,X0,X2,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f240,plain,
    ( ! [X6,X4,X2,X0,X3,X1] :
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
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ r1_tarski(X4,u1_struct_0(X3))
        | ~ m1_connsp_2(X4,X1,X6)
        | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
        | r1_tmap_1(X1,X0,X2,X6) )
    | ~ spl8_25
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f238,f182])).

fof(f182,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | v2_struct_0(X0) )
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f181])).

fof(f238,plain,
    ( ! [X6,X4,X2,X0,X3,X1] :
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
        | ~ m1_subset_1(X6,u1_struct_0(X1))
        | ~ m1_subset_1(X6,u1_struct_0(X3))
        | ~ r1_tarski(X4,u1_struct_0(X3))
        | ~ m1_connsp_2(X4,X1,X6)
        | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
        | r1_tmap_1(X1,X0,X2,X6) )
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f237])).

fof(f244,plain,
    ( spl8_37
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f232,f221,f121,f117,f97,f93,f89,f242])).

fof(f221,plain,
    ( spl8_34
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_hidden(X2,u1_struct_0(X1))
        | m1_connsp_2(sK7(X0,u1_struct_0(X1),X2),X0,X2)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X0),sK1,X0) )
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f231,f122])).

fof(f231,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X0),sK1,X0)
        | ~ m1_pre_topc(sK3,sK1) )
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f230,f94])).

% (26239)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f230,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X0),sK1,X0)
        | ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK1) )
    | spl8_3
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f229,f90])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X0),sK1,X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK1) )
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f228,f98])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X0),sK1,X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK1) )
    | ~ spl8_10
    | ~ spl8_34 ),
    inference(resolution,[],[f222,f118])).

fof(f222,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_tsep_1(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_hidden(X2,u1_struct_0(X1))
        | m1_connsp_2(sK7(X0,u1_struct_0(X1),X2),X0,X2)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0) )
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f221])).

fof(f239,plain,(
    spl8_36 ),
    inference(avatar_split_clause,[],[f72,f237])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
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
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f235,plain,
    ( spl8_1
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_17
    | spl8_18
    | ~ spl8_35 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_17
    | spl8_18
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f106,f90,f94,f98,f82,f86,f110,f102,f122,f130,f151,f134,f149,f138,f226])).

fof(f226,plain,
    ( ! [X2,X0,X5,X3,X1] :
        ( ~ v1_funct_1(X2)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X1)
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_tmap_1(X1,X0,X2,X5)
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl8_35
  <=> ! [X1,X3,X5,X0,X2] :
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
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_tmap_1(X1,X0,X2,X5)
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f149,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | spl8_18 ),
    inference(avatar_component_clause,[],[f148])).

fof(f151,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f145])).

fof(f227,plain,
    ( spl8_35
    | ~ spl8_25
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f219,f216,f181,f225])).

fof(f216,plain,
    ( spl8_33
  <=> ! [X1,X3,X5,X0,X2] :
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
        | ~ m1_subset_1(X5,u1_struct_0(X1))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_tmap_1(X1,X0,X2,X5)
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f219,plain,
    ( ! [X2,X0,X5,X3,X1] :
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
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_tmap_1(X1,X0,X2,X5)
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
    | ~ spl8_25
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f217,f182])).

fof(f217,plain,
    ( ! [X2,X0,X5,X3,X1] :
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
        | ~ m1_subset_1(X5,u1_struct_0(X1))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_tmap_1(X1,X0,X2,X5)
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f216])).

fof(f223,plain,
    ( spl8_34
    | ~ spl8_22
    | ~ spl8_24
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f214,f205,f175,f167,f221])).

fof(f205,plain,
    ( spl8_31
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_hidden(X2,X1)
        | m1_connsp_2(sK7(X0,X1,X2),X0,X2)
        | ~ v3_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f214,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_hidden(X2,u1_struct_0(X1))
        | m1_connsp_2(sK7(X0,u1_struct_0(X1),X2),X0,X2)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,X0) )
    | ~ spl8_22
    | ~ spl8_24
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f213,f168])).

fof(f213,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_hidden(X2,u1_struct_0(X1))
        | m1_connsp_2(sK7(X0,u1_struct_0(X1),X2),X0,X2)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,X0) )
    | ~ spl8_24
    | ~ spl8_31 ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_hidden(X2,u1_struct_0(X1))
        | m1_connsp_2(sK7(X0,u1_struct_0(X1),X2),X0,X2)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,X0) )
    | ~ spl8_24
    | ~ spl8_31 ),
    inference(resolution,[],[f206,f176])).

fof(f206,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_hidden(X2,X1)
        | m1_connsp_2(sK7(X0,X1,X2),X0,X2)
        | v2_struct_0(X0) )
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f205])).

fof(f218,plain,(
    spl8_33 ),
    inference(avatar_split_clause,[],[f70,f216])).

fof(f70,plain,(
    ! [X2,X0,X5,X3,X1] :
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
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f211,plain,(
    spl8_32 ),
    inference(avatar_split_clause,[],[f57,f209])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

fof(f207,plain,(
    spl8_31 ),
    inference(avatar_split_clause,[],[f58,f205])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(sK7(X0,X1,X2),X0,X2)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f199,plain,(
    spl8_29 ),
    inference(avatar_split_clause,[],[f59,f197])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | r1_tarski(sK7(X0,X1,X2),X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f183,plain,(
    spl8_25 ),
    inference(avatar_split_clause,[],[f65,f181])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f177,plain,(
    spl8_24 ),
    inference(avatar_split_clause,[],[f79,f175])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(subsumption_resolution,[],[f74,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f169,plain,(
    spl8_22 ),
    inference(avatar_split_clause,[],[f54,f167])).

fof(f165,plain,(
    spl8_21 ),
    inference(avatar_split_clause,[],[f68,f163])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f161,plain,(
    spl8_20 ),
    inference(avatar_split_clause,[],[f55,f159])).

fof(f55,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f157,plain,(
    spl8_19 ),
    inference(avatar_split_clause,[],[f53,f155])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f153,plain,
    ( spl8_17
    | spl8_18 ),
    inference(avatar_split_clause,[],[f77,f148,f145])).

fof(f77,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f35,f38])).

fof(f38,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
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

fof(f35,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f150,plain,
    ( ~ spl8_17
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f76,f148,f145])).

fof(f76,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f36,f38])).

fof(f36,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f143,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f52,f141])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f139,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f45,f137])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f135,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f44,f133])).

fof(f44,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f131,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f75,f129])).

fof(f75,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f37,f38])).

fof(f37,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f127,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f39,f125])).

fof(f39,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f123,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f42,f121])).

fof(f42,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f119,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f41,f117])).

fof(f41,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f111,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f51,f109])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f107,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f50,f105])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f103,plain,(
    ~ spl8_6 ),
    inference(avatar_split_clause,[],[f49,f101])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f99,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f48,f97])).

fof(f48,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f95,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f47,f93])).

fof(f47,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f46,f89])).

fof(f46,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f43,f85])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f40,f81])).

fof(f40,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:46:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (26241)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.48  % (26229)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (26235)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (26227)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (26224)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (26228)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (26237)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (26238)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (26231)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (26222)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (26242)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (26223)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (26230)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (26232)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.51  % (26234)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (26236)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (26240)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (26225)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (26231)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f369,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f83,f87,f91,f95,f99,f103,f107,f111,f119,f123,f127,f131,f135,f139,f143,f150,f153,f157,f161,f165,f169,f177,f183,f199,f207,f211,f218,f223,f227,f235,f239,f244,f248,f270,f287,f295,f302,f310,f319,f330,f336,f353,f359,f364,f368])).
% 0.22/0.51  fof(f368,plain,(
% 0.22/0.51    ~spl8_5 | ~spl8_11 | ~spl8_19 | spl8_52),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f366])).
% 0.22/0.51  fof(f366,plain,(
% 0.22/0.51    $false | (~spl8_5 | ~spl8_11 | ~spl8_19 | spl8_52)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f98,f122,f363,f156])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl8_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f155])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    spl8_19 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.22/0.51  fof(f363,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | spl8_52),
% 0.22/0.51    inference(avatar_component_clause,[],[f362])).
% 0.22/0.51  fof(f362,plain,(
% 0.22/0.51    spl8_52 <=> l1_pre_topc(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    m1_pre_topc(sK3,sK1) | ~spl8_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f121])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    spl8_11 <=> m1_pre_topc(sK3,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    l1_pre_topc(sK1) | ~spl8_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f97])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    spl8_5 <=> l1_pre_topc(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.51  fof(f364,plain,(
% 0.22/0.51    ~spl8_52 | ~spl8_16 | spl8_51),
% 0.22/0.51    inference(avatar_split_clause,[],[f360,f357,f141,f362])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    spl8_16 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.22/0.51  fof(f357,plain,(
% 0.22/0.51    spl8_51 <=> l1_struct_0(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 0.22/0.51  fof(f360,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | (~spl8_16 | spl8_51)),
% 0.22/0.51    inference(resolution,[],[f358,f142])).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl8_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f141])).
% 0.22/0.51  fof(f358,plain,(
% 0.22/0.51    ~l1_struct_0(sK3) | spl8_51),
% 0.22/0.51    inference(avatar_component_clause,[],[f357])).
% 0.22/0.51  fof(f359,plain,(
% 0.22/0.51    ~spl8_51 | spl8_1 | ~spl8_20 | ~spl8_49),
% 0.22/0.51    inference(avatar_split_clause,[],[f355,f334,f159,f81,f357])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    spl8_1 <=> v2_struct_0(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    spl8_20 <=> ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.22/0.51  fof(f334,plain,(
% 0.22/0.51    spl8_49 <=> v1_xboole_0(u1_struct_0(sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 0.22/0.51  fof(f355,plain,(
% 0.22/0.51    ~l1_struct_0(sK3) | (spl8_1 | ~spl8_20 | ~spl8_49)),
% 0.22/0.51    inference(subsumption_resolution,[],[f354,f82])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ~v2_struct_0(sK3) | spl8_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f81])).
% 0.22/0.51  fof(f354,plain,(
% 0.22/0.51    ~l1_struct_0(sK3) | v2_struct_0(sK3) | (~spl8_20 | ~spl8_49)),
% 0.22/0.51    inference(resolution,[],[f335,f160])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl8_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f159])).
% 0.22/0.51  fof(f335,plain,(
% 0.22/0.51    v1_xboole_0(u1_struct_0(sK3)) | ~spl8_49),
% 0.22/0.51    inference(avatar_component_clause,[],[f334])).
% 0.22/0.51  fof(f353,plain,(
% 0.22/0.51    ~spl8_42 | ~spl8_47 | ~spl8_43 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_12 | ~spl8_32 | spl8_48),
% 0.22/0.51    inference(avatar_split_clause,[],[f342,f328,f209,f125,f97,f93,f89,f282,f325,f279])).
% 0.22/0.51  fof(f279,plain,(
% 0.22/0.51    spl8_42 <=> v3_pre_topc(u1_struct_0(sK3),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 0.22/0.51  fof(f325,plain,(
% 0.22/0.51    spl8_47 <=> r2_hidden(sK4,u1_struct_0(sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 0.22/0.51  fof(f282,plain,(
% 0.22/0.51    spl8_43 <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    spl8_3 <=> v2_struct_0(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    spl8_4 <=> v2_pre_topc(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    spl8_12 <=> m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.22/0.51  fof(f209,plain,(
% 0.22/0.51    spl8_32 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.22/0.51  fof(f328,plain,(
% 0.22/0.51    spl8_48 <=> m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 0.22/0.51  fof(f342,plain,(
% 0.22/0.51    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | (spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_12 | ~spl8_32 | spl8_48)),
% 0.22/0.51    inference(subsumption_resolution,[],[f341,f90])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    ~v2_struct_0(sK1) | spl8_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f89])).
% 0.22/0.51  fof(f341,plain,(
% 0.22/0.51    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK4,u1_struct_0(sK3)) | v2_struct_0(sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | (~spl8_4 | ~spl8_5 | ~spl8_12 | ~spl8_32 | spl8_48)),
% 0.22/0.51    inference(subsumption_resolution,[],[f340,f126])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    m1_subset_1(sK4,u1_struct_0(sK1)) | ~spl8_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f125])).
% 0.22/0.51  fof(f340,plain,(
% 0.22/0.51    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~r2_hidden(sK4,u1_struct_0(sK3)) | v2_struct_0(sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | (~spl8_4 | ~spl8_5 | ~spl8_32 | spl8_48)),
% 0.22/0.51    inference(subsumption_resolution,[],[f339,f98])).
% 0.22/0.51  fof(f339,plain,(
% 0.22/0.51    ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~r2_hidden(sK4,u1_struct_0(sK3)) | v2_struct_0(sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | (~spl8_4 | ~spl8_32 | spl8_48)),
% 0.22/0.51    inference(subsumption_resolution,[],[f337,f94])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    v2_pre_topc(sK1) | ~spl8_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f93])).
% 0.22/0.51  fof(f337,plain,(
% 0.22/0.51    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~r2_hidden(sK4,u1_struct_0(sK3)) | v2_struct_0(sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | (~spl8_32 | spl8_48)),
% 0.22/0.51    inference(resolution,[],[f329,f210])).
% 0.22/0.51  fof(f210,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | v2_struct_0(X0) | ~v3_pre_topc(X1,X0)) ) | ~spl8_32),
% 0.22/0.51    inference(avatar_component_clause,[],[f209])).
% 0.22/0.51  fof(f329,plain,(
% 0.22/0.51    ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | spl8_48),
% 0.22/0.51    inference(avatar_component_clause,[],[f328])).
% 0.22/0.51  fof(f336,plain,(
% 0.22/0.51    spl8_49 | ~spl8_13 | ~spl8_21 | spl8_47),
% 0.22/0.51    inference(avatar_split_clause,[],[f332,f325,f163,f129,f334])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    spl8_13 <=> m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    spl8_21 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.22/0.51  fof(f332,plain,(
% 0.22/0.51    v1_xboole_0(u1_struct_0(sK3)) | (~spl8_13 | ~spl8_21 | spl8_47)),
% 0.22/0.51    inference(subsumption_resolution,[],[f331,f130])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    m1_subset_1(sK4,u1_struct_0(sK3)) | ~spl8_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f129])).
% 0.22/0.51  fof(f331,plain,(
% 0.22/0.51    v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | (~spl8_21 | spl8_47)),
% 0.22/0.51    inference(resolution,[],[f326,f164])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) ) | ~spl8_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f163])).
% 0.22/0.51  fof(f326,plain,(
% 0.22/0.51    ~r2_hidden(sK4,u1_struct_0(sK3)) | spl8_47),
% 0.22/0.51    inference(avatar_component_clause,[],[f325])).
% 0.22/0.51  fof(f330,plain,(
% 0.22/0.51    ~spl8_47 | ~spl8_48 | ~spl8_12 | ~spl8_13 | spl8_17 | ~spl8_18 | ~spl8_46),
% 0.22/0.51    inference(avatar_split_clause,[],[f323,f317,f148,f145,f129,f125,f328,f325])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    spl8_17 <=> r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    spl8_18 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.22/0.51  fof(f317,plain,(
% 0.22/0.51    spl8_46 <=> ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tmap_1(sK1,sK0,sK2,X0) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 0.22/0.51  fof(f323,plain,(
% 0.22/0.51    ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK4,u1_struct_0(sK3)) | (~spl8_12 | ~spl8_13 | spl8_17 | ~spl8_18 | ~spl8_46)),
% 0.22/0.51    inference(subsumption_resolution,[],[f322,f146])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ~r1_tmap_1(sK1,sK0,sK2,sK4) | spl8_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f145])).
% 0.22/0.51  fof(f322,plain,(
% 0.22/0.51    ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | r1_tmap_1(sK1,sK0,sK2,sK4) | ~r2_hidden(sK4,u1_struct_0(sK3)) | (~spl8_12 | ~spl8_13 | ~spl8_18 | ~spl8_46)),
% 0.22/0.51    inference(subsumption_resolution,[],[f321,f126])).
% 0.22/0.51  fof(f321,plain,(
% 0.22/0.51    ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | r1_tmap_1(sK1,sK0,sK2,sK4) | ~r2_hidden(sK4,u1_struct_0(sK3)) | (~spl8_13 | ~spl8_18 | ~spl8_46)),
% 0.22/0.51    inference(subsumption_resolution,[],[f320,f130])).
% 0.22/0.51  fof(f320,plain,(
% 0.22/0.51    ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | r1_tmap_1(sK1,sK0,sK2,sK4) | ~r2_hidden(sK4,u1_struct_0(sK3)) | (~spl8_18 | ~spl8_46)),
% 0.22/0.51    inference(resolution,[],[f318,f152])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~spl8_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f148])).
% 0.22/0.51  fof(f318,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tmap_1(sK1,sK0,sK2,X0) | ~r2_hidden(X0,u1_struct_0(sK3))) ) | ~spl8_46),
% 0.22/0.51    inference(avatar_component_clause,[],[f317])).
% 0.22/0.51  fof(f319,plain,(
% 0.22/0.51    spl8_46 | spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_14 | ~spl8_15 | ~spl8_45),
% 0.22/0.51    inference(avatar_split_clause,[],[f315,f308,f137,f133,f109,f105,f101,f317])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    spl8_6 <=> v2_struct_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    spl8_7 <=> v2_pre_topc(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    spl8_8 <=> l1_pre_topc(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    spl8_14 <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    spl8_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.22/0.51  fof(f308,plain,(
% 0.22/0.51    spl8_45 <=> ! [X1,X0] : (r1_tmap_1(sK1,X0,sK2,X1) | ~r2_hidden(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1) | v2_struct_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 0.22/0.51  fof(f315,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tmap_1(sK1,sK0,sK2,X0) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)) ) | (spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_14 | ~spl8_15 | ~spl8_45)),
% 0.22/0.51    inference(subsumption_resolution,[],[f314,f110])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    l1_pre_topc(sK0) | ~spl8_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f109])).
% 0.22/0.51  fof(f314,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tmap_1(sK1,sK0,sK2,X0) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | ~l1_pre_topc(sK0)) ) | (spl8_6 | ~spl8_7 | ~spl8_14 | ~spl8_15 | ~spl8_45)),
% 0.22/0.51    inference(subsumption_resolution,[],[f313,f138])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl8_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f137])).
% 0.22/0.51  fof(f313,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tmap_1(sK1,sK0,sK2,X0) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | (spl8_6 | ~spl8_7 | ~spl8_14 | ~spl8_45)),
% 0.22/0.51    inference(subsumption_resolution,[],[f312,f102])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    ~v2_struct_0(sK0) | spl8_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f101])).
% 0.22/0.51  fof(f312,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tmap_1(sK1,sK0,sK2,X0) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | v2_struct_0(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | (~spl8_7 | ~spl8_14 | ~spl8_45)),
% 0.22/0.51    inference(subsumption_resolution,[],[f311,f106])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    v2_pre_topc(sK0) | ~spl8_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f105])).
% 0.22/0.51  fof(f311,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tmap_1(sK1,sK0,sK2,X0) | ~v2_pre_topc(sK0) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | v2_struct_0(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | (~spl8_14 | ~spl8_45)),
% 0.22/0.51    inference(resolution,[],[f309,f134])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl8_14),
% 0.22/0.51    inference(avatar_component_clause,[],[f133])).
% 0.22/0.51  fof(f309,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(X0)) | ~r2_hidden(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | r1_tmap_1(sK1,X0,sK2,X1) | ~v2_pre_topc(X0) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1) | v2_struct_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl8_45),
% 0.22/0.51    inference(avatar_component_clause,[],[f308])).
% 0.22/0.51  fof(f310,plain,(
% 0.22/0.51    spl8_45 | ~spl8_2 | ~spl8_44),
% 0.22/0.51    inference(avatar_split_clause,[],[f306,f285,f85,f308])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl8_2 <=> v1_funct_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.51  fof(f285,plain,(
% 0.22/0.51    spl8_44 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tmap_1(sK1,X1,X2,X0) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0) | v2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~l1_pre_topc(X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).
% 0.22/0.51  fof(f306,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tmap_1(sK1,X0,sK2,X1) | ~r2_hidden(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1) | v2_struct_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | (~spl8_2 | ~spl8_44)),
% 0.22/0.51    inference(resolution,[],[f286,f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    v1_funct_1(sK2) | ~spl8_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f85])).
% 0.22/0.51  fof(f286,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | r1_tmap_1(sK1,X1,X2,X0) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0) | v2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~l1_pre_topc(X1)) ) | ~spl8_44),
% 0.22/0.51    inference(avatar_component_clause,[],[f285])).
% 0.22/0.51  fof(f302,plain,(
% 0.22/0.51    ~spl8_5 | ~spl8_11 | ~spl8_22 | spl8_43),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f301])).
% 0.22/0.51  fof(f301,plain,(
% 0.22/0.51    $false | (~spl8_5 | ~spl8_11 | ~spl8_22 | spl8_43)),
% 0.22/0.51    inference(subsumption_resolution,[],[f300,f98])).
% 0.22/0.51  fof(f300,plain,(
% 0.22/0.51    ~l1_pre_topc(sK1) | (~spl8_11 | ~spl8_22 | spl8_43)),
% 0.22/0.51    inference(subsumption_resolution,[],[f297,f122])).
% 0.22/0.51  fof(f297,plain,(
% 0.22/0.51    ~m1_pre_topc(sK3,sK1) | ~l1_pre_topc(sK1) | (~spl8_22 | spl8_43)),
% 0.22/0.51    inference(resolution,[],[f283,f168])).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl8_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f167])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    spl8_22 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.22/0.51  fof(f283,plain,(
% 0.22/0.51    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | spl8_43),
% 0.22/0.51    inference(avatar_component_clause,[],[f282])).
% 0.22/0.51  fof(f295,plain,(
% 0.22/0.51    ~spl8_4 | ~spl8_5 | ~spl8_10 | ~spl8_11 | ~spl8_24 | spl8_42),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f294])).
% 0.22/0.51  fof(f294,plain,(
% 0.22/0.51    $false | (~spl8_4 | ~spl8_5 | ~spl8_10 | ~spl8_11 | ~spl8_24 | spl8_42)),
% 0.22/0.51    inference(subsumption_resolution,[],[f293,f122])).
% 0.22/0.51  fof(f293,plain,(
% 0.22/0.51    ~m1_pre_topc(sK3,sK1) | (~spl8_4 | ~spl8_5 | ~spl8_10 | ~spl8_24 | spl8_42)),
% 0.22/0.51    inference(subsumption_resolution,[],[f292,f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    v1_tsep_1(sK3,sK1) | ~spl8_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f117])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    spl8_10 <=> v1_tsep_1(sK3,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.22/0.51  fof(f292,plain,(
% 0.22/0.51    ~v1_tsep_1(sK3,sK1) | ~m1_pre_topc(sK3,sK1) | (~spl8_4 | ~spl8_5 | ~spl8_24 | spl8_42)),
% 0.22/0.51    inference(subsumption_resolution,[],[f291,f94])).
% 0.22/0.51  fof(f291,plain,(
% 0.22/0.51    ~v2_pre_topc(sK1) | ~v1_tsep_1(sK3,sK1) | ~m1_pre_topc(sK3,sK1) | (~spl8_5 | ~spl8_24 | spl8_42)),
% 0.22/0.51    inference(subsumption_resolution,[],[f289,f98])).
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v1_tsep_1(sK3,sK1) | ~m1_pre_topc(sK3,sK1) | (~spl8_24 | spl8_42)),
% 0.22/0.51    inference(resolution,[],[f280,f176])).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) ) | ~spl8_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f175])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    spl8_24 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.22/0.51  fof(f280,plain,(
% 0.22/0.51    ~v3_pre_topc(u1_struct_0(sK3),sK1) | spl8_42),
% 0.22/0.51    inference(avatar_component_clause,[],[f279])).
% 0.22/0.51  fof(f287,plain,(
% 0.22/0.51    ~spl8_42 | ~spl8_43 | spl8_44 | spl8_1 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_11 | ~spl8_29 | ~spl8_41),
% 0.22/0.51    inference(avatar_split_clause,[],[f277,f268,f197,f121,f97,f93,f89,f81,f285,f282,f279])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    spl8_29 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | r1_tarski(sK7(X0,X1,X2),X1) | ~v3_pre_topc(X1,X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.22/0.51  fof(f268,plain,(
% 0.22/0.51    spl8_41 <=> ! [X1,X3,X2,X4] : (~r2_hidden(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(X4)) | ~r1_tarski(sK7(sK1,u1_struct_0(sK3),X1),u1_struct_0(X4)) | v2_struct_0(X2) | ~r1_tmap_1(X4,X2,k2_tmap_1(sK1,X2,X3,X4),X1) | r1_tmap_1(sK1,X2,X3,X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 0.22/0.51  fof(f277,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,u1_struct_0(sK3)) | v2_struct_0(X1) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0) | r1_tmap_1(sK1,X1,X2,X0) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(u1_struct_0(sK3),sK1)) ) | (spl8_1 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_11 | ~spl8_29 | ~spl8_41)),
% 0.22/0.51    inference(subsumption_resolution,[],[f276,f90])).
% 0.22/0.51  fof(f276,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,u1_struct_0(sK3)) | v2_struct_0(X1) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0) | r1_tmap_1(sK1,X1,X2,X0) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1)) ) | (spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_11 | ~spl8_29 | ~spl8_41)),
% 0.22/0.51    inference(subsumption_resolution,[],[f275,f98])).
% 0.22/0.51  fof(f275,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,u1_struct_0(sK3)) | v2_struct_0(X1) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0) | r1_tmap_1(sK1,X1,X2,X0) | ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1)) ) | (spl8_1 | ~spl8_4 | ~spl8_11 | ~spl8_29 | ~spl8_41)),
% 0.22/0.51    inference(subsumption_resolution,[],[f274,f94])).
% 0.22/0.51  fof(f274,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,u1_struct_0(sK3)) | v2_struct_0(X1) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0) | r1_tmap_1(sK1,X1,X2,X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1)) ) | (spl8_1 | ~spl8_11 | ~spl8_29 | ~spl8_41)),
% 0.22/0.51    inference(subsumption_resolution,[],[f273,f122])).
% 0.22/0.51  fof(f273,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,u1_struct_0(sK3)) | v2_struct_0(X1) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0) | r1_tmap_1(sK1,X1,X2,X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1)) ) | (spl8_1 | ~spl8_29 | ~spl8_41)),
% 0.22/0.51    inference(subsumption_resolution,[],[f272,f82])).
% 0.22/0.51  fof(f272,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,u1_struct_0(sK3)) | v2_struct_0(X1) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0) | r1_tmap_1(sK1,X1,X2,X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1)) ) | (~spl8_29 | ~spl8_41)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f271])).
% 0.22/0.51  fof(f271,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,u1_struct_0(sK3)) | v2_struct_0(X1) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0) | r1_tmap_1(sK1,X1,X2,X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(sK3)) | v2_struct_0(sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1)) ) | (~spl8_29 | ~spl8_41)),
% 0.22/0.51    inference(resolution,[],[f269,f198])).
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_tarski(sK7(X0,X1,X2),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | v2_struct_0(X0) | ~v3_pre_topc(X1,X0)) ) | ~spl8_29),
% 0.22/0.51    inference(avatar_component_clause,[],[f197])).
% 0.22/0.51  fof(f269,plain,(
% 0.22/0.51    ( ! [X4,X2,X3,X1] : (~r1_tarski(sK7(sK1,u1_struct_0(sK3),X1),u1_struct_0(X4)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(X4)) | ~r2_hidden(X1,u1_struct_0(sK3)) | v2_struct_0(X2) | ~r1_tmap_1(X4,X2,k2_tmap_1(sK1,X2,X3,X4),X1) | r1_tmap_1(sK1,X2,X3,X1)) ) | ~spl8_41),
% 0.22/0.51    inference(avatar_component_clause,[],[f268])).
% 0.22/0.51  fof(f270,plain,(
% 0.22/0.51    spl8_41 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_37 | ~spl8_38),
% 0.22/0.51    inference(avatar_split_clause,[],[f256,f246,f242,f97,f93,f89,f268])).
% 0.22/0.51  fof(f242,plain,(
% 0.22/0.51    spl8_37 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(sK3)) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X0),sK1,X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 0.22/0.51  fof(f246,plain,(
% 0.22/0.51    spl8_38 <=> ! [X1,X3,X0,X2,X4,X6] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 0.22/0.51  fof(f256,plain,(
% 0.22/0.51    ( ! [X4,X2,X3,X1] : (~r2_hidden(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(X4)) | ~r1_tarski(sK7(sK1,u1_struct_0(sK3),X1),u1_struct_0(X4)) | v2_struct_0(X2) | ~r1_tmap_1(X4,X2,k2_tmap_1(sK1,X2,X3,X4),X1) | r1_tmap_1(sK1,X2,X3,X1)) ) | (spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_37 | ~spl8_38)),
% 0.22/0.51    inference(subsumption_resolution,[],[f255,f98])).
% 0.22/0.51  fof(f255,plain,(
% 0.22/0.51    ( ! [X4,X2,X3,X1] : (~r2_hidden(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~l1_pre_topc(sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(X4)) | ~r1_tarski(sK7(sK1,u1_struct_0(sK3),X1),u1_struct_0(X4)) | v2_struct_0(X2) | ~r1_tmap_1(X4,X2,k2_tmap_1(sK1,X2,X3,X4),X1) | r1_tmap_1(sK1,X2,X3,X1)) ) | (spl8_3 | ~spl8_4 | ~spl8_37 | ~spl8_38)),
% 0.22/0.51    inference(subsumption_resolution,[],[f254,f94])).
% 0.22/0.51  fof(f254,plain,(
% 0.22/0.51    ( ! [X4,X2,X3,X1] : (~r2_hidden(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(X4)) | ~r1_tarski(sK7(sK1,u1_struct_0(sK3),X1),u1_struct_0(X4)) | v2_struct_0(X2) | ~r1_tmap_1(X4,X2,k2_tmap_1(sK1,X2,X3,X4),X1) | r1_tmap_1(sK1,X2,X3,X1)) ) | (spl8_3 | ~spl8_37 | ~spl8_38)),
% 0.22/0.51    inference(subsumption_resolution,[],[f250,f90])).
% 0.22/0.51  fof(f250,plain,(
% 0.22/0.51    ( ! [X4,X2,X3,X1] : (~r2_hidden(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),X1),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(X4)) | ~r1_tarski(sK7(sK1,u1_struct_0(sK3),X1),u1_struct_0(X4)) | v2_struct_0(X2) | ~r1_tmap_1(X4,X2,k2_tmap_1(sK1,X2,X3,X4),X1) | r1_tmap_1(sK1,X2,X3,X1)) ) | (~spl8_37 | ~spl8_38)),
% 0.22/0.51    inference(resolution,[],[f243,f247])).
% 0.22/0.51  % (26226)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  fof(f247,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (~m1_connsp_2(X4,X1,X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | v2_struct_0(X0) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) ) | ~spl8_38),
% 0.22/0.51    inference(avatar_component_clause,[],[f246])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    ( ! [X0] : (m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X0),sK1,X0) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | ~spl8_37),
% 0.22/0.51    inference(avatar_component_clause,[],[f242])).
% 0.22/0.51  fof(f248,plain,(
% 0.22/0.51    spl8_38 | ~spl8_25 | ~spl8_36),
% 0.22/0.51    inference(avatar_split_clause,[],[f240,f237,f181,f246])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    spl8_25 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.22/0.51  fof(f237,plain,(
% 0.22/0.51    spl8_36 <=> ! [X1,X3,X0,X2,X4,X6] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 0.22/0.51  fof(f240,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) ) | (~spl8_25 | ~spl8_36)),
% 0.22/0.51    inference(subsumption_resolution,[],[f238,f182])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X0)) ) | ~spl8_25),
% 0.22/0.51    inference(avatar_component_clause,[],[f181])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) ) | ~spl8_36),
% 0.22/0.51    inference(avatar_component_clause,[],[f237])).
% 0.22/0.51  fof(f244,plain,(
% 0.22/0.51    spl8_37 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_10 | ~spl8_11 | ~spl8_34),
% 0.22/0.51    inference(avatar_split_clause,[],[f232,f221,f121,f117,f97,f93,f89,f242])).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    spl8_34 <=> ! [X1,X0,X2] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | m1_connsp_2(sK7(X0,u1_struct_0(X1),X2),X0,X2) | v2_struct_0(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 0.22/0.51  fof(f232,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(sK3)) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X0),sK1,X0)) ) | (spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_10 | ~spl8_11 | ~spl8_34)),
% 0.22/0.51    inference(subsumption_resolution,[],[f231,f122])).
% 0.22/0.51  fof(f231,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(sK3)) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X0),sK1,X0) | ~m1_pre_topc(sK3,sK1)) ) | (spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_10 | ~spl8_34)),
% 0.22/0.51    inference(subsumption_resolution,[],[f230,f94])).
% 0.22/0.51  % (26239)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  fof(f230,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(sK3)) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X0),sK1,X0) | ~v2_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1)) ) | (spl8_3 | ~spl8_5 | ~spl8_10 | ~spl8_34)),
% 0.22/0.51    inference(subsumption_resolution,[],[f229,f90])).
% 0.22/0.51  fof(f229,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(sK3)) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X0),sK1,X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1)) ) | (~spl8_5 | ~spl8_10 | ~spl8_34)),
% 0.22/0.51    inference(subsumption_resolution,[],[f228,f98])).
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(sK3)) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X0),sK1,X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1)) ) | (~spl8_10 | ~spl8_34)),
% 0.22/0.51    inference(resolution,[],[f222,f118])).
% 0.22/0.51  fof(f222,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | m1_connsp_2(sK7(X0,u1_struct_0(X1),X2),X0,X2) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0)) ) | ~spl8_34),
% 0.22/0.51    inference(avatar_component_clause,[],[f221])).
% 0.22/0.51  fof(f239,plain,(
% 0.22/0.51    spl8_36),
% 0.22/0.51    inference(avatar_split_clause,[],[f72,f237])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.22/0.51    inference(equality_resolution,[],[f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    spl8_1 | ~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_15 | ~spl8_17 | spl8_18 | ~spl8_35),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f233])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    $false | (spl8_1 | ~spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_11 | ~spl8_13 | ~spl8_14 | ~spl8_15 | ~spl8_17 | spl8_18 | ~spl8_35)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f106,f90,f94,f98,f82,f86,f110,f102,f122,f130,f151,f134,f149,f138,f226])).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) ) | ~spl8_35),
% 0.22/0.51    inference(avatar_component_clause,[],[f225])).
% 0.22/0.51  fof(f225,plain,(
% 0.22/0.51    spl8_35 <=> ! [X1,X3,X5,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | spl8_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f148])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    r1_tmap_1(sK1,sK0,sK2,sK4) | ~spl8_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f145])).
% 0.22/0.51  fof(f227,plain,(
% 0.22/0.51    spl8_35 | ~spl8_25 | ~spl8_33),
% 0.22/0.51    inference(avatar_split_clause,[],[f219,f216,f181,f225])).
% 0.22/0.51  fof(f216,plain,(
% 0.22/0.51    spl8_33 <=> ! [X1,X3,X5,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    ( ! [X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) ) | (~spl8_25 | ~spl8_33)),
% 0.22/0.51    inference(subsumption_resolution,[],[f217,f182])).
% 0.22/0.51  fof(f217,plain,(
% 0.22/0.51    ( ! [X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) ) | ~spl8_33),
% 0.22/0.51    inference(avatar_component_clause,[],[f216])).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    spl8_34 | ~spl8_22 | ~spl8_24 | ~spl8_31),
% 0.22/0.51    inference(avatar_split_clause,[],[f214,f205,f175,f167,f221])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    spl8_31 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | m1_connsp_2(sK7(X0,X1,X2),X0,X2) | ~v3_pre_topc(X1,X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.22/0.51  fof(f214,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | m1_connsp_2(sK7(X0,u1_struct_0(X1),X2),X0,X2) | v2_struct_0(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) ) | (~spl8_22 | ~spl8_24 | ~spl8_31)),
% 0.22/0.51    inference(subsumption_resolution,[],[f213,f168])).
% 0.22/0.51  fof(f213,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | m1_connsp_2(sK7(X0,u1_struct_0(X1),X2),X0,X2) | v2_struct_0(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) ) | (~spl8_24 | ~spl8_31)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f212])).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | m1_connsp_2(sK7(X0,u1_struct_0(X1),X2),X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) ) | (~spl8_24 | ~spl8_31)),
% 0.22/0.51    inference(resolution,[],[f206,f176])).
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | m1_connsp_2(sK7(X0,X1,X2),X0,X2) | v2_struct_0(X0)) ) | ~spl8_31),
% 0.22/0.51    inference(avatar_component_clause,[],[f205])).
% 0.22/0.51  fof(f218,plain,(
% 0.22/0.51    spl8_33),
% 0.22/0.51    inference(avatar_split_clause,[],[f70,f216])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.22/0.51    inference(equality_resolution,[],[f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X1,X0,X2,X4) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    spl8_32),
% 0.22/0.51    inference(avatar_split_clause,[],[f57,f209])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    spl8_31),
% 0.22/0.51    inference(avatar_split_clause,[],[f58,f205])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | m1_connsp_2(sK7(X0,X1,X2),X0,X2) | ~v3_pre_topc(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    spl8_29),
% 0.22/0.51    inference(avatar_split_clause,[],[f59,f197])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | r1_tarski(sK7(X0,X1,X2),X1) | ~v3_pre_topc(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    spl8_25),
% 0.22/0.51    inference(avatar_split_clause,[],[f65,f181])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    spl8_24),
% 0.22/0.51    inference(avatar_split_clause,[],[f79,f175])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f74,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    spl8_22),
% 0.22/0.51    inference(avatar_split_clause,[],[f54,f167])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    spl8_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f68,f163])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    spl8_20),
% 0.22/0.51    inference(avatar_split_clause,[],[f55,f159])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    spl8_19),
% 0.22/0.51    inference(avatar_split_clause,[],[f53,f155])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    spl8_17 | spl8_18),
% 0.22/0.51    inference(avatar_split_clause,[],[f77,f148,f145])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.22/0.51    inference(forward_demodulation,[],[f35,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    sK4 = sK5),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f12])).
% 0.22/0.51  fof(f12,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    ~spl8_17 | ~spl8_18),
% 0.22/0.51    inference(avatar_split_clause,[],[f76,f148,f145])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.22/0.51    inference(forward_demodulation,[],[f36,f38])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    spl8_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f52,f141])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    spl8_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f45,f137])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    spl8_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f44,f133])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    spl8_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f75,f129])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.22/0.52    inference(forward_demodulation,[],[f37,f38])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    spl8_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f39,f125])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    spl8_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f42,f121])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    m1_pre_topc(sK3,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    spl8_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f41,f117])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    v1_tsep_1(sK3,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    spl8_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f51,f109])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    l1_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    spl8_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f50,f105])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    v2_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    ~spl8_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f49,f101])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ~v2_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    spl8_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f48,f97])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    l1_pre_topc(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    spl8_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f47,f93])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    v2_pre_topc(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ~spl8_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f46,f89])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ~v2_struct_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    spl8_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f43,f85])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    v1_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ~spl8_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f40,f81])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ~v2_struct_0(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (26231)------------------------------
% 0.22/0.52  % (26231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (26231)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (26231)Memory used [KB]: 10874
% 0.22/0.52  % (26231)Time elapsed: 0.091 s
% 0.22/0.52  % (26231)------------------------------
% 0.22/0.52  % (26231)------------------------------
% 0.22/0.52  % (26221)Success in time 0.155 s
%------------------------------------------------------------------------------
