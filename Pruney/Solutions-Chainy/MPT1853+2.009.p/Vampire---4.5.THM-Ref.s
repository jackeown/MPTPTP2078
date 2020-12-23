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
% DateTime   : Thu Dec  3 13:20:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  252 ( 433 expanded)
%              Number of leaves         :   59 ( 192 expanded)
%              Depth                    :    8
%              Number of atoms          : 1004 (1588 expanded)
%              Number of equality atoms :   27 (  38 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f432,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f93,f97,f101,f108,f111,f119,f127,f131,f135,f139,f147,f151,f155,f163,f168,f176,f184,f188,f192,f201,f207,f211,f215,f220,f230,f235,f242,f254,f269,f278,f290,f300,f306,f311,f322,f325,f353,f361,f381,f393,f402,f416,f431])).

fof(f431,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_24
    | ~ spl3_54 ),
    inference(avatar_contradiction_clause,[],[f430])).

fof(f430,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_24
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f429,f88])).

fof(f88,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f429,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_24
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f428,f96])).

fof(f96,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f428,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_24
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f427,f92])).

fof(f92,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f427,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl3_24
    | ~ spl3_54 ),
    inference(duplicate_literal_removal,[],[f426])).

fof(f426,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl3_24
    | ~ spl3_54 ),
    inference(resolution,[],[f415,f187])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl3_24
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f415,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f414])).

fof(f414,plain,
    ( spl3_54
  <=> ! [X0] :
        ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f416,plain,
    ( spl3_54
    | ~ spl3_12
    | spl3_51 ),
    inference(avatar_split_clause,[],[f408,f400,f133,f414])).

% (31127)Termination reason: Refutation not found, incomplete strategy

% (31127)Memory used [KB]: 6268
% (31127)Time elapsed: 0.105 s
% (31127)------------------------------
% (31127)------------------------------
fof(f133,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f400,plain,
    ( spl3_51
  <=> l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f408,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_12
    | spl3_51 ),
    inference(resolution,[],[f401,f134])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f401,plain,
    ( ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | spl3_51 ),
    inference(avatar_component_clause,[],[f400])).

fof(f402,plain,
    ( ~ spl3_51
    | ~ spl3_8
    | spl3_49 ),
    inference(avatar_split_clause,[],[f394,f379,f117,f400])).

fof(f117,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f379,plain,
    ( spl3_49
  <=> l1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f394,plain,
    ( ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl3_8
    | spl3_49 ),
    inference(resolution,[],[f380,f118])).

fof(f118,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f117])).

% (31128)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f380,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | spl3_49 ),
    inference(avatar_component_clause,[],[f379])).

fof(f393,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_23
    | spl3_48 ),
    inference(avatar_contradiction_clause,[],[f392])).

fof(f392,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_23
    | spl3_48 ),
    inference(subsumption_resolution,[],[f391,f88])).

fof(f391,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_23
    | spl3_48 ),
    inference(subsumption_resolution,[],[f390,f96])).

fof(f390,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_23
    | spl3_48 ),
    inference(subsumption_resolution,[],[f387,f92])).

fof(f387,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl3_23
    | spl3_48 ),
    inference(resolution,[],[f377,f183])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( v7_struct_0(k1_tex_2(X0,X1))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl3_23
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v7_struct_0(k1_tex_2(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f377,plain,
    ( ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | spl3_48 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl3_48
  <=> v7_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f381,plain,
    ( spl3_37
    | ~ spl3_48
    | ~ spl3_49
    | ~ spl3_4
    | ~ spl3_18
    | ~ spl3_43
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f374,f359,f298,f161,f99,f379,f376,f261])).

fof(f261,plain,
    ( spl3_37
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f99,plain,
    ( spl3_4
  <=> ! [X0] : ~ v1_subset_1(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f161,plain,
    ( spl3_18
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f298,plain,
    ( spl3_43
  <=> ! [X0] :
        ( ~ v7_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
        | v1_subset_1(u1_struct_0(sK0),u1_struct_0(X0))
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f359,plain,
    ( spl3_47
  <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f374,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_18
    | ~ spl3_43
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f373,f100])).

fof(f100,plain,
    ( ! [X0] : ~ v1_subset_1(X0,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f373,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl3_18
    | ~ spl3_43
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f371,f162])).

fof(f162,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f371,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl3_43
    | ~ spl3_47 ),
    inference(superposition,[],[f299,f360])).

fof(f360,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f359])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_struct_0(X0)
        | ~ v7_struct_0(X0)
        | v1_subset_1(u1_struct_0(sK0),u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f298])).

fof(f361,plain,
    ( spl3_47
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f357,f351,f103,f95,f91,f87,f359])).

fof(f103,plain,
    ( spl3_5
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f351,plain,
    ( spl3_46
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | u1_struct_0(X0) = u1_struct_0(k1_tex_2(X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v1_tex_2(k1_tex_2(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f357,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_46 ),
    inference(subsumption_resolution,[],[f356,f109])).

fof(f109,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f356,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_46 ),
    inference(subsumption_resolution,[],[f355,f88])).

fof(f355,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_46 ),
    inference(subsumption_resolution,[],[f354,f92])).

fof(f354,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl3_3
    | ~ spl3_46 ),
    inference(resolution,[],[f352,f96])).

fof(f352,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | u1_struct_0(X0) = u1_struct_0(k1_tex_2(X0,X1))
        | v2_struct_0(X0)
        | v1_tex_2(k1_tex_2(X0,X1),X0) )
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f351])).

fof(f353,plain,
    ( spl3_46
    | ~ spl3_24
    | ~ spl3_25
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f249,f240,f190,f186,f351])).

fof(f190,plain,
    ( spl3_25
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v1_tex_2(X1,X0)
        | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f240,plain,
    ( spl3_34
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X1)
        | u1_struct_0(X1) = u1_struct_0(k1_tex_2(X1,X0))
        | v1_subset_1(u1_struct_0(k1_tex_2(X1,X0)),u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | u1_struct_0(X0) = u1_struct_0(k1_tex_2(X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v1_tex_2(k1_tex_2(X0,X1),X0) )
    | ~ spl3_24
    | ~ spl3_25
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f248,f187])).

fof(f248,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | u1_struct_0(X0) = u1_struct_0(k1_tex_2(X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
        | v1_tex_2(k1_tex_2(X0,X1),X0) )
    | ~ spl3_25
    | ~ spl3_34 ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | u1_struct_0(X0) = u1_struct_0(k1_tex_2(X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
        | v1_tex_2(k1_tex_2(X0,X1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_25
    | ~ spl3_34 ),
    inference(resolution,[],[f241,f191])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_pre_topc(X1,X0)
        | v1_tex_2(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f190])).

fof(f241,plain,
    ( ! [X0,X1] :
        ( v1_subset_1(u1_struct_0(k1_tex_2(X1,X0)),u1_struct_0(X1))
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X1)
        | u1_struct_0(X1) = u1_struct_0(k1_tex_2(X1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(X1)) )
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f240])).

fof(f325,plain,
    ( ~ spl3_32
    | spl3_1
    | ~ spl3_13
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f324,f244,f137,f87,f225])).

fof(f225,plain,
    ( spl3_32
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f137,plain,
    ( spl3_13
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f244,plain,
    ( spl3_35
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f324,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_1
    | ~ spl3_13
    | ~ spl3_35 ),
    inference(subsumption_resolution,[],[f323,f88])).

fof(f323,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_13
    | ~ spl3_35 ),
    inference(resolution,[],[f321,f138])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f321,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f244])).

fof(f322,plain,
    ( spl3_35
    | ~ spl3_33
    | ~ spl3_4
    | ~ spl3_18
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f316,f288,f161,f99,f228,f244])).

fof(f228,plain,
    ( spl3_33
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f288,plain,
    ( spl3_41
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f316,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_4
    | ~ spl3_18
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f314,f100])).

fof(f314,plain,
    ( v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_18
    | ~ spl3_41 ),
    inference(resolution,[],[f289,f162])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f288])).

fof(f311,plain,
    ( ~ spl3_3
    | spl3_6
    | ~ spl3_36 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl3_3
    | spl3_6
    | ~ spl3_36 ),
    inference(unit_resulting_resolution,[],[f96,f110,f253])).

fof(f253,plain,
    ( ! [X1] :
        ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl3_36
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f110,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_6
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f306,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_21
    | ~ spl3_37 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_21
    | ~ spl3_37 ),
    inference(unit_resulting_resolution,[],[f88,f92,f96,f262,f175])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( ~ v2_struct_0(k1_tex_2(X0,X1))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f262,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f261])).

fof(f300,plain,
    ( spl3_43
    | ~ spl3_28
    | spl3_33 ),
    inference(avatar_split_clause,[],[f283,f228,f205,f298])).

fof(f205,plain,
    ( spl3_28
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v7_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v1_subset_1(X1,u1_struct_0(X0))
        | v1_zfmisc_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f283,plain,
    ( ! [X0] :
        ( ~ v7_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
        | v1_subset_1(u1_struct_0(sK0),u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl3_28
    | spl3_33 ),
    inference(resolution,[],[f229,f206])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( v1_zfmisc_1(X1)
        | ~ v7_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f205])).

fof(f229,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | spl3_33 ),
    inference(avatar_component_clause,[],[f228])).

fof(f290,plain,
    ( spl3_41
    | ~ spl3_32
    | spl3_1
    | ~ spl3_30
    | spl3_39 ),
    inference(avatar_split_clause,[],[f271,f267,f213,f87,f225,f288])).

fof(f213,plain,
    ( spl3_30
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | v7_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v1_xboole_0(X1)
        | ~ v1_zfmisc_1(X1)
        | v1_subset_1(X1,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f267,plain,
    ( spl3_39
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f271,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ v1_zfmisc_1(X0)
        | v1_subset_1(X0,u1_struct_0(sK0)) )
    | spl3_1
    | ~ spl3_30
    | spl3_39 ),
    inference(subsumption_resolution,[],[f270,f88])).

fof(f270,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ l1_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ v1_zfmisc_1(X0)
        | v1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl3_30
    | spl3_39 ),
    inference(resolution,[],[f268,f214])).

fof(f214,plain,
    ( ! [X0,X1] :
        ( v7_struct_0(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v1_xboole_0(X1)
        | ~ v1_zfmisc_1(X1)
        | v1_subset_1(X1,u1_struct_0(X0)) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f213])).

fof(f268,plain,
    ( ~ v7_struct_0(sK0)
    | spl3_39 ),
    inference(avatar_component_clause,[],[f267])).

fof(f278,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_24
    | spl3_38 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_24
    | spl3_38 ),
    inference(subsumption_resolution,[],[f276,f88])).

fof(f276,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_24
    | spl3_38 ),
    inference(subsumption_resolution,[],[f275,f96])).

fof(f275,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_24
    | spl3_38 ),
    inference(subsumption_resolution,[],[f273,f92])).

fof(f273,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl3_24
    | spl3_38 ),
    inference(resolution,[],[f265,f187])).

fof(f265,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | spl3_38 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl3_38
  <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f269,plain,
    ( spl3_37
    | ~ spl3_38
    | ~ spl3_39
    | spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f258,f199,f103,f91,f87,f267,f264,f261])).

fof(f199,plain,
    ( spl3_27
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v7_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ v1_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f258,plain,
    ( ~ v7_struct_0(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f257,f88])).

fof(f257,plain,
    ( ~ v7_struct_0(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f255,f92])).

fof(f255,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl3_5
    | ~ spl3_27 ),
    inference(resolution,[],[f104,f200])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ v1_tex_2(X1,X0)
        | ~ v7_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | v2_struct_0(X0) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f199])).

fof(f104,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f254,plain,
    ( spl3_36
    | ~ spl3_16
    | spl3_33 ),
    inference(avatar_split_clause,[],[f237,f228,f149,f252])).

fof(f149,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( v1_zfmisc_1(X0)
        | ~ m1_subset_1(X1,X0)
        | v1_subset_1(k6_domain_1(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f237,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) )
    | ~ spl3_16
    | spl3_33 ),
    inference(resolution,[],[f229,f150])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( v1_zfmisc_1(X0)
        | ~ m1_subset_1(X1,X0)
        | v1_subset_1(k6_domain_1(X0,X1),X0) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f149])).

fof(f242,plain,
    ( spl3_34
    | ~ spl3_15
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f216,f209,f145,f240])).

fof(f145,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | X0 = X1
        | v1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f209,plain,
    ( spl3_29
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0)
        | m1_subset_1(u1_struct_0(k1_tex_2(X0,X1)),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f216,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X1)
        | u1_struct_0(X1) = u1_struct_0(k1_tex_2(X1,X0))
        | v1_subset_1(u1_struct_0(k1_tex_2(X1,X0)),u1_struct_0(X1)) )
    | ~ spl3_15
    | ~ spl3_29 ),
    inference(resolution,[],[f210,f146])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | X0 = X1
        | v1_subset_1(X1,X0) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f145])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(u1_struct_0(k1_tex_2(X0,X1)),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f209])).

fof(f235,plain,
    ( ~ spl3_2
    | ~ spl3_8
    | spl3_32 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_8
    | spl3_32 ),
    inference(subsumption_resolution,[],[f232,f92])).

fof(f232,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_8
    | spl3_32 ),
    inference(resolution,[],[f226,f118])).

fof(f226,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_32 ),
    inference(avatar_component_clause,[],[f225])).

fof(f230,plain,
    ( ~ spl3_32
    | ~ spl3_33
    | spl3_1
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f223,f218,f106,f95,f87,f228,f225])).

fof(f218,plain,
    ( spl3_31
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
        | ~ v1_zfmisc_1(u1_struct_0(X1))
        | ~ l1_struct_0(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f223,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | spl3_1
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f222,f88])).

fof(f222,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f221,f96])).

fof(f221,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_6
    | ~ spl3_31 ),
    inference(resolution,[],[f219,f107])).

fof(f107,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ v1_zfmisc_1(u1_struct_0(X1))
        | ~ l1_struct_0(X1)
        | v2_struct_0(X1) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f218])).

fof(f220,plain,
    ( spl3_31
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f197,f166,f137,f218])).

fof(f166,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0)
        | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
        | ~ v1_zfmisc_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
        | ~ v1_zfmisc_1(u1_struct_0(X1))
        | ~ l1_struct_0(X1)
        | v2_struct_0(X1) )
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(resolution,[],[f167,f138])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0)
        | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
        | ~ v1_zfmisc_1(X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f166])).

fof(f215,plain,(
    spl3_30 ),
    inference(avatar_split_clause,[],[f63,f213])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ v1_zfmisc_1(X1)
      | v1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc8_tex_2)).

fof(f211,plain,
    ( spl3_29
    | ~ spl3_17
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f203,f186,f153,f209])).

fof(f153,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0)
        | m1_subset_1(u1_struct_0(k1_tex_2(X0,X1)),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl3_17
    | ~ spl3_24 ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | m1_subset_1(u1_struct_0(k1_tex_2(X0,X1)),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl3_17
    | ~ spl3_24 ),
    inference(resolution,[],[f187,f154])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f153])).

fof(f207,plain,(
    spl3_28 ),
    inference(avatar_split_clause,[],[f85,f205])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_subset_1(X1,u1_struct_0(X0))
      | v1_zfmisc_1(X1) ) ),
    inference(subsumption_resolution,[],[f65,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | v1_subset_1(X1,u1_struct_0(X0))
      | v1_zfmisc_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
          | v1_subset_1(X1,u1_struct_0(X0))
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
          | v1_subset_1(X1,u1_struct_0(X0))
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) )
           => ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc7_tex_2)).

fof(f201,plain,(
    spl3_27 ),
    inference(avatar_split_clause,[],[f66,f199])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v7_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

fof(f192,plain,(
    spl3_25 ),
    inference(avatar_split_clause,[],[f82,f190])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_tex_2(X1,X0)
      | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f78,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0)
      | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v1_tex_2(X1,X0)
      | ~ v1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v1_subset_1(X2,u1_struct_0(X0))
                <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).

fof(f188,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f74,f186])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f184,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f76,f182])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v7_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f176,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f72,f174])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f168,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f55,f166])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f163,plain,
    ( spl3_18
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f158,f145,f129,f125,f161])).

fof(f125,plain,
    ( spl3_10
  <=> ! [X0] : ~ v1_subset_1(sK2(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f129,plain,
    ( spl3_11
  <=> ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f158,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f130,f157])).

fof(f157,plain,
    ( ! [X0] : sK2(X0) = X0
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f156,f126])).

fof(f126,plain,
    ( ! [X0] : ~ v1_subset_1(sK2(X0),X0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f156,plain,
    ( ! [X0] :
        ( sK2(X0) = X0
        | v1_subset_1(sK2(X0),X0) )
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(resolution,[],[f146,f130])).

fof(f130,plain,
    ( ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f155,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f58,f153])).

fof(f151,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f84,f149])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_subset_1(k6_domain_1(X0,X1),X0) ) ),
    inference(subsumption_resolution,[],[f62,f61])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_subset_1(k6_domain_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(f147,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f70,f145])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f139,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f64,f137])).

fof(f64,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f135,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f57,f133])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f131,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f68,f129])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f127,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f69,f125])).

fof(f69,plain,(
    ! [X0] : ~ v1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f119,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f56,f117])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f111,plain,
    ( ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f49,f106,f103])).

fof(f49,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f108,plain,
    ( spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f48,f106,f103])).

fof(f48,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f22])).

% (31128)Refutation not found, incomplete strategy% (31128)------------------------------
% (31128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f101,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f81,f99])).

% (31128)Termination reason: Refutation not found, incomplete strategy

% (31128)Memory used [KB]: 10746
% (31128)Time elapsed: 0.128 s
% (31128)------------------------------
% (31128)------------------------------
fof(f81,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f53,f54])).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f53,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f97,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f50,f95])).

fof(f50,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f93,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f52,f91])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f89,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f51,f87])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:24:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (31136)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.48  % (31130)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (31132)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (31130)Refutation not found, incomplete strategy% (31130)------------------------------
% 0.20/0.48  % (31130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (31130)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (31130)Memory used [KB]: 1663
% 0.20/0.48  % (31130)Time elapsed: 0.072 s
% 0.20/0.48  % (31130)------------------------------
% 0.20/0.48  % (31130)------------------------------
% 0.20/0.48  % (31132)Refutation not found, incomplete strategy% (31132)------------------------------
% 0.20/0.48  % (31132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (31132)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (31132)Memory used [KB]: 6140
% 0.20/0.48  % (31132)Time elapsed: 0.074 s
% 0.20/0.48  % (31132)------------------------------
% 0.20/0.48  % (31132)------------------------------
% 0.20/0.48  % (31124)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (31129)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (31117)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (31122)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (31121)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (31131)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (31137)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (31129)Refutation not found, incomplete strategy% (31129)------------------------------
% 0.20/0.50  % (31129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (31129)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (31129)Memory used [KB]: 6396
% 0.20/0.50  % (31129)Time elapsed: 0.089 s
% 0.20/0.50  % (31129)------------------------------
% 0.20/0.50  % (31129)------------------------------
% 0.20/0.50  % (31134)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (31120)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (31118)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (31119)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (31123)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.51  % (31120)Refutation not found, incomplete strategy% (31120)------------------------------
% 0.20/0.51  % (31120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31120)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (31120)Memory used [KB]: 10618
% 0.20/0.51  % (31120)Time elapsed: 0.092 s
% 0.20/0.51  % (31120)------------------------------
% 0.20/0.51  % (31120)------------------------------
% 0.20/0.51  % (31118)Refutation not found, incomplete strategy% (31118)------------------------------
% 0.20/0.51  % (31118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31118)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (31118)Memory used [KB]: 10618
% 0.20/0.51  % (31118)Time elapsed: 0.091 s
% 0.20/0.51  % (31118)------------------------------
% 0.20/0.51  % (31118)------------------------------
% 0.20/0.51  % (31117)Refutation not found, incomplete strategy% (31117)------------------------------
% 0.20/0.51  % (31117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31117)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (31117)Memory used [KB]: 6268
% 0.20/0.51  % (31117)Time elapsed: 0.054 s
% 0.20/0.51  % (31117)------------------------------
% 0.20/0.51  % (31117)------------------------------
% 0.20/0.51  % (31127)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (31125)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.52  % (31126)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.52  % (31127)Refutation not found, incomplete strategy% (31127)------------------------------
% 0.20/0.52  % (31127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31137)Refutation not found, incomplete strategy% (31137)------------------------------
% 0.20/0.52  % (31137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31135)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.52  % (31126)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (31133)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.52  % (31137)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (31137)Memory used [KB]: 10618
% 0.20/0.52  % (31137)Time elapsed: 0.103 s
% 0.20/0.52  % (31137)------------------------------
% 0.20/0.52  % (31137)------------------------------
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f432,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f89,f93,f97,f101,f108,f111,f119,f127,f131,f135,f139,f147,f151,f155,f163,f168,f176,f184,f188,f192,f201,f207,f211,f215,f220,f230,f235,f242,f254,f269,f278,f290,f300,f306,f311,f322,f325,f353,f361,f381,f393,f402,f416,f431])).
% 0.20/0.52  fof(f431,plain,(
% 0.20/0.52    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_24 | ~spl3_54),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f430])).
% 0.20/0.52  fof(f430,plain,(
% 0.20/0.52    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_24 | ~spl3_54)),
% 0.20/0.52    inference(subsumption_resolution,[],[f429,f88])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    ~v2_struct_0(sK0) | spl3_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f87])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    spl3_1 <=> v2_struct_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.52  fof(f429,plain,(
% 0.20/0.52    v2_struct_0(sK0) | (~spl3_2 | ~spl3_3 | ~spl3_24 | ~spl3_54)),
% 0.20/0.52    inference(subsumption_resolution,[],[f428,f96])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f95])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    spl3_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.52  fof(f428,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl3_2 | ~spl3_24 | ~spl3_54)),
% 0.20/0.52    inference(subsumption_resolution,[],[f427,f92])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    l1_pre_topc(sK0) | ~spl3_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f91])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    spl3_2 <=> l1_pre_topc(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.52  fof(f427,plain,(
% 0.20/0.52    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl3_24 | ~spl3_54)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f426])).
% 0.20/0.52  fof(f426,plain,(
% 0.20/0.52    ~l1_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl3_24 | ~spl3_54)),
% 0.20/0.52    inference(resolution,[],[f415,f187])).
% 0.20/0.52  fof(f187,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl3_24),
% 0.20/0.52    inference(avatar_component_clause,[],[f186])).
% 0.20/0.52  fof(f186,plain,(
% 0.20/0.52    spl3_24 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.52  fof(f415,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | ~spl3_54),
% 0.20/0.52    inference(avatar_component_clause,[],[f414])).
% 0.20/0.52  fof(f414,plain,(
% 0.20/0.52    spl3_54 <=> ! [X0] : (~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | ~l1_pre_topc(X0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.20/0.52  fof(f416,plain,(
% 0.20/0.52    spl3_54 | ~spl3_12 | spl3_51),
% 0.20/0.52    inference(avatar_split_clause,[],[f408,f400,f133,f414])).
% 0.20/0.52  % (31127)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (31127)Memory used [KB]: 6268
% 0.20/0.52  % (31127)Time elapsed: 0.105 s
% 0.20/0.52  % (31127)------------------------------
% 0.20/0.52  % (31127)------------------------------
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    spl3_12 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.53  fof(f400,plain,(
% 0.20/0.53    spl3_51 <=> l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.20/0.53  fof(f408,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | (~spl3_12 | spl3_51)),
% 0.20/0.53    inference(resolution,[],[f401,f134])).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl3_12),
% 0.20/0.53    inference(avatar_component_clause,[],[f133])).
% 0.20/0.53  fof(f401,plain,(
% 0.20/0.53    ~l1_pre_topc(k1_tex_2(sK0,sK1)) | spl3_51),
% 0.20/0.53    inference(avatar_component_clause,[],[f400])).
% 0.20/0.53  fof(f402,plain,(
% 0.20/0.53    ~spl3_51 | ~spl3_8 | spl3_49),
% 0.20/0.53    inference(avatar_split_clause,[],[f394,f379,f117,f400])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    spl3_8 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.53  fof(f379,plain,(
% 0.20/0.53    spl3_49 <=> l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.20/0.53  fof(f394,plain,(
% 0.20/0.53    ~l1_pre_topc(k1_tex_2(sK0,sK1)) | (~spl3_8 | spl3_49)),
% 0.20/0.53    inference(resolution,[],[f380,f118])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl3_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f117])).
% 0.20/0.53  % (31128)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.53  fof(f380,plain,(
% 0.20/0.53    ~l1_struct_0(k1_tex_2(sK0,sK1)) | spl3_49),
% 0.20/0.53    inference(avatar_component_clause,[],[f379])).
% 0.20/0.53  fof(f393,plain,(
% 0.20/0.53    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_23 | spl3_48),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f392])).
% 0.20/0.53  fof(f392,plain,(
% 0.20/0.53    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_23 | spl3_48)),
% 0.20/0.53    inference(subsumption_resolution,[],[f391,f88])).
% 0.20/0.53  fof(f391,plain,(
% 0.20/0.53    v2_struct_0(sK0) | (~spl3_2 | ~spl3_3 | ~spl3_23 | spl3_48)),
% 0.20/0.53    inference(subsumption_resolution,[],[f390,f96])).
% 0.20/0.53  fof(f390,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl3_2 | ~spl3_23 | spl3_48)),
% 0.20/0.53    inference(subsumption_resolution,[],[f387,f92])).
% 0.20/0.53  fof(f387,plain,(
% 0.20/0.53    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl3_23 | spl3_48)),
% 0.20/0.53    inference(resolution,[],[f377,f183])).
% 0.20/0.53  fof(f183,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl3_23),
% 0.20/0.53    inference(avatar_component_clause,[],[f182])).
% 0.20/0.53  fof(f182,plain,(
% 0.20/0.53    spl3_23 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v7_struct_0(k1_tex_2(X0,X1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.53  fof(f377,plain,(
% 0.20/0.53    ~v7_struct_0(k1_tex_2(sK0,sK1)) | spl3_48),
% 0.20/0.53    inference(avatar_component_clause,[],[f376])).
% 0.20/0.53  fof(f376,plain,(
% 0.20/0.53    spl3_48 <=> v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.20/0.53  fof(f381,plain,(
% 0.20/0.53    spl3_37 | ~spl3_48 | ~spl3_49 | ~spl3_4 | ~spl3_18 | ~spl3_43 | ~spl3_47),
% 0.20/0.53    inference(avatar_split_clause,[],[f374,f359,f298,f161,f99,f379,f376,f261])).
% 0.20/0.53  fof(f261,plain,(
% 0.20/0.53    spl3_37 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    spl3_4 <=> ! [X0] : ~v1_subset_1(X0,X0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.53  fof(f161,plain,(
% 0.20/0.53    spl3_18 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.53  fof(f298,plain,(
% 0.20/0.53    spl3_43 <=> ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_subset_1(u1_struct_0(sK0),u1_struct_0(X0)) | v2_struct_0(X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.20/0.53  fof(f359,plain,(
% 0.20/0.53    spl3_47 <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.20/0.53  fof(f374,plain,(
% 0.20/0.53    ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | (~spl3_4 | ~spl3_18 | ~spl3_43 | ~spl3_47)),
% 0.20/0.53    inference(subsumption_resolution,[],[f373,f100])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_subset_1(X0,X0)) ) | ~spl3_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f99])).
% 0.20/0.53  fof(f373,plain,(
% 0.20/0.53    ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | v2_struct_0(k1_tex_2(sK0,sK1)) | (~spl3_18 | ~spl3_43 | ~spl3_47)),
% 0.20/0.53    inference(subsumption_resolution,[],[f371,f162])).
% 0.20/0.53  fof(f162,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl3_18),
% 0.20/0.53    inference(avatar_component_clause,[],[f161])).
% 0.20/0.53  fof(f371,plain,(
% 0.20/0.53    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | v2_struct_0(k1_tex_2(sK0,sK1)) | (~spl3_43 | ~spl3_47)),
% 0.20/0.53    inference(superposition,[],[f299,f360])).
% 0.20/0.53  fof(f360,plain,(
% 0.20/0.53    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~spl3_47),
% 0.20/0.53    inference(avatar_component_clause,[],[f359])).
% 0.20/0.53  fof(f299,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | ~v7_struct_0(X0) | v1_subset_1(u1_struct_0(sK0),u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl3_43),
% 0.20/0.53    inference(avatar_component_clause,[],[f298])).
% 0.20/0.53  fof(f361,plain,(
% 0.20/0.53    spl3_47 | spl3_1 | ~spl3_2 | ~spl3_3 | spl3_5 | ~spl3_46),
% 0.20/0.53    inference(avatar_split_clause,[],[f357,f351,f103,f95,f91,f87,f359])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    spl3_5 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.53  fof(f351,plain,(
% 0.20/0.53    spl3_46 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.20/0.53  fof(f357,plain,(
% 0.20/0.53    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | (spl3_1 | ~spl3_2 | ~spl3_3 | spl3_5 | ~spl3_46)),
% 0.20/0.53    inference(subsumption_resolution,[],[f356,f109])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | spl3_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f103])).
% 0.20/0.53  fof(f356,plain,(
% 0.20/0.53    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_46)),
% 0.20/0.53    inference(subsumption_resolution,[],[f355,f88])).
% 0.20/0.53  fof(f355,plain,(
% 0.20/0.53    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl3_2 | ~spl3_3 | ~spl3_46)),
% 0.20/0.53    inference(subsumption_resolution,[],[f354,f92])).
% 0.20/0.53  fof(f354,plain,(
% 0.20/0.53    ~l1_pre_topc(sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl3_3 | ~spl3_46)),
% 0.20/0.53    inference(resolution,[],[f352,f96])).
% 0.20/0.53  fof(f352,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(k1_tex_2(X0,X1)) | v2_struct_0(X0) | v1_tex_2(k1_tex_2(X0,X1),X0)) ) | ~spl3_46),
% 0.20/0.53    inference(avatar_component_clause,[],[f351])).
% 0.20/0.53  fof(f353,plain,(
% 0.20/0.53    spl3_46 | ~spl3_24 | ~spl3_25 | ~spl3_34),
% 0.20/0.53    inference(avatar_split_clause,[],[f249,f240,f190,f186,f351])).
% 0.20/0.53  fof(f190,plain,(
% 0.20/0.53    spl3_25 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_tex_2(X1,X0) | ~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.53  fof(f240,plain,(
% 0.20/0.53    spl3_34 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_pre_topc(X1) | u1_struct_0(X1) = u1_struct_0(k1_tex_2(X1,X0)) | v1_subset_1(u1_struct_0(k1_tex_2(X1,X0)),u1_struct_0(X1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.53  fof(f249,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) ) | (~spl3_24 | ~spl3_25 | ~spl3_34)),
% 0.20/0.53    inference(subsumption_resolution,[],[f248,f187])).
% 0.20/0.53  fof(f248,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | v1_tex_2(k1_tex_2(X0,X1),X0)) ) | (~spl3_25 | ~spl3_34)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f247])).
% 0.20/0.53  fof(f247,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | v1_tex_2(k1_tex_2(X0,X1),X0) | ~l1_pre_topc(X0)) ) | (~spl3_25 | ~spl3_34)),
% 0.20/0.53    inference(resolution,[],[f241,f191])).
% 0.20/0.53  fof(f191,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v1_tex_2(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl3_25),
% 0.20/0.53    inference(avatar_component_clause,[],[f190])).
% 0.20/0.53  fof(f241,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(k1_tex_2(X1,X0)),u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_pre_topc(X1) | u1_struct_0(X1) = u1_struct_0(k1_tex_2(X1,X0)) | ~m1_subset_1(X0,u1_struct_0(X1))) ) | ~spl3_34),
% 0.20/0.53    inference(avatar_component_clause,[],[f240])).
% 0.20/0.53  fof(f325,plain,(
% 0.20/0.53    ~spl3_32 | spl3_1 | ~spl3_13 | ~spl3_35),
% 0.20/0.53    inference(avatar_split_clause,[],[f324,f244,f137,f87,f225])).
% 0.20/0.53  fof(f225,plain,(
% 0.20/0.53    spl3_32 <=> l1_struct_0(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.53  fof(f137,plain,(
% 0.20/0.53    spl3_13 <=> ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.53  fof(f244,plain,(
% 0.20/0.53    spl3_35 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.53  fof(f324,plain,(
% 0.20/0.53    ~l1_struct_0(sK0) | (spl3_1 | ~spl3_13 | ~spl3_35)),
% 0.20/0.53    inference(subsumption_resolution,[],[f323,f88])).
% 0.20/0.53  fof(f323,plain,(
% 0.20/0.53    ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl3_13 | ~spl3_35)),
% 0.20/0.53    inference(resolution,[],[f321,f138])).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl3_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f137])).
% 0.20/0.53  fof(f321,plain,(
% 0.20/0.53    v1_xboole_0(u1_struct_0(sK0)) | ~spl3_35),
% 0.20/0.53    inference(avatar_component_clause,[],[f244])).
% 0.20/0.53  fof(f322,plain,(
% 0.20/0.53    spl3_35 | ~spl3_33 | ~spl3_4 | ~spl3_18 | ~spl3_41),
% 0.20/0.53    inference(avatar_split_clause,[],[f316,f288,f161,f99,f228,f244])).
% 0.20/0.53  fof(f228,plain,(
% 0.20/0.53    spl3_33 <=> v1_zfmisc_1(u1_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.53  fof(f288,plain,(
% 0.20/0.53    spl3_41 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(X0,u1_struct_0(sK0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.20/0.53  fof(f316,plain,(
% 0.20/0.53    ~v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl3_4 | ~spl3_18 | ~spl3_41)),
% 0.20/0.53    inference(subsumption_resolution,[],[f314,f100])).
% 0.20/0.53  fof(f314,plain,(
% 0.20/0.53    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl3_18 | ~spl3_41)),
% 0.20/0.53    inference(resolution,[],[f289,f162])).
% 0.20/0.53  fof(f289,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(X0,u1_struct_0(sK0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) ) | ~spl3_41),
% 0.20/0.53    inference(avatar_component_clause,[],[f288])).
% 0.20/0.53  fof(f311,plain,(
% 0.20/0.53    ~spl3_3 | spl3_6 | ~spl3_36),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f309])).
% 0.20/0.53  fof(f309,plain,(
% 0.20/0.53    $false | (~spl3_3 | spl3_6 | ~spl3_36)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f96,f110,f253])).
% 0.20/0.53  fof(f253,plain,(
% 0.20/0.53    ( ! [X1] : (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl3_36),
% 0.20/0.53    inference(avatar_component_clause,[],[f252])).
% 0.20/0.53  fof(f252,plain,(
% 0.20/0.53    spl3_36 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl3_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f106])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    spl3_6 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.53  fof(f306,plain,(
% 0.20/0.53    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_21 | ~spl3_37),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f303])).
% 0.20/0.53  fof(f303,plain,(
% 0.20/0.53    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_21 | ~spl3_37)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f88,f92,f96,f262,f175])).
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl3_21),
% 0.20/0.53    inference(avatar_component_clause,[],[f174])).
% 0.20/0.53  fof(f174,plain,(
% 0.20/0.53    spl3_21 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_struct_0(k1_tex_2(X0,X1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl3_37),
% 0.20/0.53    inference(avatar_component_clause,[],[f261])).
% 0.20/0.53  fof(f300,plain,(
% 0.20/0.53    spl3_43 | ~spl3_28 | spl3_33),
% 0.20/0.53    inference(avatar_split_clause,[],[f283,f228,f205,f298])).
% 0.20/0.53  fof(f205,plain,(
% 0.20/0.53    spl3_28 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v7_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_subset_1(X1,u1_struct_0(X0)) | v1_zfmisc_1(X1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.53  fof(f283,plain,(
% 0.20/0.53    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_subset_1(u1_struct_0(sK0),u1_struct_0(X0)) | v2_struct_0(X0)) ) | (~spl3_28 | spl3_33)),
% 0.20/0.53    inference(resolution,[],[f229,f206])).
% 0.20/0.53  fof(f206,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v7_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl3_28),
% 0.20/0.53    inference(avatar_component_clause,[],[f205])).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    ~v1_zfmisc_1(u1_struct_0(sK0)) | spl3_33),
% 0.20/0.53    inference(avatar_component_clause,[],[f228])).
% 0.20/0.53  fof(f290,plain,(
% 0.20/0.53    spl3_41 | ~spl3_32 | spl3_1 | ~spl3_30 | spl3_39),
% 0.20/0.53    inference(avatar_split_clause,[],[f271,f267,f213,f87,f225,f288])).
% 0.20/0.53  fof(f213,plain,(
% 0.20/0.53    spl3_30 <=> ! [X1,X0] : (v2_struct_0(X0) | v7_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~v1_zfmisc_1(X1) | v1_subset_1(X1,u1_struct_0(X0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.53  fof(f267,plain,(
% 0.20/0.53    spl3_39 <=> v7_struct_0(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.20/0.53  fof(f271,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0) | v1_subset_1(X0,u1_struct_0(sK0))) ) | (spl3_1 | ~spl3_30 | spl3_39)),
% 0.20/0.53    inference(subsumption_resolution,[],[f270,f88])).
% 0.20/0.53  fof(f270,plain,(
% 0.20/0.53    ( ! [X0] : (v2_struct_0(sK0) | ~l1_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0) | v1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl3_30 | spl3_39)),
% 0.20/0.53    inference(resolution,[],[f268,f214])).
% 0.20/0.53  fof(f214,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v7_struct_0(X0) | v2_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~v1_zfmisc_1(X1) | v1_subset_1(X1,u1_struct_0(X0))) ) | ~spl3_30),
% 0.20/0.53    inference(avatar_component_clause,[],[f213])).
% 0.20/0.53  fof(f268,plain,(
% 0.20/0.53    ~v7_struct_0(sK0) | spl3_39),
% 0.20/0.53    inference(avatar_component_clause,[],[f267])).
% 0.20/0.53  fof(f278,plain,(
% 0.20/0.53    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_24 | spl3_38),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f277])).
% 0.20/0.53  fof(f277,plain,(
% 0.20/0.53    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_24 | spl3_38)),
% 0.20/0.53    inference(subsumption_resolution,[],[f276,f88])).
% 0.20/0.53  fof(f276,plain,(
% 0.20/0.53    v2_struct_0(sK0) | (~spl3_2 | ~spl3_3 | ~spl3_24 | spl3_38)),
% 0.20/0.53    inference(subsumption_resolution,[],[f275,f96])).
% 0.20/0.53  fof(f275,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl3_2 | ~spl3_24 | spl3_38)),
% 0.20/0.53    inference(subsumption_resolution,[],[f273,f92])).
% 0.20/0.53  fof(f273,plain,(
% 0.20/0.53    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl3_24 | spl3_38)),
% 0.20/0.53    inference(resolution,[],[f265,f187])).
% 0.20/0.53  fof(f265,plain,(
% 0.20/0.53    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | spl3_38),
% 0.20/0.53    inference(avatar_component_clause,[],[f264])).
% 0.20/0.53  fof(f264,plain,(
% 0.20/0.53    spl3_38 <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.20/0.53  fof(f269,plain,(
% 0.20/0.53    spl3_37 | ~spl3_38 | ~spl3_39 | spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_27),
% 0.20/0.53    inference(avatar_split_clause,[],[f258,f199,f103,f91,f87,f267,f264,f261])).
% 0.20/0.53  fof(f199,plain,(
% 0.20/0.53    spl3_27 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v7_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~v1_tex_2(X1,X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.53  fof(f258,plain,(
% 0.20/0.53    ~v7_struct_0(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | (spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_27)),
% 0.20/0.53    inference(subsumption_resolution,[],[f257,f88])).
% 0.20/0.53  fof(f257,plain,(
% 0.20/0.53    ~v7_struct_0(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | (~spl3_2 | ~spl3_5 | ~spl3_27)),
% 0.20/0.53    inference(subsumption_resolution,[],[f255,f92])).
% 0.20/0.53  fof(f255,plain,(
% 0.20/0.53    ~v7_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | (~spl3_5 | ~spl3_27)),
% 0.20/0.53    inference(resolution,[],[f104,f200])).
% 0.20/0.53  fof(f200,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | ~v7_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v2_struct_0(X0)) ) | ~spl3_27),
% 0.20/0.53    inference(avatar_component_clause,[],[f199])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl3_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f103])).
% 0.20/0.53  fof(f254,plain,(
% 0.20/0.53    spl3_36 | ~spl3_16 | spl3_33),
% 0.20/0.53    inference(avatar_split_clause,[],[f237,f228,f149,f252])).
% 0.20/0.53  fof(f149,plain,(
% 0.20/0.53    spl3_16 <=> ! [X1,X0] : (v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | v1_subset_1(k6_domain_1(X0,X1),X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.53  fof(f237,plain,(
% 0.20/0.53    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))) ) | (~spl3_16 | spl3_33)),
% 0.20/0.53    inference(resolution,[],[f229,f150])).
% 0.20/0.53  fof(f150,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | v1_subset_1(k6_domain_1(X0,X1),X0)) ) | ~spl3_16),
% 0.20/0.53    inference(avatar_component_clause,[],[f149])).
% 0.20/0.53  fof(f242,plain,(
% 0.20/0.53    spl3_34 | ~spl3_15 | ~spl3_29),
% 0.20/0.53    inference(avatar_split_clause,[],[f216,f209,f145,f240])).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    spl3_15 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.53  fof(f209,plain,(
% 0.20/0.53    spl3_29 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_subset_1(u1_struct_0(k1_tex_2(X0,X1)),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.53  fof(f216,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_pre_topc(X1) | u1_struct_0(X1) = u1_struct_0(k1_tex_2(X1,X0)) | v1_subset_1(u1_struct_0(k1_tex_2(X1,X0)),u1_struct_0(X1))) ) | (~spl3_15 | ~spl3_29)),
% 0.20/0.53    inference(resolution,[],[f210,f146])).
% 0.20/0.53  fof(f146,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) ) | ~spl3_15),
% 0.20/0.53    inference(avatar_component_clause,[],[f145])).
% 0.20/0.53  fof(f210,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(k1_tex_2(X0,X1)),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl3_29),
% 0.20/0.53    inference(avatar_component_clause,[],[f209])).
% 0.20/0.53  fof(f235,plain,(
% 0.20/0.53    ~spl3_2 | ~spl3_8 | spl3_32),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f234])).
% 0.20/0.53  fof(f234,plain,(
% 0.20/0.53    $false | (~spl3_2 | ~spl3_8 | spl3_32)),
% 0.20/0.53    inference(subsumption_resolution,[],[f232,f92])).
% 0.20/0.53  fof(f232,plain,(
% 0.20/0.53    ~l1_pre_topc(sK0) | (~spl3_8 | spl3_32)),
% 0.20/0.53    inference(resolution,[],[f226,f118])).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    ~l1_struct_0(sK0) | spl3_32),
% 0.20/0.53    inference(avatar_component_clause,[],[f225])).
% 0.20/0.53  fof(f230,plain,(
% 0.20/0.53    ~spl3_32 | ~spl3_33 | spl3_1 | ~spl3_3 | ~spl3_6 | ~spl3_31),
% 0.20/0.53    inference(avatar_split_clause,[],[f223,f218,f106,f95,f87,f228,f225])).
% 0.20/0.53  fof(f218,plain,(
% 0.20/0.53    spl3_31 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1)) | ~v1_zfmisc_1(u1_struct_0(X1)) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.53  fof(f223,plain,(
% 0.20/0.53    ~v1_zfmisc_1(u1_struct_0(sK0)) | ~l1_struct_0(sK0) | (spl3_1 | ~spl3_3 | ~spl3_6 | ~spl3_31)),
% 0.20/0.53    inference(subsumption_resolution,[],[f222,f88])).
% 0.20/0.53  fof(f222,plain,(
% 0.20/0.53    ~v1_zfmisc_1(u1_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl3_3 | ~spl3_6 | ~spl3_31)),
% 0.20/0.53    inference(subsumption_resolution,[],[f221,f96])).
% 0.20/0.53  fof(f221,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v1_zfmisc_1(u1_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl3_6 | ~spl3_31)),
% 0.20/0.53    inference(resolution,[],[f219,f107])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl3_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f106])).
% 0.20/0.53  fof(f219,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v1_zfmisc_1(u1_struct_0(X1)) | ~l1_struct_0(X1) | v2_struct_0(X1)) ) | ~spl3_31),
% 0.20/0.53    inference(avatar_component_clause,[],[f218])).
% 0.20/0.53  fof(f220,plain,(
% 0.20/0.53    spl3_31 | ~spl3_13 | ~spl3_19),
% 0.20/0.53    inference(avatar_split_clause,[],[f197,f166,f137,f218])).
% 0.20/0.53  fof(f166,plain,(
% 0.20/0.53    spl3_19 <=> ! [X1,X0] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~v1_zfmisc_1(X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.53  fof(f197,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1)) | ~v1_zfmisc_1(u1_struct_0(X1)) | ~l1_struct_0(X1) | v2_struct_0(X1)) ) | (~spl3_13 | ~spl3_19)),
% 0.20/0.53    inference(resolution,[],[f167,f138])).
% 0.20/0.53  fof(f167,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~v1_zfmisc_1(X0)) ) | ~spl3_19),
% 0.20/0.53    inference(avatar_component_clause,[],[f166])).
% 0.20/0.53  fof(f215,plain,(
% 0.20/0.53    spl3_30),
% 0.20/0.53    inference(avatar_split_clause,[],[f63,f213])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | v7_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~v1_zfmisc_1(X1) | v1_subset_1(X1,u1_struct_0(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc8_tex_2)).
% 0.20/0.53  fof(f211,plain,(
% 0.20/0.53    spl3_29 | ~spl3_17 | ~spl3_24),
% 0.20/0.53    inference(avatar_split_clause,[],[f203,f186,f153,f209])).
% 0.20/0.53  fof(f153,plain,(
% 0.20/0.53    spl3_17 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.53  fof(f203,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_subset_1(u1_struct_0(k1_tex_2(X0,X1)),k1_zfmisc_1(u1_struct_0(X0)))) ) | (~spl3_17 | ~spl3_24)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f202])).
% 0.20/0.53  fof(f202,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(k1_tex_2(X0,X1)),k1_zfmisc_1(u1_struct_0(X0)))) ) | (~spl3_17 | ~spl3_24)),
% 0.20/0.53    inference(resolution,[],[f187,f154])).
% 0.20/0.53  fof(f154,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl3_17),
% 0.20/0.53    inference(avatar_component_clause,[],[f153])).
% 0.20/0.53  fof(f207,plain,(
% 0.20/0.53    spl3_28),
% 0.20/0.53    inference(avatar_split_clause,[],[f85,f205])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~v7_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_subset_1(X1,u1_struct_0(X0)) | v1_zfmisc_1(X1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f65,f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(X0) | v1_zfmisc_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~v7_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | v1_subset_1(X1,u1_struct_0(X0)) | v1_zfmisc_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) | v1_subset_1(X1,u1_struct_0(X0)) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) | (v1_subset_1(X1,u1_struct_0(X0)) | v1_xboole_0(X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) => (v1_zfmisc_1(X1) & ~v1_xboole_0(X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc7_tex_2)).
% 0.20/0.53  fof(f201,plain,(
% 0.20/0.53    spl3_27),
% 0.20/0.53    inference(avatar_split_clause,[],[f66,f199])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~v7_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~v1_tex_2(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).
% 0.20/0.53  fof(f192,plain,(
% 0.20/0.53    spl3_25),
% 0.20/0.53    inference(avatar_split_clause,[],[f82,f190])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_tex_2(X1,X0) | ~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f78,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0) | ~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.20/0.53    inference(equality_resolution,[],[f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).
% 0.20/0.53  fof(f188,plain,(
% 0.20/0.53    spl3_24),
% 0.20/0.53    inference(avatar_split_clause,[],[f74,f186])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.20/0.53  fof(f184,plain,(
% 0.20/0.53    spl3_23),
% 0.20/0.53    inference(avatar_split_clause,[],[f76,f182])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v7_struct_0(k1_tex_2(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.20/0.53  fof(f176,plain,(
% 0.20/0.53    spl3_21),
% 0.20/0.53    inference(avatar_split_clause,[],[f72,f174])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_struct_0(k1_tex_2(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f45])).
% 0.20/0.53  fof(f168,plain,(
% 0.20/0.53    spl3_19),
% 0.20/0.53    inference(avatar_split_clause,[],[f55,f166])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~v1_zfmisc_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 0.20/0.53    inference(flattening,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,axiom,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    spl3_18 | ~spl3_10 | ~spl3_11 | ~spl3_15),
% 0.20/0.53    inference(avatar_split_clause,[],[f158,f145,f129,f125,f161])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    spl3_10 <=> ! [X0] : ~v1_subset_1(sK2(X0),X0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    spl3_11 <=> ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.53  fof(f158,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | (~spl3_10 | ~spl3_11 | ~spl3_15)),
% 0.20/0.53    inference(backward_demodulation,[],[f130,f157])).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    ( ! [X0] : (sK2(X0) = X0) ) | (~spl3_10 | ~spl3_11 | ~spl3_15)),
% 0.20/0.53    inference(subsumption_resolution,[],[f156,f126])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_subset_1(sK2(X0),X0)) ) | ~spl3_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f125])).
% 0.20/0.53  fof(f156,plain,(
% 0.20/0.53    ( ! [X0] : (sK2(X0) = X0 | v1_subset_1(sK2(X0),X0)) ) | (~spl3_11 | ~spl3_15)),
% 0.20/0.53    inference(resolution,[],[f146,f130])).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(X0))) ) | ~spl3_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f129])).
% 0.20/0.53  fof(f155,plain,(
% 0.20/0.53    spl3_17),
% 0.20/0.53    inference(avatar_split_clause,[],[f58,f153])).
% 0.20/0.53  fof(f151,plain,(
% 0.20/0.53    spl3_16),
% 0.20/0.53    inference(avatar_split_clause,[],[f84,f149])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | v1_subset_1(k6_domain_1(X0,X1),X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f62,f61])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | v1_subset_1(k6_domain_1(X0,X1),X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.53    inference(flattening,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,axiom,(
% 0.20/0.53    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).
% 0.20/0.53  fof(f147,plain,(
% 0.20/0.53    spl3_15),
% 0.20/0.53    inference(avatar_split_clause,[],[f70,f145])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    spl3_13),
% 0.20/0.53    inference(avatar_split_clause,[],[f64,f137])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    spl3_12),
% 0.20/0.53    inference(avatar_split_clause,[],[f57,f133])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    spl3_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f68,f129])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    spl3_10),
% 0.20/0.53    inference(avatar_split_clause,[],[f69,f125])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_subset_1(sK2(X0),X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    spl3_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f56,f117])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    ~spl3_5 | ~spl3_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f49,f106,f103])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.20/0.53    inference(negated_conjecture,[],[f19])).
% 0.20/0.53  fof(f19,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    spl3_5 | spl3_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f48,f106,f103])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  % (31128)Refutation not found, incomplete strategy% (31128)------------------------------
% 0.20/0.53  % (31128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    spl3_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f81,f99])).
% 0.20/0.53  % (31128)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31128)Memory used [KB]: 10746
% 0.20/0.53  % (31128)Time elapsed: 0.128 s
% 0.20/0.53  % (31128)------------------------------
% 0.20/0.53  % (31128)------------------------------
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.20/0.53    inference(backward_demodulation,[],[f53,f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    spl3_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f50,f95])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    spl3_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f52,f91])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ~spl3_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f51,f87])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ~v2_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (31126)------------------------------
% 0.20/0.53  % (31126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31126)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (31126)Memory used [KB]: 10746
% 0.20/0.53  % (31126)Time elapsed: 0.128 s
% 0.20/0.53  % (31126)------------------------------
% 0.20/0.53  % (31126)------------------------------
% 0.20/0.53  % (31113)Success in time 0.169 s
%------------------------------------------------------------------------------
