%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 265 expanded)
%              Number of leaves         :   35 ( 116 expanded)
%              Depth                    :    8
%              Number of atoms          :  561 (1063 expanded)
%              Number of equality atoms :   49 (  96 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f271,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f52,f60,f64,f68,f72,f76,f80,f84,f88,f92,f96,f100,f104,f121,f127,f133,f141,f161,f170,f189,f197,f202,f221,f236,f244,f255,f270])).

fof(f270,plain,
    ( ~ spl3_37
    | spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_14
    | spl3_36
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f262,f253,f231,f98,f62,f58,f50,f234])).

fof(f234,plain,
    ( spl3_37
  <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f50,plain,
    ( spl3_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f58,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f62,plain,
    ( spl3_5
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f98,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v3_tex_2(sK2(X0,X1),X0)
        | v4_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f231,plain,
    ( spl3_36
  <=> v4_tex_2(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f253,plain,
    ( spl3_39
  <=> sK1 = sK2(sK0,k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f262,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_14
    | spl3_36
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f261,f232])).

fof(f232,plain,
    ( ~ v4_tex_2(k1_pre_topc(sK0,sK1),sK0)
    | spl3_36 ),
    inference(avatar_component_clause,[],[f231])).

fof(f261,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | v4_tex_2(k1_pre_topc(sK0,sK1),sK0)
    | spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_14
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f260,f51])).

fof(f51,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f260,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | v4_tex_2(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_14
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f259,f59])).

fof(f59,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f259,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | v4_tex_2(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_5
    | ~ spl3_14
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f258,f63])).

fof(f63,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f258,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | v4_tex_2(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_14
    | ~ spl3_39 ),
    inference(superposition,[],[f99,f254])).

fof(f254,plain,
    ( sK1 = sK2(sK0,k1_pre_topc(sK0,sK1))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f253])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ v3_tex_2(sK2(X0,X1),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0)
        | v4_tex_2(X1,X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f98])).

fof(f255,plain,
    ( ~ spl3_37
    | spl3_39
    | spl3_2
    | ~ spl3_4
    | ~ spl3_15
    | ~ spl3_26
    | spl3_36 ),
    inference(avatar_split_clause,[],[f247,f231,f159,f102,f58,f50,f253,f234])).

fof(f102,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | u1_struct_0(X1) = sK2(X0,X1)
        | v4_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f159,plain,
    ( spl3_26
  <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f247,plain,
    ( sK1 = sK2(sK0,k1_pre_topc(sK0,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | spl3_2
    | ~ spl3_4
    | ~ spl3_15
    | ~ spl3_26
    | spl3_36 ),
    inference(forward_demodulation,[],[f246,f160])).

fof(f160,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f159])).

fof(f246,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK2(sK0,k1_pre_topc(sK0,sK1))
    | spl3_2
    | ~ spl3_4
    | ~ spl3_15
    | spl3_36 ),
    inference(subsumption_resolution,[],[f245,f51])).

fof(f245,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK2(sK0,k1_pre_topc(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl3_4
    | ~ spl3_15
    | spl3_36 ),
    inference(subsumption_resolution,[],[f238,f59])).

fof(f238,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK2(sK0,k1_pre_topc(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl3_15
    | spl3_36 ),
    inference(resolution,[],[f232,f103])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( v4_tex_2(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | u1_struct_0(X1) = sK2(X0,X1)
        | v2_struct_0(X0) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f102])).

fof(f244,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | ~ spl3_13
    | spl3_37 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_13
    | spl3_37 ),
    inference(subsumption_resolution,[],[f242,f59])).

fof(f242,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_6
    | ~ spl3_13
    | spl3_37 ),
    inference(subsumption_resolution,[],[f240,f67])).

fof(f67,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f240,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_13
    | spl3_37 ),
    inference(resolution,[],[f235,f95])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f235,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | spl3_37 ),
    inference(avatar_component_clause,[],[f234])).

fof(f236,plain,
    ( spl3_34
    | ~ spl3_36
    | ~ spl3_37
    | ~ spl3_30
    | ~ spl3_8
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f212,f159,f74,f178,f234,f231,f219])).

fof(f219,plain,
    ( spl3_34
  <=> v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f178,plain,
    ( spl3_30
  <=> v1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f74,plain,
    ( spl3_8
  <=> ! [X2] :
        ( v2_struct_0(X2)
        | ~ v1_pre_topc(X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ v4_tex_2(X2,sK0)
        | u1_struct_0(X2) != sK1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f212,plain,
    ( ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ v4_tex_2(k1_pre_topc(sK0,sK1),sK0)
    | v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_8
    | ~ spl3_26 ),
    inference(trivial_inequality_removal,[],[f204])).

fof(f204,plain,
    ( sK1 != sK1
    | ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ v4_tex_2(k1_pre_topc(sK0,sK1),sK0)
    | v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_8
    | ~ spl3_26 ),
    inference(superposition,[],[f75,f160])).

fof(f75,plain,
    ( ! [X2] :
        ( u1_struct_0(X2) != sK1
        | ~ v1_pre_topc(X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ v4_tex_2(X2,sK0)
        | v2_struct_0(X2) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f221,plain,
    ( ~ spl3_34
    | ~ spl3_25
    | spl3_1
    | ~ spl3_11
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f215,f159,f86,f46,f156,f219])).

fof(f156,plain,
    ( spl3_25
  <=> l1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f46,plain,
    ( spl3_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f86,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | v1_xboole_0(u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f215,plain,
    ( ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ v2_struct_0(k1_pre_topc(sK0,sK1))
    | spl3_1
    | ~ spl3_11
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f205,f47])).

fof(f47,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f205,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_11
    | ~ spl3_26 ),
    inference(superposition,[],[f87,f160])).

fof(f87,plain,
    ( ! [X0] :
        ( v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | ~ v2_struct_0(X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f86])).

fof(f202,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_33 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f200,f67])).

fof(f200,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f199,f59])).

fof(f199,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_13
    | ~ spl3_33 ),
    inference(duplicate_literal_removal,[],[f198])).

fof(f198,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_13
    | ~ spl3_33 ),
    inference(resolution,[],[f196,f95])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f195])).

% (2495)Refutation not found, incomplete strategy% (2495)------------------------------
% (2495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f195,plain,
    ( spl3_33
  <=> ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

% (2495)Termination reason: Refutation not found, incomplete strategy

% (2495)Memory used [KB]: 1663
% (2495)Time elapsed: 0.078 s
% (2495)------------------------------
% (2495)------------------------------
fof(f197,plain,
    ( spl3_33
    | ~ spl3_10
    | spl3_28 ),
    inference(avatar_split_clause,[],[f175,f168,f82,f195])).

fof(f82,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f168,plain,
    ( spl3_28
  <=> l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_10
    | spl3_28 ),
    inference(resolution,[],[f169,f83])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f169,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f168])).

fof(f189,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | ~ spl3_12
    | spl3_30 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_12
    | spl3_30 ),
    inference(subsumption_resolution,[],[f187,f59])).

fof(f187,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_6
    | ~ spl3_12
    | spl3_30 ),
    inference(subsumption_resolution,[],[f185,f67])).

fof(f185,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_12
    | spl3_30 ),
    inference(resolution,[],[f179,f91])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( v1_pre_topc(k1_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f179,plain,
    ( ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f178])).

fof(f170,plain,
    ( ~ spl3_28
    | ~ spl3_7
    | spl3_25 ),
    inference(avatar_split_clause,[],[f162,f156,f70,f168])).

fof(f70,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f162,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl3_7
    | spl3_25 ),
    inference(resolution,[],[f157,f71])).

fof(f71,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f157,plain,
    ( ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f156])).

fof(f161,plain,
    ( ~ spl3_25
    | spl3_26
    | ~ spl3_9
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f146,f139,f78,f159,f156])).

fof(f78,plain,
    ( spl3_9
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f139,plain,
    ( spl3_22
  <=> sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f146,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_9
    | ~ spl3_22 ),
    inference(superposition,[],[f140,f79])).

fof(f79,plain,
    ( ! [X0] :
        ( u1_struct_0(X0) = k2_struct_0(X0)
        | ~ l1_struct_0(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f140,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f139])).

fof(f141,plain,
    ( spl3_22
    | ~ spl3_6
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f134,f131,f66,f139])).

fof(f131,plain,
    ( spl3_21
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(k1_pre_topc(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f134,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_6
    | ~ spl3_21 ),
    inference(resolution,[],[f132,f67])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(k1_pre_topc(sK0,X0)) = X0 )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f131])).

fof(f133,plain,
    ( spl3_21
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f128,f125,f58,f131])).

fof(f125,plain,
    ( spl3_20
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(k1_pre_topc(sK0,X0)) = X0 )
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(resolution,[],[f126,f59])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_struct_0(k1_pre_topc(X0,X1)) = X1 )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f125])).

fof(f127,plain,
    ( spl3_20
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f123,f119,f94,f90,f125])).

fof(f119,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_pre_topc(k1_pre_topc(X0,X1))
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
        | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_struct_0(k1_pre_topc(X0,X1)) = X1 )
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f122,f95])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
        | k2_struct_0(k1_pre_topc(X0,X1)) = X1 )
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f120,f91])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_pre_topc(k1_pre_topc(X0,X1))
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
        | k2_struct_0(k1_pre_topc(X0,X1)) = X1 )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f42,f119])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f104,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f37,f102])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v4_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_tex_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

fof(f100,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f38,f98])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v3_tex_2(sK2(X0,X1),X0)
      | v4_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f96,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f41,f94])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f92,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f40,f90])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f88,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f39,f86])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f84,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f32,f82])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f80,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f30,f78])).

fof(f30,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f76,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f23,f74])).

fof(f23,plain,(
    ! [X2] :
      ( v2_struct_0(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ v4_tex_2(X2,sK0)
      | u1_struct_0(X2) != sK1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ~ ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_pre_topc(X2)
                      & ~ v2_struct_0(X2) )
                   => ~ ( u1_struct_0(X2) = X1
                        & v4_tex_2(X2,X0) ) )
                & v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => ~ ( u1_struct_0(X2) = X1
                      & v4_tex_2(X2,X0) ) )
              & v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).

fof(f72,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f31,f70])).

fof(f31,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f68,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f25,f66])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f26,f62])).

fof(f26,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f29,f58])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f27,f50])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:57:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (2489)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (2487)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (2497)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (2491)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (2495)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (2498)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (2490)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (2499)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (2491)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f271,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f48,f52,f60,f64,f68,f72,f76,f80,f84,f88,f92,f96,f100,f104,f121,f127,f133,f141,f161,f170,f189,f197,f202,f221,f236,f244,f255,f270])).
% 0.22/0.50  fof(f270,plain,(
% 0.22/0.50    ~spl3_37 | spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_14 | spl3_36 | ~spl3_39),
% 0.22/0.50    inference(avatar_split_clause,[],[f262,f253,f231,f98,f62,f58,f50,f234])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    spl3_37 <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    spl3_2 <=> v2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    spl3_4 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    spl3_5 <=> v3_tex_2(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    spl3_14 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_tex_2(sK2(X0,X1),X0) | v4_tex_2(X1,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.50  fof(f231,plain,(
% 0.22/0.50    spl3_36 <=> v4_tex_2(k1_pre_topc(sK0,sK1),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.50  fof(f253,plain,(
% 0.22/0.50    spl3_39 <=> sK1 = sK2(sK0,k1_pre_topc(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.22/0.50  fof(f262,plain,(
% 0.22/0.50    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_14 | spl3_36 | ~spl3_39)),
% 0.22/0.50    inference(subsumption_resolution,[],[f261,f232])).
% 0.22/0.50  fof(f232,plain,(
% 0.22/0.50    ~v4_tex_2(k1_pre_topc(sK0,sK1),sK0) | spl3_36),
% 0.22/0.50    inference(avatar_component_clause,[],[f231])).
% 0.22/0.50  fof(f261,plain,(
% 0.22/0.50    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | v4_tex_2(k1_pre_topc(sK0,sK1),sK0) | (spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_14 | ~spl3_39)),
% 0.22/0.50    inference(subsumption_resolution,[],[f260,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ~v2_struct_0(sK0) | spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f50])).
% 0.22/0.50  fof(f260,plain,(
% 0.22/0.50    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | v2_struct_0(sK0) | v4_tex_2(k1_pre_topc(sK0,sK1),sK0) | (~spl3_4 | ~spl3_5 | ~spl3_14 | ~spl3_39)),
% 0.22/0.50    inference(subsumption_resolution,[],[f259,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    l1_pre_topc(sK0) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f58])).
% 0.22/0.50  fof(f259,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | v2_struct_0(sK0) | v4_tex_2(k1_pre_topc(sK0,sK1),sK0) | (~spl3_5 | ~spl3_14 | ~spl3_39)),
% 0.22/0.50    inference(subsumption_resolution,[],[f258,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    v3_tex_2(sK1,sK0) | ~spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f62])).
% 0.22/0.50  fof(f258,plain,(
% 0.22/0.50    ~v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | v2_struct_0(sK0) | v4_tex_2(k1_pre_topc(sK0,sK1),sK0) | (~spl3_14 | ~spl3_39)),
% 0.22/0.50    inference(superposition,[],[f99,f254])).
% 0.22/0.50  fof(f254,plain,(
% 0.22/0.50    sK1 = sK2(sK0,k1_pre_topc(sK0,sK1)) | ~spl3_39),
% 0.22/0.50    inference(avatar_component_clause,[],[f253])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v3_tex_2(sK2(X0,X1),X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | v4_tex_2(X1,X0)) ) | ~spl3_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f98])).
% 0.22/0.50  fof(f255,plain,(
% 0.22/0.50    ~spl3_37 | spl3_39 | spl3_2 | ~spl3_4 | ~spl3_15 | ~spl3_26 | spl3_36),
% 0.22/0.50    inference(avatar_split_clause,[],[f247,f231,f159,f102,f58,f50,f253,f234])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    spl3_15 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | v4_tex_2(X1,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    spl3_26 <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.50  fof(f247,plain,(
% 0.22/0.50    sK1 = sK2(sK0,k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (spl3_2 | ~spl3_4 | ~spl3_15 | ~spl3_26 | spl3_36)),
% 0.22/0.50    inference(forward_demodulation,[],[f246,f160])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_26),
% 0.22/0.50    inference(avatar_component_clause,[],[f159])).
% 0.22/0.50  fof(f246,plain,(
% 0.22/0.50    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK2(sK0,k1_pre_topc(sK0,sK1)) | (spl3_2 | ~spl3_4 | ~spl3_15 | spl3_36)),
% 0.22/0.50    inference(subsumption_resolution,[],[f245,f51])).
% 0.22/0.50  fof(f245,plain,(
% 0.22/0.50    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK2(sK0,k1_pre_topc(sK0,sK1)) | v2_struct_0(sK0) | (~spl3_4 | ~spl3_15 | spl3_36)),
% 0.22/0.50    inference(subsumption_resolution,[],[f238,f59])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK2(sK0,k1_pre_topc(sK0,sK1)) | v2_struct_0(sK0) | (~spl3_15 | spl3_36)),
% 0.22/0.50    inference(resolution,[],[f232,f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v4_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | v2_struct_0(X0)) ) | ~spl3_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f102])).
% 0.22/0.50  fof(f244,plain,(
% 0.22/0.50    ~spl3_4 | ~spl3_6 | ~spl3_13 | spl3_37),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f243])).
% 0.22/0.50  fof(f243,plain,(
% 0.22/0.50    $false | (~spl3_4 | ~spl3_6 | ~spl3_13 | spl3_37)),
% 0.22/0.50    inference(subsumption_resolution,[],[f242,f59])).
% 0.22/0.50  fof(f242,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | (~spl3_6 | ~spl3_13 | spl3_37)),
% 0.22/0.50    inference(subsumption_resolution,[],[f240,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_13 | spl3_37)),
% 0.22/0.50    inference(resolution,[],[f235,f95])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f94])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    spl3_13 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.50  fof(f235,plain,(
% 0.22/0.50    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | spl3_37),
% 0.22/0.50    inference(avatar_component_clause,[],[f234])).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    spl3_34 | ~spl3_36 | ~spl3_37 | ~spl3_30 | ~spl3_8 | ~spl3_26),
% 0.22/0.50    inference(avatar_split_clause,[],[f212,f159,f74,f178,f234,f231,f219])).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    spl3_34 <=> v2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    spl3_30 <=> v1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    spl3_8 <=> ! [X2] : (v2_struct_0(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,sK0) | ~v4_tex_2(X2,sK0) | u1_struct_0(X2) != sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    ~v1_pre_topc(k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~v4_tex_2(k1_pre_topc(sK0,sK1),sK0) | v2_struct_0(k1_pre_topc(sK0,sK1)) | (~spl3_8 | ~spl3_26)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f204])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    sK1 != sK1 | ~v1_pre_topc(k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~v4_tex_2(k1_pre_topc(sK0,sK1),sK0) | v2_struct_0(k1_pre_topc(sK0,sK1)) | (~spl3_8 | ~spl3_26)),
% 0.22/0.50    inference(superposition,[],[f75,f160])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X2] : (u1_struct_0(X2) != sK1 | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,sK0) | ~v4_tex_2(X2,sK0) | v2_struct_0(X2)) ) | ~spl3_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f74])).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    ~spl3_34 | ~spl3_25 | spl3_1 | ~spl3_11 | ~spl3_26),
% 0.22/0.50    inference(avatar_split_clause,[],[f215,f159,f86,f46,f156,f219])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    spl3_25 <=> l1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    spl3_1 <=> v1_xboole_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    spl3_11 <=> ! [X0] : (~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    ~l1_struct_0(k1_pre_topc(sK0,sK1)) | ~v2_struct_0(k1_pre_topc(sK0,sK1)) | (spl3_1 | ~spl3_11 | ~spl3_26)),
% 0.22/0.50    inference(subsumption_resolution,[],[f205,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ~v1_xboole_0(sK1) | spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f46])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    v1_xboole_0(sK1) | ~l1_struct_0(k1_pre_topc(sK0,sK1)) | ~v2_struct_0(k1_pre_topc(sK0,sK1)) | (~spl3_11 | ~spl3_26)),
% 0.22/0.50    inference(superposition,[],[f87,f160])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) ) | ~spl3_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f86])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    ~spl3_4 | ~spl3_6 | ~spl3_13 | ~spl3_33),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f201])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    $false | (~spl3_4 | ~spl3_6 | ~spl3_13 | ~spl3_33)),
% 0.22/0.50    inference(subsumption_resolution,[],[f200,f67])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_4 | ~spl3_13 | ~spl3_33)),
% 0.22/0.50    inference(subsumption_resolution,[],[f199,f59])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_13 | ~spl3_33)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f198])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_13 | ~spl3_33)),
% 0.22/0.50    inference(resolution,[],[f196,f95])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | ~spl3_33),
% 0.22/0.50    inference(avatar_component_clause,[],[f195])).
% 0.22/0.50  % (2495)Refutation not found, incomplete strategy% (2495)------------------------------
% 0.22/0.50  % (2495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    spl3_33 <=> ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.50  % (2495)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (2495)Memory used [KB]: 1663
% 0.22/0.50  % (2495)Time elapsed: 0.078 s
% 0.22/0.50  % (2495)------------------------------
% 0.22/0.50  % (2495)------------------------------
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    spl3_33 | ~spl3_10 | spl3_28),
% 0.22/0.50    inference(avatar_split_clause,[],[f175,f168,f82,f195])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    spl3_10 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    spl3_28 <=> l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | (~spl3_10 | spl3_28)),
% 0.22/0.50    inference(resolution,[],[f169,f83])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl3_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f82])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | spl3_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f168])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    ~spl3_4 | ~spl3_6 | ~spl3_12 | spl3_30),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f188])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    $false | (~spl3_4 | ~spl3_6 | ~spl3_12 | spl3_30)),
% 0.22/0.50    inference(subsumption_resolution,[],[f187,f59])).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | (~spl3_6 | ~spl3_12 | spl3_30)),
% 0.22/0.50    inference(subsumption_resolution,[],[f185,f67])).
% 0.22/0.50  fof(f185,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_12 | spl3_30)),
% 0.22/0.50    inference(resolution,[],[f179,f91])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl3_12 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    ~v1_pre_topc(k1_pre_topc(sK0,sK1)) | spl3_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f178])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    ~spl3_28 | ~spl3_7 | spl3_25),
% 0.22/0.50    inference(avatar_split_clause,[],[f162,f156,f70,f168])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    spl3_7 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | (~spl3_7 | spl3_25)),
% 0.22/0.50    inference(resolution,[],[f157,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl3_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f70])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ~l1_struct_0(k1_pre_topc(sK0,sK1)) | spl3_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f156])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    ~spl3_25 | spl3_26 | ~spl3_9 | ~spl3_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f146,f139,f78,f159,f156])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl3_9 <=> ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    spl3_22 <=> sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~l1_struct_0(k1_pre_topc(sK0,sK1)) | (~spl3_9 | ~spl3_22)),
% 0.22/0.50    inference(superposition,[],[f140,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) ) | ~spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f78])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f139])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    spl3_22 | ~spl3_6 | ~spl3_21),
% 0.22/0.50    inference(avatar_split_clause,[],[f134,f131,f66,f139])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    spl3_21 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(k1_pre_topc(sK0,X0)) = X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) | (~spl3_6 | ~spl3_21)),
% 0.22/0.50    inference(resolution,[],[f132,f67])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(k1_pre_topc(sK0,X0)) = X0) ) | ~spl3_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f131])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl3_21 | ~spl3_4 | ~spl3_20),
% 0.22/0.50    inference(avatar_split_clause,[],[f128,f125,f58,f131])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    spl3_20 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(k1_pre_topc(X0,X1)) = X1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(k1_pre_topc(sK0,X0)) = X0) ) | (~spl3_4 | ~spl3_20)),
% 0.22/0.50    inference(resolution,[],[f126,f59])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) ) | ~spl3_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f125])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    spl3_20 | ~spl3_12 | ~spl3_13 | ~spl3_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f123,f119,f94,f90,f125])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    spl3_19 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) ) | (~spl3_12 | ~spl3_13 | ~spl3_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f122,f95])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) ) | (~spl3_12 | ~spl3_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f120,f91])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) ) | ~spl3_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f119])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    spl3_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f42,f119])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.22/0.50    inference(equality_resolution,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    spl3_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f102])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | v4_tex_2(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    spl3_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f38,f98])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_tex_2(sK2(X0,X1),X0) | v4_tex_2(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    spl3_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f41,f94])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f40,f90])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl3_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f39,f86])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f32,f82])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f78])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f23,f74])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X2] : (v2_struct_0(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,sK0) | ~v4_tex_2(X2,sK0) | u1_struct_0(X2) != sK1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((! [X2] : ((u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) & v3_tex_2(X1,X0)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 0.22/0.50    inference(negated_conjecture,[],[f8])).
% 0.22/0.50  fof(f8,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f31,f70])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f25,f66])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f62])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    v3_tex_2(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f29,f58])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ~spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f27,f50])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ~spl3_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f24,f46])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ~v1_xboole_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (2491)------------------------------
% 0.22/0.50  % (2491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (2491)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (2491)Memory used [KB]: 10746
% 0.22/0.50  % (2491)Time elapsed: 0.059 s
% 0.22/0.50  % (2491)------------------------------
% 0.22/0.50  % (2491)------------------------------
% 0.22/0.50  % (2481)Success in time 0.139 s
%------------------------------------------------------------------------------
