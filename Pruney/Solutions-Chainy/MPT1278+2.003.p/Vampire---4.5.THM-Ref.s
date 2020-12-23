%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  237 ( 468 expanded)
%              Number of leaves         :   56 ( 217 expanded)
%              Depth                    :   10
%              Number of atoms          :  814 (1498 expanded)
%              Number of equality atoms :   84 ( 191 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f534,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f71,f75,f79,f83,f87,f91,f99,f103,f107,f111,f119,f123,f133,f137,f141,f150,f161,f172,f176,f182,f201,f205,f213,f218,f229,f238,f253,f270,f274,f301,f305,f312,f325,f345,f349,f369,f391,f479,f492,f521,f533])).

fof(f533,plain,
    ( spl2_5
    | ~ spl2_29
    | ~ spl2_50
    | ~ spl2_63 ),
    inference(avatar_contradiction_clause,[],[f532])).

fof(f532,plain,
    ( $false
    | spl2_5
    | ~ spl2_29
    | ~ spl2_50
    | ~ spl2_63 ),
    inference(subsumption_resolution,[],[f531,f82])).

fof(f82,plain,
    ( k1_xboole_0 != sK1
    | spl2_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl2_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f531,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_29
    | ~ spl2_50
    | ~ spl2_63 ),
    inference(forward_demodulation,[],[f523,f390])).

fof(f390,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1)
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl2_50
  <=> ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f523,plain,
    ( sK1 = k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl2_29
    | ~ spl2_63 ),
    inference(backward_demodulation,[],[f200,f520])).

fof(f520,plain,
    ( u1_struct_0(sK0) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl2_63 ),
    inference(avatar_component_clause,[],[f519])).

fof(f519,plain,
    ( spl2_63
  <=> u1_struct_0(sK0) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).

fof(f200,plain,
    ( sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl2_29
  <=> sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f521,plain,
    ( ~ spl2_59
    | spl2_63
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_19
    | ~ spl2_25
    | ~ spl2_35
    | ~ spl2_46
    | ~ spl2_48
    | ~ spl2_58 ),
    inference(avatar_split_clause,[],[f493,f474,f367,f347,f236,f174,f148,f101,f69,f519,f477])).

fof(f477,plain,
    ( spl2_59
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f69,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f101,plain,
    ( spl2_10
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f148,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f174,plain,
    ( spl2_25
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = k2_struct_0(X0)
        | ~ v1_tops_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f236,plain,
    ( spl2_35
  <=> v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f347,plain,
    ( spl2_46
  <=> v1_tops_1(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f367,plain,
    ( spl2_48
  <=> v4_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f474,plain,
    ( spl2_58
  <=> k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f493,plain,
    ( u1_struct_0(sK0) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_19
    | ~ spl2_25
    | ~ spl2_35
    | ~ spl2_46
    | ~ spl2_48
    | ~ spl2_58 ),
    inference(backward_demodulation,[],[f386,f475])).

fof(f475,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_58 ),
    inference(avatar_component_clause,[],[f474])).

fof(f386,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_19
    | ~ spl2_25
    | ~ spl2_35
    | ~ spl2_46
    | ~ spl2_48 ),
    inference(backward_demodulation,[],[f244,f384])).

fof(f384,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_19
    | ~ spl2_25
    | ~ spl2_46
    | ~ spl2_48 ),
    inference(backward_demodulation,[],[f359,f383])).

fof(f383,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_19
    | ~ spl2_48 ),
    inference(subsumption_resolution,[],[f382,f70])).

fof(f70,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f382,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ spl2_10
    | ~ spl2_19
    | ~ spl2_48 ),
    inference(subsumption_resolution,[],[f378,f102])).

fof(f102,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f378,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ spl2_19
    | ~ spl2_48 ),
    inference(resolution,[],[f368,f149])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | k2_pre_topc(X0,X1) = X1 )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f148])).

fof(f368,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f367])).

fof(f359,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_25
    | ~ spl2_46 ),
    inference(subsumption_resolution,[],[f358,f70])).

fof(f358,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_10
    | ~ spl2_25
    | ~ spl2_46 ),
    inference(subsumption_resolution,[],[f357,f102])).

fof(f357,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_25
    | ~ spl2_46 ),
    inference(resolution,[],[f348,f175])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( ~ v1_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = k2_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f174])).

fof(f348,plain,
    ( v1_tops_1(u1_struct_0(sK0),sK0)
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f347])).

fof(f244,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_25
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f243,f70])).

fof(f243,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_25
    | ~ spl2_35 ),
    inference(resolution,[],[f237,f175])).

fof(f237,plain,
    ( v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f236])).

fof(f492,plain,
    ( ~ spl2_6
    | ~ spl2_42
    | spl2_59 ),
    inference(avatar_contradiction_clause,[],[f491])).

fof(f491,plain,
    ( $false
    | ~ spl2_6
    | ~ spl2_42
    | spl2_59 ),
    inference(subsumption_resolution,[],[f489,f86])).

fof(f86,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f489,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_42
    | spl2_59 ),
    inference(resolution,[],[f478,f311])).

fof(f311,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl2_42
  <=> ! [X1,X0] :
        ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f478,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_59 ),
    inference(avatar_component_clause,[],[f477])).

fof(f479,plain,
    ( spl2_58
    | ~ spl2_59
    | ~ spl2_2
    | ~ spl2_19
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f317,f303,f148,f69,f477,f474])).

fof(f303,plain,
    ( spl2_41
  <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f317,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_19
    | ~ spl2_41 ),
    inference(subsumption_resolution,[],[f314,f70])).

fof(f314,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_19
    | ~ spl2_41 ),
    inference(resolution,[],[f304,f149])).

fof(f304,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f303])).

fof(f391,plain,
    ( spl2_50
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_32
    | ~ spl2_39 ),
    inference(avatar_split_clause,[],[f288,f272,f211,f117,f105,f101,f97,f389])).

fof(f97,plain,
    ( spl2_9
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f105,plain,
    ( spl2_11
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f117,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f211,plain,
    ( spl2_32
  <=> ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f272,plain,
    ( spl2_39
  <=> ! [X1] : k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f288,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1)
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_32
    | ~ spl2_39 ),
    inference(subsumption_resolution,[],[f287,f102])).

fof(f287,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
        | k1_xboole_0 = k4_xboole_0(X1,X1) )
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_32
    | ~ spl2_39 ),
    inference(forward_demodulation,[],[f286,f282])).

fof(f282,plain,
    ( ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_32
    | ~ spl2_39 ),
    inference(backward_demodulation,[],[f212,f280])).

fof(f280,plain,
    ( ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0)
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_39 ),
    inference(forward_demodulation,[],[f279,f106])).

fof(f106,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f279,plain,
    ( ! [X0] : k1_xboole_0 = k3_subset_1(X0,k4_xboole_0(X0,k1_xboole_0))
    | ~ spl2_9
    | ~ spl2_14
    | ~ spl2_39 ),
    inference(subsumption_resolution,[],[f275,f98])).

fof(f98,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f275,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_subset_1(X0,k4_xboole_0(X0,k1_xboole_0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )
    | ~ spl2_14
    | ~ spl2_39 ),
    inference(superposition,[],[f273,f118])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f117])).

fof(f273,plain,
    ( ! [X1] : k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0))
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f272])).

fof(f212,plain,
    ( ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f211])).

fof(f286,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k4_xboole_0(X1,X1)
        | ~ m1_subset_1(k3_subset_1(X1,k1_xboole_0),k1_zfmisc_1(X1)) )
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_32
    | ~ spl2_39 ),
    inference(forward_demodulation,[],[f276,f282])).

fof(f276,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k4_xboole_0(X1,k3_subset_1(X1,k1_xboole_0))
        | ~ m1_subset_1(k3_subset_1(X1,k1_xboole_0),k1_zfmisc_1(X1)) )
    | ~ spl2_14
    | ~ spl2_39 ),
    inference(superposition,[],[f273,f118])).

fof(f369,plain,
    ( spl2_48
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_40
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f352,f343,f299,f97,f89,f367])).

fof(f89,plain,
    ( spl2_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f299,plain,
    ( spl2_40
  <=> ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f343,plain,
    ( spl2_45
  <=> ! [X1] :
        ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f352,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_40
    | ~ spl2_45 ),
    inference(forward_demodulation,[],[f351,f300])).

fof(f300,plain,
    ( ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f299])).

fof(f351,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_45 ),
    inference(subsumption_resolution,[],[f350,f98])).

fof(f350,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ spl2_7
    | ~ spl2_45 ),
    inference(resolution,[],[f344,f90])).

fof(f90,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f344,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) )
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f343])).

fof(f349,plain,
    ( spl2_46
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_40
    | ~ spl2_43 ),
    inference(avatar_split_clause,[],[f341,f323,f299,f97,f89,f347])).

fof(f323,plain,
    ( spl2_43
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f341,plain,
    ( v1_tops_1(u1_struct_0(sK0),sK0)
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_40
    | ~ spl2_43 ),
    inference(forward_demodulation,[],[f340,f300])).

fof(f340,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_43 ),
    inference(subsumption_resolution,[],[f339,f98])).

fof(f339,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_7
    | ~ spl2_43 ),
    inference(resolution,[],[f324,f90])).

fof(f324,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f323])).

fof(f345,plain,
    ( spl2_45
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_16
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f261,f251,f131,f69,f65,f343])).

fof(f65,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f131,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_xboole_0(X1)
        | v3_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f251,plain,
    ( spl2_37
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ v3_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f261,plain,
    ( ! [X1] :
        ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X1) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_16
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f260,f66])).

fof(f66,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f260,plain,
    ( ! [X1] :
        ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X1)
        | ~ v2_pre_topc(sK0) )
    | ~ spl2_2
    | ~ spl2_16
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f257,f70])).

fof(f257,plain,
    ( ! [X1] :
        ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v1_xboole_0(X1)
        | ~ v2_pre_topc(sK0) )
    | ~ spl2_16
    | ~ spl2_37 ),
    inference(duplicate_literal_removal,[],[f256])).

fof(f256,plain,
    ( ! [X1] :
        ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X1)
        | ~ v2_pre_topc(sK0) )
    | ~ spl2_16
    | ~ spl2_37 ),
    inference(resolution,[],[f252,f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_xboole_0(X1)
        | ~ v2_pre_topc(X0) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f131])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f251])).

fof(f325,plain,
    ( spl2_43
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_18
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f224,f216,f139,f69,f65,f323])).

fof(f139,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_xboole_0(X1)
        | v3_tops_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f216,plain,
    ( spl2_33
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tops_1(X0,sK0)
        | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ v1_xboole_0(X0) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_18
    | ~ spl2_33 ),
    inference(subsumption_resolution,[],[f223,f66])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ v1_xboole_0(X0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl2_2
    | ~ spl2_18
    | ~ spl2_33 ),
    inference(subsumption_resolution,[],[f221,f70])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_xboole_0(X0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl2_18
    | ~ spl2_33 ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl2_18
    | ~ spl2_33 ),
    inference(resolution,[],[f217,f140])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( v3_tops_1(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_xboole_0(X1)
        | ~ v2_pre_topc(X0) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f139])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ v3_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) )
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f216])).

fof(f312,plain,
    ( spl2_42
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f125,f117,f109,f310])).

fof(f109,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(superposition,[],[f110,f118])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f305,plain,
    ( spl2_41
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f297,f268,f117,f85,f303])).

fof(f268,plain,
    ( spl2_38
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f297,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_38 ),
    inference(subsumption_resolution,[],[f293,f86])).

fof(f293,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_14
    | ~ spl2_38 ),
    inference(superposition,[],[f269,f118])).

fof(f269,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f268])).

fof(f301,plain,
    ( spl2_40
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_32
    | ~ spl2_39 ),
    inference(avatar_split_clause,[],[f282,f272,f211,f117,f105,f97,f299])).

fof(f274,plain,
    ( spl2_39
    | ~ spl2_9
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f127,f121,f97,f272])).

fof(f121,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f127,plain,
    ( ! [X1] : k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0))
    | ~ spl2_9
    | ~ spl2_15 ),
    inference(resolution,[],[f122,f98])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f121])).

fof(f270,plain,
    ( spl2_38
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f259,f251,f85,f73,f268])).

fof(f73,plain,
    ( spl2_3
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f259,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f254,f86])).

fof(f254,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_37 ),
    inference(resolution,[],[f252,f74])).

fof(f74,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f253,plain,
    ( spl2_37
    | ~ spl2_2
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f234,f203,f69,f251])).

fof(f203,plain,
    ( spl2_30
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
        | ~ v3_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl2_2
    | ~ spl2_30 ),
    inference(resolution,[],[f204,f70])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
        | ~ v3_pre_topc(X1,X0) )
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f203])).

fof(f238,plain,
    ( spl2_35
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f233,f227,f117,f85,f236])).

fof(f227,plain,
    ( spl2_34
  <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f233,plain,
    ( v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f231,f86])).

fof(f231,plain,
    ( v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_14
    | ~ spl2_34 ),
    inference(superposition,[],[f228,f118])).

fof(f228,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f227])).

fof(f229,plain,
    ( spl2_34
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f222,f216,f85,f77,f227])).

fof(f77,plain,
    ( spl2_4
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f222,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_33 ),
    inference(subsumption_resolution,[],[f219,f86])).

fof(f219,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_4
    | ~ spl2_33 ),
    inference(resolution,[],[f217,f78])).

fof(f78,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f218,plain,
    ( spl2_33
    | ~ spl2_2
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f214,f159,f69,f216])).

fof(f159,plain,
    ( spl2_21
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_tops_1(X1,X0)
        | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tops_1(X0,sK0)
        | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) )
    | ~ spl2_2
    | ~ spl2_21 ),
    inference(resolution,[],[f160,f70])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_tops_1(X1,X0)
        | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f159])).

fof(f213,plain,
    ( spl2_32
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f126,f121,f101,f211])).

fof(f126,plain,
    ( ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(resolution,[],[f122,f102])).

fof(f205,plain,(
    spl2_30 ),
    inference(avatar_split_clause,[],[f56,f203])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(f201,plain,
    ( spl2_29
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f193,f170,f117,f85,f199])).

fof(f170,plain,
    ( spl2_24
  <=> sK1 = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f193,plain,
    ( sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_6
    | ~ spl2_14
    | ~ spl2_24 ),
    inference(subsumption_resolution,[],[f192,f86])).

fof(f192,plain,
    ( sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_14
    | ~ spl2_24 ),
    inference(superposition,[],[f171,f118])).

fof(f171,plain,
    ( sK1 = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f170])).

fof(f182,plain,
    ( ~ spl2_6
    | ~ spl2_12
    | spl2_23 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl2_6
    | ~ spl2_12
    | spl2_23 ),
    inference(subsumption_resolution,[],[f178,f86])).

fof(f178,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_12
    | spl2_23 ),
    inference(resolution,[],[f168,f110])).

fof(f168,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_23 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl2_23
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f176,plain,(
    spl2_25 ),
    inference(avatar_split_clause,[],[f52,f174])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f172,plain,
    ( ~ spl2_23
    | spl2_24
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f143,f135,f117,f170,f167])).

fof(f135,plain,
    ( spl2_17
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f143,plain,
    ( sK1 = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(superposition,[],[f136,f118])).

fof(f136,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f135])).

fof(f161,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f50,f159])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

fof(f150,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f49,f148])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f141,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f58,f139])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v3_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_tops_1)).

fof(f137,plain,
    ( spl2_17
    | ~ spl2_6
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f129,f121,f85,f135])).

fof(f129,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_6
    | ~ spl2_15 ),
    inference(resolution,[],[f122,f86])).

fof(f133,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f57,f131])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

fof(f123,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f61,f121])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f119,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f60,f117])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f111,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f59,f109])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f107,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f46,f105])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f103,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f63,f101])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f47,f44])).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f99,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f45,f97])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f91,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f43,f89])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f87,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f37,f85])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

fof(f83,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f40,f81])).

fof(f40,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f79,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f39,f77])).

fof(f39,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f38,f73])).

fof(f38,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f42,f69])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f41,f65])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:38:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.46  % (29067)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (29063)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (29063)Refutation not found, incomplete strategy% (29063)------------------------------
% 0.20/0.48  % (29063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (29063)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (29063)Memory used [KB]: 10618
% 0.20/0.48  % (29063)Time elapsed: 0.047 s
% 0.20/0.48  % (29063)------------------------------
% 0.20/0.48  % (29063)------------------------------
% 0.20/0.48  % (29073)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (29073)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f534,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f67,f71,f75,f79,f83,f87,f91,f99,f103,f107,f111,f119,f123,f133,f137,f141,f150,f161,f172,f176,f182,f201,f205,f213,f218,f229,f238,f253,f270,f274,f301,f305,f312,f325,f345,f349,f369,f391,f479,f492,f521,f533])).
% 0.20/0.49  fof(f533,plain,(
% 0.20/0.49    spl2_5 | ~spl2_29 | ~spl2_50 | ~spl2_63),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f532])).
% 0.20/0.49  fof(f532,plain,(
% 0.20/0.49    $false | (spl2_5 | ~spl2_29 | ~spl2_50 | ~spl2_63)),
% 0.20/0.49    inference(subsumption_resolution,[],[f531,f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    k1_xboole_0 != sK1 | spl2_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    spl2_5 <=> k1_xboole_0 = sK1),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.49  fof(f531,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | (~spl2_29 | ~spl2_50 | ~spl2_63)),
% 0.20/0.49    inference(forward_demodulation,[],[f523,f390])).
% 0.20/0.49  fof(f390,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) ) | ~spl2_50),
% 0.20/0.49    inference(avatar_component_clause,[],[f389])).
% 0.20/0.49  fof(f389,plain,(
% 0.20/0.49    spl2_50 <=> ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 0.20/0.49  fof(f523,plain,(
% 0.20/0.49    sK1 = k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) | (~spl2_29 | ~spl2_63)),
% 0.20/0.49    inference(backward_demodulation,[],[f200,f520])).
% 0.20/0.49  fof(f520,plain,(
% 0.20/0.49    u1_struct_0(sK0) = k4_xboole_0(u1_struct_0(sK0),sK1) | ~spl2_63),
% 0.20/0.49    inference(avatar_component_clause,[],[f519])).
% 0.20/0.49  fof(f519,plain,(
% 0.20/0.49    spl2_63 <=> u1_struct_0(sK0) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).
% 0.20/0.49  fof(f200,plain,(
% 0.20/0.49    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl2_29),
% 0.20/0.49    inference(avatar_component_clause,[],[f199])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    spl2_29 <=> sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.20/0.49  fof(f521,plain,(
% 0.20/0.49    ~spl2_59 | spl2_63 | ~spl2_2 | ~spl2_10 | ~spl2_19 | ~spl2_25 | ~spl2_35 | ~spl2_46 | ~spl2_48 | ~spl2_58),
% 0.20/0.49    inference(avatar_split_clause,[],[f493,f474,f367,f347,f236,f174,f148,f101,f69,f519,f477])).
% 0.20/0.49  fof(f477,plain,(
% 0.20/0.49    spl2_59 <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    spl2_2 <=> l1_pre_topc(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    spl2_10 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    spl2_19 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    spl2_25 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.20/0.49  fof(f236,plain,(
% 0.20/0.49    spl2_35 <=> v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.20/0.49  fof(f347,plain,(
% 0.20/0.49    spl2_46 <=> v1_tops_1(u1_struct_0(sK0),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.20/0.49  fof(f367,plain,(
% 0.20/0.49    spl2_48 <=> v4_pre_topc(u1_struct_0(sK0),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 0.20/0.49  fof(f474,plain,(
% 0.20/0.49    spl2_58 <=> k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 0.20/0.49  fof(f493,plain,(
% 0.20/0.49    u1_struct_0(sK0) = k4_xboole_0(u1_struct_0(sK0),sK1) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_10 | ~spl2_19 | ~spl2_25 | ~spl2_35 | ~spl2_46 | ~spl2_48 | ~spl2_58)),
% 0.20/0.49    inference(backward_demodulation,[],[f386,f475])).
% 0.20/0.49  fof(f475,plain,(
% 0.20/0.49    k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl2_58),
% 0.20/0.49    inference(avatar_component_clause,[],[f474])).
% 0.20/0.49  fof(f386,plain,(
% 0.20/0.49    u1_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_10 | ~spl2_19 | ~spl2_25 | ~spl2_35 | ~spl2_46 | ~spl2_48)),
% 0.20/0.49    inference(backward_demodulation,[],[f244,f384])).
% 0.20/0.49  fof(f384,plain,(
% 0.20/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl2_2 | ~spl2_10 | ~spl2_19 | ~spl2_25 | ~spl2_46 | ~spl2_48)),
% 0.20/0.49    inference(backward_demodulation,[],[f359,f383])).
% 0.20/0.49  fof(f383,plain,(
% 0.20/0.49    u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | (~spl2_2 | ~spl2_10 | ~spl2_19 | ~spl2_48)),
% 0.20/0.49    inference(subsumption_resolution,[],[f382,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    l1_pre_topc(sK0) | ~spl2_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f69])).
% 0.20/0.49  fof(f382,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | (~spl2_10 | ~spl2_19 | ~spl2_48)),
% 0.20/0.49    inference(subsumption_resolution,[],[f378,f102])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl2_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f101])).
% 0.20/0.49  fof(f378,plain,(
% 0.20/0.49    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | (~spl2_19 | ~spl2_48)),
% 0.20/0.49    inference(resolution,[],[f368,f149])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = X1) ) | ~spl2_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f148])).
% 0.20/0.49  fof(f368,plain,(
% 0.20/0.49    v4_pre_topc(u1_struct_0(sK0),sK0) | ~spl2_48),
% 0.20/0.49    inference(avatar_component_clause,[],[f367])).
% 0.20/0.49  fof(f359,plain,(
% 0.20/0.49    k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | (~spl2_2 | ~spl2_10 | ~spl2_25 | ~spl2_46)),
% 0.20/0.49    inference(subsumption_resolution,[],[f358,f70])).
% 0.20/0.49  fof(f358,plain,(
% 0.20/0.49    k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | (~spl2_10 | ~spl2_25 | ~spl2_46)),
% 0.20/0.49    inference(subsumption_resolution,[],[f357,f102])).
% 0.20/0.49  fof(f357,plain,(
% 0.20/0.49    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | (~spl2_25 | ~spl2_46)),
% 0.20/0.49    inference(resolution,[],[f348,f175])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl2_25),
% 0.20/0.49    inference(avatar_component_clause,[],[f174])).
% 0.20/0.49  fof(f348,plain,(
% 0.20/0.49    v1_tops_1(u1_struct_0(sK0),sK0) | ~spl2_46),
% 0.20/0.49    inference(avatar_component_clause,[],[f347])).
% 0.20/0.49  fof(f244,plain,(
% 0.20/0.49    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_25 | ~spl2_35)),
% 0.20/0.49    inference(subsumption_resolution,[],[f243,f70])).
% 0.20/0.49  fof(f243,plain,(
% 0.20/0.49    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | (~spl2_25 | ~spl2_35)),
% 0.20/0.49    inference(resolution,[],[f237,f175])).
% 0.20/0.49  fof(f237,plain,(
% 0.20/0.49    v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~spl2_35),
% 0.20/0.49    inference(avatar_component_clause,[],[f236])).
% 0.20/0.49  fof(f492,plain,(
% 0.20/0.49    ~spl2_6 | ~spl2_42 | spl2_59),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f491])).
% 0.20/0.49  fof(f491,plain,(
% 0.20/0.49    $false | (~spl2_6 | ~spl2_42 | spl2_59)),
% 0.20/0.49    inference(subsumption_resolution,[],[f489,f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    spl2_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.49  fof(f489,plain,(
% 0.20/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_42 | spl2_59)),
% 0.20/0.49    inference(resolution,[],[f478,f311])).
% 0.20/0.49  fof(f311,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_42),
% 0.20/0.49    inference(avatar_component_clause,[],[f310])).
% 0.20/0.49  fof(f310,plain,(
% 0.20/0.49    spl2_42 <=> ! [X1,X0] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.20/0.49  fof(f478,plain,(
% 0.20/0.49    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_59),
% 0.20/0.49    inference(avatar_component_clause,[],[f477])).
% 0.20/0.49  fof(f479,plain,(
% 0.20/0.49    spl2_58 | ~spl2_59 | ~spl2_2 | ~spl2_19 | ~spl2_41),
% 0.20/0.49    inference(avatar_split_clause,[],[f317,f303,f148,f69,f477,f474])).
% 0.20/0.49  fof(f303,plain,(
% 0.20/0.49    spl2_41 <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 0.20/0.49  fof(f317,plain,(
% 0.20/0.49    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_19 | ~spl2_41)),
% 0.20/0.49    inference(subsumption_resolution,[],[f314,f70])).
% 0.20/0.49  fof(f314,plain,(
% 0.20/0.49    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl2_19 | ~spl2_41)),
% 0.20/0.49    inference(resolution,[],[f304,f149])).
% 0.20/0.49  fof(f304,plain,(
% 0.20/0.49    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~spl2_41),
% 0.20/0.49    inference(avatar_component_clause,[],[f303])).
% 0.20/0.49  fof(f391,plain,(
% 0.20/0.49    spl2_50 | ~spl2_9 | ~spl2_10 | ~spl2_11 | ~spl2_14 | ~spl2_32 | ~spl2_39),
% 0.20/0.49    inference(avatar_split_clause,[],[f288,f272,f211,f117,f105,f101,f97,f389])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    spl2_9 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    spl2_11 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    spl2_14 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.49  fof(f211,plain,(
% 0.20/0.49    spl2_32 <=> ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.20/0.49  fof(f272,plain,(
% 0.20/0.49    spl2_39 <=> ! [X1] : k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.20/0.49  fof(f288,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) ) | (~spl2_9 | ~spl2_10 | ~spl2_11 | ~spl2_14 | ~spl2_32 | ~spl2_39)),
% 0.20/0.49    inference(subsumption_resolution,[],[f287,f102])).
% 0.20/0.49  fof(f287,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | k1_xboole_0 = k4_xboole_0(X1,X1)) ) | (~spl2_9 | ~spl2_11 | ~spl2_14 | ~spl2_32 | ~spl2_39)),
% 0.20/0.49    inference(forward_demodulation,[],[f286,f282])).
% 0.20/0.49  fof(f282,plain,(
% 0.20/0.49    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) ) | (~spl2_9 | ~spl2_11 | ~spl2_14 | ~spl2_32 | ~spl2_39)),
% 0.20/0.49    inference(backward_demodulation,[],[f212,f280])).
% 0.20/0.49  fof(f280,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) ) | (~spl2_9 | ~spl2_11 | ~spl2_14 | ~spl2_39)),
% 0.20/0.49    inference(forward_demodulation,[],[f279,f106])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f105])).
% 0.20/0.49  fof(f279,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k4_xboole_0(X0,k1_xboole_0))) ) | (~spl2_9 | ~spl2_14 | ~spl2_39)),
% 0.20/0.49    inference(subsumption_resolution,[],[f275,f98])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl2_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f97])).
% 0.20/0.49  fof(f275,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k4_xboole_0(X0,k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | (~spl2_14 | ~spl2_39)),
% 0.20/0.49    inference(superposition,[],[f273,f118])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f117])).
% 0.20/0.49  fof(f273,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0))) ) | ~spl2_39),
% 0.20/0.49    inference(avatar_component_clause,[],[f272])).
% 0.20/0.49  fof(f212,plain,(
% 0.20/0.49    ( ! [X0] : (k3_subset_1(X0,k3_subset_1(X0,X0)) = X0) ) | ~spl2_32),
% 0.20/0.49    inference(avatar_component_clause,[],[f211])).
% 0.20/0.49  fof(f286,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1) | ~m1_subset_1(k3_subset_1(X1,k1_xboole_0),k1_zfmisc_1(X1))) ) | (~spl2_9 | ~spl2_11 | ~spl2_14 | ~spl2_32 | ~spl2_39)),
% 0.20/0.49    inference(forward_demodulation,[],[f276,f282])).
% 0.20/0.49  fof(f276,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k3_subset_1(X1,k1_xboole_0)) | ~m1_subset_1(k3_subset_1(X1,k1_xboole_0),k1_zfmisc_1(X1))) ) | (~spl2_14 | ~spl2_39)),
% 0.20/0.49    inference(superposition,[],[f273,f118])).
% 0.20/0.49  fof(f369,plain,(
% 0.20/0.49    spl2_48 | ~spl2_7 | ~spl2_9 | ~spl2_40 | ~spl2_45),
% 0.20/0.49    inference(avatar_split_clause,[],[f352,f343,f299,f97,f89,f367])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    spl2_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.49  fof(f299,plain,(
% 0.20/0.49    spl2_40 <=> ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.20/0.49  fof(f343,plain,(
% 0.20/0.49    spl2_45 <=> ! [X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.20/0.49  fof(f352,plain,(
% 0.20/0.49    v4_pre_topc(u1_struct_0(sK0),sK0) | (~spl2_7 | ~spl2_9 | ~spl2_40 | ~spl2_45)),
% 0.20/0.49    inference(forward_demodulation,[],[f351,f300])).
% 0.20/0.49  fof(f300,plain,(
% 0.20/0.49    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) ) | ~spl2_40),
% 0.20/0.49    inference(avatar_component_clause,[],[f299])).
% 0.20/0.49  fof(f351,plain,(
% 0.20/0.49    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) | (~spl2_7 | ~spl2_9 | ~spl2_45)),
% 0.20/0.49    inference(subsumption_resolution,[],[f350,f98])).
% 0.20/0.49  fof(f350,plain,(
% 0.20/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) | (~spl2_7 | ~spl2_45)),
% 0.20/0.49    inference(resolution,[],[f344,f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0) | ~spl2_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f89])).
% 0.20/0.49  fof(f344,plain,(
% 0.20/0.49    ( ! [X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)) ) | ~spl2_45),
% 0.20/0.49    inference(avatar_component_clause,[],[f343])).
% 0.20/0.49  fof(f349,plain,(
% 0.20/0.49    spl2_46 | ~spl2_7 | ~spl2_9 | ~spl2_40 | ~spl2_43),
% 0.20/0.49    inference(avatar_split_clause,[],[f341,f323,f299,f97,f89,f347])).
% 0.20/0.49  fof(f323,plain,(
% 0.20/0.49    spl2_43 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~v1_xboole_0(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.20/0.49  fof(f341,plain,(
% 0.20/0.49    v1_tops_1(u1_struct_0(sK0),sK0) | (~spl2_7 | ~spl2_9 | ~spl2_40 | ~spl2_43)),
% 0.20/0.49    inference(forward_demodulation,[],[f340,f300])).
% 0.20/0.49  fof(f340,plain,(
% 0.20/0.49    v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) | (~spl2_7 | ~spl2_9 | ~spl2_43)),
% 0.20/0.49    inference(subsumption_resolution,[],[f339,f98])).
% 0.20/0.49  fof(f339,plain,(
% 0.20/0.49    v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_7 | ~spl2_43)),
% 0.20/0.49    inference(resolution,[],[f324,f90])).
% 0.20/0.49  fof(f324,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(X0) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_43),
% 0.20/0.49    inference(avatar_component_clause,[],[f323])).
% 0.20/0.49  fof(f345,plain,(
% 0.20/0.49    spl2_45 | ~spl2_1 | ~spl2_2 | ~spl2_16 | ~spl2_37),
% 0.20/0.49    inference(avatar_split_clause,[],[f261,f251,f131,f69,f65,f343])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    spl2_1 <=> v2_pre_topc(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    spl2_16 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v3_pre_topc(X1,X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.49  fof(f251,plain,(
% 0.20/0.49    spl2_37 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~v3_pre_topc(X0,sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.20/0.49  fof(f261,plain,(
% 0.20/0.49    ( ! [X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X1)) ) | (~spl2_1 | ~spl2_2 | ~spl2_16 | ~spl2_37)),
% 0.20/0.49    inference(subsumption_resolution,[],[f260,f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    v2_pre_topc(sK0) | ~spl2_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f65])).
% 0.20/0.49  fof(f260,plain,(
% 0.20/0.49    ( ! [X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X1) | ~v2_pre_topc(sK0)) ) | (~spl2_2 | ~spl2_16 | ~spl2_37)),
% 0.20/0.49    inference(subsumption_resolution,[],[f257,f70])).
% 0.20/0.49  fof(f257,plain,(
% 0.20/0.49    ( ! [X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v1_xboole_0(X1) | ~v2_pre_topc(sK0)) ) | (~spl2_16 | ~spl2_37)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f256])).
% 0.20/0.49  fof(f256,plain,(
% 0.20/0.49    ( ! [X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X1) | ~v2_pre_topc(sK0)) ) | (~spl2_16 | ~spl2_37)),
% 0.20/0.49    inference(resolution,[],[f252,f132])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~v2_pre_topc(X0)) ) | ~spl2_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f131])).
% 0.20/0.49  fof(f252,plain,(
% 0.20/0.49    ( ! [X0] : (~v3_pre_topc(X0,sK0) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_37),
% 0.20/0.49    inference(avatar_component_clause,[],[f251])).
% 0.20/0.49  fof(f325,plain,(
% 0.20/0.49    spl2_43 | ~spl2_1 | ~spl2_2 | ~spl2_18 | ~spl2_33),
% 0.20/0.49    inference(avatar_split_clause,[],[f224,f216,f139,f69,f65,f323])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    spl2_18 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v3_tops_1(X1,X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.49  fof(f216,plain,(
% 0.20/0.49    spl2_33 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tops_1(X0,sK0) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~v1_xboole_0(X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_18 | ~spl2_33)),
% 0.20/0.49    inference(subsumption_resolution,[],[f223,f66])).
% 0.20/0.49  fof(f223,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~v1_xboole_0(X0) | ~v2_pre_topc(sK0)) ) | (~spl2_2 | ~spl2_18 | ~spl2_33)),
% 0.20/0.49    inference(subsumption_resolution,[],[f221,f70])).
% 0.20/0.49  fof(f221,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~l1_pre_topc(sK0) | ~v1_xboole_0(X0) | ~v2_pre_topc(sK0)) ) | (~spl2_18 | ~spl2_33)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f220])).
% 0.20/0.49  fof(f220,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X0) | ~v2_pre_topc(sK0)) ) | (~spl2_18 | ~spl2_33)),
% 0.20/0.49    inference(resolution,[],[f217,f140])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v3_tops_1(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~v2_pre_topc(X0)) ) | ~spl2_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f139])).
% 0.20/0.49  fof(f217,plain,(
% 0.20/0.49    ( ! [X0] : (~v3_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)) ) | ~spl2_33),
% 0.20/0.49    inference(avatar_component_clause,[],[f216])).
% 0.20/0.49  fof(f312,plain,(
% 0.20/0.49    spl2_42 | ~spl2_12 | ~spl2_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f125,f117,f109,f310])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    spl2_12 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl2_12 | ~spl2_14)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f124])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl2_12 | ~spl2_14)),
% 0.20/0.49    inference(superposition,[],[f110,f118])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f109])).
% 0.20/0.49  fof(f305,plain,(
% 0.20/0.49    spl2_41 | ~spl2_6 | ~spl2_14 | ~spl2_38),
% 0.20/0.49    inference(avatar_split_clause,[],[f297,f268,f117,f85,f303])).
% 0.20/0.49  fof(f268,plain,(
% 0.20/0.49    spl2_38 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.20/0.49  fof(f297,plain,(
% 0.20/0.49    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | (~spl2_6 | ~spl2_14 | ~spl2_38)),
% 0.20/0.49    inference(subsumption_resolution,[],[f293,f86])).
% 0.20/0.49  fof(f293,plain,(
% 0.20/0.49    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_14 | ~spl2_38)),
% 0.20/0.49    inference(superposition,[],[f269,f118])).
% 0.20/0.49  fof(f269,plain,(
% 0.20/0.49    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_38),
% 0.20/0.49    inference(avatar_component_clause,[],[f268])).
% 0.20/0.49  fof(f301,plain,(
% 0.20/0.49    spl2_40 | ~spl2_9 | ~spl2_11 | ~spl2_14 | ~spl2_32 | ~spl2_39),
% 0.20/0.49    inference(avatar_split_clause,[],[f282,f272,f211,f117,f105,f97,f299])).
% 0.20/0.49  fof(f274,plain,(
% 0.20/0.49    spl2_39 | ~spl2_9 | ~spl2_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f127,f121,f97,f272])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    spl2_15 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0))) ) | (~spl2_9 | ~spl2_15)),
% 0.20/0.49    inference(resolution,[],[f122,f98])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) ) | ~spl2_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f121])).
% 0.20/0.49  fof(f270,plain,(
% 0.20/0.49    spl2_38 | ~spl2_3 | ~spl2_6 | ~spl2_37),
% 0.20/0.49    inference(avatar_split_clause,[],[f259,f251,f85,f73,f268])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    spl2_3 <=> v3_pre_topc(sK1,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.49  fof(f259,plain,(
% 0.20/0.49    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl2_3 | ~spl2_6 | ~spl2_37)),
% 0.20/0.49    inference(subsumption_resolution,[],[f254,f86])).
% 0.20/0.49  fof(f254,plain,(
% 0.20/0.49    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_37)),
% 0.20/0.49    inference(resolution,[],[f252,f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    v3_pre_topc(sK1,sK0) | ~spl2_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f73])).
% 0.20/0.49  fof(f253,plain,(
% 0.20/0.49    spl2_37 | ~spl2_2 | ~spl2_30),
% 0.20/0.49    inference(avatar_split_clause,[],[f234,f203,f69,f251])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    spl2_30 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.20/0.49  fof(f234,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~v3_pre_topc(X0,sK0)) ) | (~spl2_2 | ~spl2_30)),
% 0.20/0.49    inference(resolution,[],[f204,f70])).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0)) ) | ~spl2_30),
% 0.20/0.49    inference(avatar_component_clause,[],[f203])).
% 0.20/0.49  fof(f238,plain,(
% 0.20/0.49    spl2_35 | ~spl2_6 | ~spl2_14 | ~spl2_34),
% 0.20/0.49    inference(avatar_split_clause,[],[f233,f227,f117,f85,f236])).
% 0.20/0.49  fof(f227,plain,(
% 0.20/0.49    spl2_34 <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.20/0.49  fof(f233,plain,(
% 0.20/0.49    v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | (~spl2_6 | ~spl2_14 | ~spl2_34)),
% 0.20/0.49    inference(subsumption_resolution,[],[f231,f86])).
% 0.20/0.49  fof(f231,plain,(
% 0.20/0.49    v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_14 | ~spl2_34)),
% 0.20/0.49    inference(superposition,[],[f228,f118])).
% 0.20/0.49  fof(f228,plain,(
% 0.20/0.49    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_34),
% 0.20/0.49    inference(avatar_component_clause,[],[f227])).
% 0.20/0.49  fof(f229,plain,(
% 0.20/0.49    spl2_34 | ~spl2_4 | ~spl2_6 | ~spl2_33),
% 0.20/0.49    inference(avatar_split_clause,[],[f222,f216,f85,f77,f227])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    spl2_4 <=> v3_tops_1(sK1,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.49  fof(f222,plain,(
% 0.20/0.49    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl2_4 | ~spl2_6 | ~spl2_33)),
% 0.20/0.49    inference(subsumption_resolution,[],[f219,f86])).
% 0.20/0.49  fof(f219,plain,(
% 0.20/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl2_4 | ~spl2_33)),
% 0.20/0.49    inference(resolution,[],[f217,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    v3_tops_1(sK1,sK0) | ~spl2_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f77])).
% 0.20/0.49  fof(f218,plain,(
% 0.20/0.49    spl2_33 | ~spl2_2 | ~spl2_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f214,f159,f69,f216])).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    spl2_21 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.20/0.49  fof(f214,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tops_1(X0,sK0) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)) ) | (~spl2_2 | ~spl2_21)),
% 0.20/0.49    inference(resolution,[],[f160,f70])).
% 0.20/0.49  fof(f160,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) ) | ~spl2_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f159])).
% 0.20/0.49  fof(f213,plain,(
% 0.20/0.49    spl2_32 | ~spl2_10 | ~spl2_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f126,f121,f101,f211])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    ( ! [X0] : (k3_subset_1(X0,k3_subset_1(X0,X0)) = X0) ) | (~spl2_10 | ~spl2_15)),
% 0.20/0.50    inference(resolution,[],[f122,f102])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    spl2_30),
% 0.20/0.50    inference(avatar_split_clause,[],[f56,f203])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    spl2_29 | ~spl2_6 | ~spl2_14 | ~spl2_24),
% 0.20/0.50    inference(avatar_split_clause,[],[f193,f170,f117,f85,f199])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    spl2_24 <=> sK1 = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.20/0.50  fof(f193,plain,(
% 0.20/0.50    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl2_6 | ~spl2_14 | ~spl2_24)),
% 0.20/0.50    inference(subsumption_resolution,[],[f192,f86])).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_14 | ~spl2_24)),
% 0.20/0.50    inference(superposition,[],[f171,f118])).
% 0.20/0.50  fof(f171,plain,(
% 0.20/0.50    sK1 = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_24),
% 0.20/0.50    inference(avatar_component_clause,[],[f170])).
% 0.20/0.50  fof(f182,plain,(
% 0.20/0.50    ~spl2_6 | ~spl2_12 | spl2_23),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f181])).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    $false | (~spl2_6 | ~spl2_12 | spl2_23)),
% 0.20/0.50    inference(subsumption_resolution,[],[f178,f86])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_12 | spl2_23)),
% 0.20/0.50    inference(resolution,[],[f168,f110])).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_23),
% 0.20/0.50    inference(avatar_component_clause,[],[f167])).
% 0.20/0.50  fof(f167,plain,(
% 0.20/0.50    spl2_23 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.20/0.50  fof(f176,plain,(
% 0.20/0.50    spl2_25),
% 0.20/0.50    inference(avatar_split_clause,[],[f52,f174])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    ~spl2_23 | spl2_24 | ~spl2_14 | ~spl2_17),
% 0.20/0.50    inference(avatar_split_clause,[],[f143,f135,f117,f170,f167])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    spl2_17 <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    sK1 = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_14 | ~spl2_17)),
% 0.20/0.50    inference(superposition,[],[f136,f118])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f135])).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    spl2_21),
% 0.20/0.50    inference(avatar_split_clause,[],[f50,f159])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    spl2_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f49,f148])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    spl2_18),
% 0.20/0.50    inference(avatar_split_clause,[],[f58,f139])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v3_tops_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_tops_1(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_tops_1)).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    spl2_17 | ~spl2_6 | ~spl2_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f129,f121,f85,f135])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_6 | ~spl2_15)),
% 0.20/0.50    inference(resolution,[],[f122,f86])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    spl2_16),
% 0.20/0.50    inference(avatar_split_clause,[],[f57,f131])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v3_pre_topc(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    spl2_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f61,f121])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    spl2_14),
% 0.20/0.50    inference(avatar_split_clause,[],[f60,f117])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    spl2_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f59,f109])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    spl2_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f46,f105])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    spl2_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f63,f101])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f47,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    spl2_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f45,f97])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    spl2_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f43,f89])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    spl2_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f37,f85])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.20/0.50    inference(negated_conjecture,[],[f17])).
% 0.20/0.50  fof(f17,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ~spl2_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f40,f81])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    k1_xboole_0 != sK1),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    spl2_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f39,f77])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    v3_tops_1(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    spl2_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f38,f73])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    v3_pre_topc(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    spl2_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f42,f69])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    spl2_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f41,f65])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    v2_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (29073)------------------------------
% 0.20/0.50  % (29073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29073)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (29073)Memory used [KB]: 10874
% 0.20/0.50  % (29073)Time elapsed: 0.077 s
% 0.20/0.50  % (29073)------------------------------
% 0.20/0.50  % (29073)------------------------------
% 0.20/0.50  % (29055)Success in time 0.138 s
%------------------------------------------------------------------------------
