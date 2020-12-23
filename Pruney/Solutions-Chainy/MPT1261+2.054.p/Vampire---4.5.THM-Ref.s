%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:56 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  261 ( 474 expanded)
%              Number of leaves         :   69 ( 225 expanded)
%              Depth                    :   10
%              Number of atoms          :  777 (1462 expanded)
%              Number of equality atoms :  170 ( 344 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3735,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f99,f108,f110,f114,f118,f122,f126,f130,f138,f146,f150,f160,f169,f173,f205,f209,f215,f237,f245,f251,f271,f276,f280,f317,f341,f360,f399,f415,f419,f466,f536,f652,f680,f685,f1069,f1099,f1104,f1246,f1393,f1400,f2005,f2400,f3400,f3455,f3704,f3732,f3734])).

fof(f3734,plain,
    ( ~ spl2_85
    | spl2_99
    | ~ spl2_179 ),
    inference(avatar_contradiction_clause,[],[f3733])).

fof(f3733,plain,
    ( $false
    | ~ spl2_85
    | spl2_99
    | ~ spl2_179 ),
    inference(subsumption_resolution,[],[f3470,f1250])).

fof(f1250,plain,
    ( sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | spl2_99 ),
    inference(avatar_component_clause,[],[f1249])).

fof(f1249,plain,
    ( spl2_99
  <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_99])])).

fof(f3470,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_85
    | ~ spl2_179 ),
    inference(unit_resulting_resolution,[],[f1068,f3454])).

fof(f3454,plain,
    ( ! [X4,X3] :
        ( k2_xboole_0(X4,X3) = X4
        | ~ r1_tarski(X3,X4) )
    | ~ spl2_179 ),
    inference(avatar_component_clause,[],[f3453])).

fof(f3453,plain,
    ( spl2_179
  <=> ! [X3,X4] :
        ( k2_xboole_0(X4,X3) = X4
        | ~ r1_tarski(X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_179])])).

fof(f1068,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_85 ),
    inference(avatar_component_clause,[],[f1066])).

fof(f1066,plain,
    ( spl2_85
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_85])])).

fof(f3732,plain,
    ( ~ spl2_14
    | spl2_37
    | ~ spl2_55
    | ~ spl2_98
    | ~ spl2_107
    | ~ spl2_108 ),
    inference(avatar_contradiction_clause,[],[f3731])).

fof(f3731,plain,
    ( $false
    | ~ spl2_14
    | spl2_37
    | ~ spl2_55
    | ~ spl2_98
    | ~ spl2_107
    | ~ spl2_108 ),
    inference(subsumption_resolution,[],[f340,f3730])).

fof(f3730,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_14
    | ~ spl2_55
    | ~ spl2_98
    | ~ spl2_107
    | ~ spl2_108 ),
    inference(forward_demodulation,[],[f3729,f1399])).

fof(f1399,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_108 ),
    inference(avatar_component_clause,[],[f1397])).

fof(f1397,plain,
    ( spl2_108
  <=> sK1 = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_108])])).

fof(f3729,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_14
    | ~ spl2_55
    | ~ spl2_98
    | ~ spl2_107 ),
    inference(forward_demodulation,[],[f1394,f1245])).

fof(f1245,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_98 ),
    inference(avatar_component_clause,[],[f1243])).

fof(f1243,plain,
    ( spl2_98
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).

fof(f1394,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_14
    | ~ spl2_55
    | ~ spl2_107 ),
    inference(forward_demodulation,[],[f1392,f539])).

fof(f539,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)
    | ~ spl2_14
    | ~ spl2_55 ),
    inference(superposition,[],[f535,f145])).

fof(f145,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl2_14
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f535,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f534])).

fof(f534,plain,
    ( spl2_55
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f1392,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_107 ),
    inference(avatar_component_clause,[],[f1390])).

fof(f1390,plain,
    ( spl2_107
  <=> k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_107])])).

fof(f340,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_37 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl2_37
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f3704,plain,
    ( ~ spl2_3
    | spl2_5
    | ~ spl2_18
    | ~ spl2_24
    | ~ spl2_66
    | ~ spl2_86
    | ~ spl2_159 ),
    inference(avatar_contradiction_clause,[],[f3703])).

fof(f3703,plain,
    ( $false
    | ~ spl2_3
    | spl2_5
    | ~ spl2_18
    | ~ spl2_24
    | ~ spl2_66
    | ~ spl2_86
    | ~ spl2_159 ),
    inference(subsumption_resolution,[],[f98,f3702])).

fof(f3702,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_5
    | ~ spl2_18
    | ~ spl2_24
    | ~ spl2_66
    | ~ spl2_86
    | ~ spl2_159 ),
    inference(trivial_inequality_removal,[],[f3701])).

fof(f3701,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_5
    | ~ spl2_18
    | ~ spl2_24
    | ~ spl2_66
    | ~ spl2_86
    | ~ spl2_159 ),
    inference(forward_demodulation,[],[f3700,f2685])).

fof(f2685,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_66
    | ~ spl2_159 ),
    inference(unit_resulting_resolution,[],[f2399,f684])).

fof(f684,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_66 ),
    inference(avatar_component_clause,[],[f683])).

fof(f683,plain,
    ( spl2_66
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f2399,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_159 ),
    inference(avatar_component_clause,[],[f2397])).

fof(f2397,plain,
    ( spl2_159
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_159])])).

fof(f3700,plain,
    ( k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_5
    | ~ spl2_18
    | ~ spl2_24
    | ~ spl2_86 ),
    inference(forward_demodulation,[],[f1082,f1110])).

fof(f1110,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_18
    | ~ spl2_86 ),
    inference(superposition,[],[f168,f1103])).

fof(f1103,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_86 ),
    inference(avatar_component_clause,[],[f1101])).

fof(f1101,plain,
    ( spl2_86
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).

fof(f168,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl2_18
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f1082,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_5
    | ~ spl2_24 ),
    inference(superposition,[],[f106,f214])).

fof(f214,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl2_24
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f106,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl2_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f3455,plain,
    ( spl2_179
    | ~ spl2_6
    | ~ spl2_16
    | ~ spl2_144
    | ~ spl2_176 ),
    inference(avatar_split_clause,[],[f3401,f3398,f2003,f158,f112,f3453])).

fof(f112,plain,
    ( spl2_6
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f158,plain,
    ( spl2_16
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f2003,plain,
    ( spl2_144
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_144])])).

fof(f3398,plain,
    ( spl2_176
  <=> ! [X3,X4] :
        ( k2_xboole_0(X4,X3) = k5_xboole_0(X4,k1_xboole_0)
        | ~ r1_tarski(X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_176])])).

fof(f3401,plain,
    ( ! [X4,X3] :
        ( k2_xboole_0(X4,X3) = X4
        | ~ r1_tarski(X3,X4) )
    | ~ spl2_6
    | ~ spl2_16
    | ~ spl2_144
    | ~ spl2_176 ),
    inference(forward_demodulation,[],[f3399,f2022])).

fof(f2022,plain,
    ( ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl2_6
    | ~ spl2_16
    | ~ spl2_144 ),
    inference(forward_demodulation,[],[f2011,f113])).

fof(f113,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f2011,plain,
    ( ! [X1] : k5_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k1_xboole_0)
    | ~ spl2_16
    | ~ spl2_144 ),
    inference(superposition,[],[f159,f2004])).

fof(f2004,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_144 ),
    inference(avatar_component_clause,[],[f2003])).

fof(f159,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f158])).

fof(f3399,plain,
    ( ! [X4,X3] :
        ( k2_xboole_0(X4,X3) = k5_xboole_0(X4,k1_xboole_0)
        | ~ r1_tarski(X3,X4) )
    | ~ spl2_176 ),
    inference(avatar_component_clause,[],[f3398])).

fof(f3400,plain,
    ( spl2_176
    | ~ spl2_16
    | ~ spl2_64 ),
    inference(avatar_split_clause,[],[f664,f650,f158,f3398])).

fof(f650,plain,
    ( spl2_64
  <=> ! [X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X1,X2)
        | ~ r1_tarski(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).

fof(f664,plain,
    ( ! [X4,X3] :
        ( k2_xboole_0(X4,X3) = k5_xboole_0(X4,k1_xboole_0)
        | ~ r1_tarski(X3,X4) )
    | ~ spl2_16
    | ~ spl2_64 ),
    inference(superposition,[],[f159,f651])).

fof(f651,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 = k4_xboole_0(X1,X2)
        | ~ r1_tarski(X1,X2) )
    | ~ spl2_64 ),
    inference(avatar_component_clause,[],[f650])).

fof(f2400,plain,
    ( spl2_159
    | ~ spl2_12
    | ~ spl2_85 ),
    inference(avatar_split_clause,[],[f1097,f1066,f136,f2397])).

fof(f136,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f1097,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_12
    | ~ spl2_85 ),
    inference(unit_resulting_resolution,[],[f1068,f137])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f2005,plain,
    ( spl2_144
    | ~ spl2_47
    | ~ spl2_64 ),
    inference(avatar_split_clause,[],[f658,f650,f417,f2003])).

fof(f417,plain,
    ( spl2_47
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f658,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_47
    | ~ spl2_64 ),
    inference(unit_resulting_resolution,[],[f418,f651])).

fof(f418,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f417])).

fof(f1400,plain,
    ( spl2_108
    | ~ spl2_14
    | ~ spl2_55
    | ~ spl2_99
    | ~ spl2_107 ),
    inference(avatar_split_clause,[],[f1395,f1390,f1249,f534,f144,f1397])).

fof(f1395,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_14
    | ~ spl2_55
    | ~ spl2_99
    | ~ spl2_107 ),
    inference(forward_demodulation,[],[f1394,f1251])).

fof(f1251,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_99 ),
    inference(avatar_component_clause,[],[f1249])).

fof(f1393,plain,
    ( spl2_107
    | ~ spl2_3
    | ~ spl2_29
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f327,f314,f249,f96,f1390])).

fof(f249,plain,
    ( spl2_29
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f314,plain,
    ( spl2_36
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f327,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_29
    | ~ spl2_36 ),
    inference(unit_resulting_resolution,[],[f98,f316,f250])).

fof(f250,plain,
    ( ! [X2,X0,X1] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f249])).

fof(f316,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f314])).

fof(f1246,plain,
    ( spl2_98
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_29
    | ~ spl2_33
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f334,f314,f278,f249,f96,f91,f1243])).

fof(f91,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f278,plain,
    ( spl2_33
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f334,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_29
    | ~ spl2_33
    | ~ spl2_36 ),
    inference(forward_demodulation,[],[f329,f300])).

fof(f300,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_33 ),
    inference(unit_resulting_resolution,[],[f93,f98,f279])).

fof(f279,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f278])).

fof(f93,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f329,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_29
    | ~ spl2_36 ),
    inference(unit_resulting_resolution,[],[f98,f316,f250])).

fof(f1104,plain,
    ( spl2_86
    | ~ spl2_39
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f400,f396,f358,f1101])).

fof(f358,plain,
    ( spl2_39
  <=> ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f396,plain,
    ( spl2_44
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f400,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_39
    | ~ spl2_44 ),
    inference(superposition,[],[f398,f359])).

fof(f359,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f358])).

fof(f398,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f396])).

fof(f1099,plain,
    ( ~ spl2_2
    | spl2_85
    | ~ spl2_4
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f262,f243,f96,f101,f1066,f91])).

fof(f101,plain,
    ( spl2_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f243,plain,
    ( spl2_28
  <=> ! [X1,X0] :
        ( r1_tarski(k2_tops_1(X0,X1),X1)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f262,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(resolution,[],[f244,f98])).

fof(f244,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | r1_tarski(k2_tops_1(X0,X1),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f243])).

fof(f1069,plain,
    ( spl2_85
    | ~ spl2_8
    | ~ spl2_46 ),
    inference(avatar_split_clause,[],[f1052,f412,f120,f1066])).

fof(f120,plain,
    ( spl2_8
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f412,plain,
    ( spl2_46
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f1052,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_8
    | ~ spl2_46 ),
    inference(superposition,[],[f121,f414])).

fof(f414,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f412])).

fof(f121,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f685,plain,
    ( spl2_66
    | ~ spl2_18
    | ~ spl2_22
    | ~ spl2_50
    | ~ spl2_65 ),
    inference(avatar_split_clause,[],[f681,f678,f464,f203,f167,f683])).

fof(f203,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f464,plain,
    ( spl2_50
  <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f678,plain,
    ( spl2_65
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).

fof(f681,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_18
    | ~ spl2_22
    | ~ spl2_50
    | ~ spl2_65 ),
    inference(forward_demodulation,[],[f679,f491])).

fof(f491,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,X1))
    | ~ spl2_18
    | ~ spl2_22
    | ~ spl2_50 ),
    inference(forward_demodulation,[],[f472,f168])).

fof(f472,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1))
    | ~ spl2_22
    | ~ spl2_50 ),
    inference(unit_resulting_resolution,[],[f465,f204])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f203])).

fof(f465,plain,
    ( ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f464])).

fof(f679,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_65 ),
    inference(avatar_component_clause,[],[f678])).

fof(f680,plain,
    ( spl2_65
    | ~ spl2_22
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f229,f207,f203,f678])).

fof(f207,plain,
    ( spl2_23
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f229,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_22
    | ~ spl2_23 ),
    inference(duplicate_literal_removal,[],[f225])).

fof(f225,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_22
    | ~ spl2_23 ),
    inference(superposition,[],[f208,f204])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f207])).

fof(f652,plain,
    ( spl2_64
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f197,f171,f148,f124,f116,f112,f650])).

fof(f116,plain,
    ( spl2_7
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f124,plain,
    ( spl2_9
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f148,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f171,plain,
    ( spl2_19
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f197,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 = k4_xboole_0(X1,X2)
        | ~ r1_tarski(X1,X2) )
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f195,f196])).

fof(f196,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f194,f151])).

fof(f151,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(superposition,[],[f125,f113])).

fof(f125,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f194,plain,
    ( ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)
    | ~ spl2_7
    | ~ spl2_19 ),
    inference(superposition,[],[f172,f117])).

fof(f117,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f172,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f171])).

fof(f195,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1)
        | ~ r1_tarski(X1,X2) )
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(superposition,[],[f172,f149])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f148])).

fof(f536,plain,
    ( spl2_55
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f180,f144,f128,f534])).

fof(f128,plain,
    ( spl2_10
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f180,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(superposition,[],[f145,f129])).

fof(f129,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f466,plain,
    ( spl2_50
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f155,f136,f120,f464])).

fof(f155,plain,
    ( ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f121,f137])).

fof(f419,plain,
    ( spl2_47
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f152,f124,f120,f417])).

fof(f152,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(superposition,[],[f121,f125])).

fof(f415,plain,
    ( ~ spl2_3
    | spl2_46
    | ~ spl2_5
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f232,f213,f105,f412,f96])).

fof(f232,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5
    | ~ spl2_24 ),
    inference(superposition,[],[f214,f107])).

fof(f107,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f399,plain,
    ( spl2_44
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f293,f274,f96,f91,f396])).

fof(f274,plain,
    ( spl2_32
  <=> ! [X1,X0] :
        ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f293,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_32 ),
    inference(unit_resulting_resolution,[],[f93,f98,f275])).

fof(f275,plain,
    ( ! [X0,X1] :
        ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f274])).

fof(f360,plain,
    ( spl2_39
    | ~ spl2_3
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f231,f213,f96,f358])).

fof(f231,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3
    | ~ spl2_24 ),
    inference(unit_resulting_resolution,[],[f98,f214])).

fof(f341,plain,
    ( ~ spl2_37
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f288,f269,f101,f96,f91,f86,f338])).

fof(f86,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f269,plain,
    ( spl2_31
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) != X1
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f288,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_31 ),
    inference(unit_resulting_resolution,[],[f93,f88,f102,f98,f270])).

fof(f270,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) != X1
        | v4_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f269])).

fof(f102,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f88,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f317,plain,
    ( spl2_36
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f246,f235,f96,f91,f314])).

fof(f235,plain,
    ( spl2_26
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f246,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_26 ),
    inference(unit_resulting_resolution,[],[f93,f98,f236])).

fof(f236,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f235])).

fof(f280,plain,(
    spl2_33 ),
    inference(avatar_split_clause,[],[f62,f278])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f276,plain,(
    spl2_32 ),
    inference(avatar_split_clause,[],[f61,f274])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f271,plain,(
    spl2_31 ),
    inference(avatar_split_clause,[],[f64,f269])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f251,plain,(
    spl2_29 ),
    inference(avatar_split_clause,[],[f84,f249])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f245,plain,(
    spl2_28 ),
    inference(avatar_split_clause,[],[f65,f243])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f237,plain,(
    spl2_26 ),
    inference(avatar_split_clause,[],[f79,f235])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f215,plain,(
    spl2_24 ),
    inference(avatar_split_clause,[],[f82,f213])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f209,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f78,f207])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f205,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f77,f203])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f173,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f74,f171])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f169,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f73,f167])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f160,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f72,f158])).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f150,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f75,f148])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f146,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f71,f144])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f138,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f81,f136])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f130,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f69,f128])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f126,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f68,f124])).

fof(f68,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f122,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f67,f120])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f118,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f66,f116])).

fof(f66,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f114,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f59,f112])).

fof(f59,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f110,plain,
    ( ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f109,f105,f101])).

fof(f109,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f58,f107])).

fof(f58,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f108,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f57,f105,f101])).

fof(f57,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f99,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f56,f96])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f94,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f55,f91])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f54,f86])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (32763)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.44  % (32753)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (32747)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (32749)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (32748)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (32762)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (32746)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (32760)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (32750)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (32751)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (32752)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (32756)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (32755)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (32754)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (32759)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.50  % (32758)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.50  % (32757)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.33/0.52  % (32761)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 2.18/0.66  % (32751)Refutation found. Thanks to Tanya!
% 2.18/0.66  % SZS status Theorem for theBenchmark
% 2.18/0.66  % SZS output start Proof for theBenchmark
% 2.18/0.66  fof(f3735,plain,(
% 2.18/0.66    $false),
% 2.18/0.66    inference(avatar_sat_refutation,[],[f89,f94,f99,f108,f110,f114,f118,f122,f126,f130,f138,f146,f150,f160,f169,f173,f205,f209,f215,f237,f245,f251,f271,f276,f280,f317,f341,f360,f399,f415,f419,f466,f536,f652,f680,f685,f1069,f1099,f1104,f1246,f1393,f1400,f2005,f2400,f3400,f3455,f3704,f3732,f3734])).
% 2.18/0.66  fof(f3734,plain,(
% 2.18/0.66    ~spl2_85 | spl2_99 | ~spl2_179),
% 2.18/0.66    inference(avatar_contradiction_clause,[],[f3733])).
% 2.18/0.66  fof(f3733,plain,(
% 2.18/0.66    $false | (~spl2_85 | spl2_99 | ~spl2_179)),
% 2.18/0.66    inference(subsumption_resolution,[],[f3470,f1250])).
% 2.18/0.66  fof(f1250,plain,(
% 2.18/0.66    sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | spl2_99),
% 2.18/0.66    inference(avatar_component_clause,[],[f1249])).
% 2.18/0.66  fof(f1249,plain,(
% 2.18/0.66    spl2_99 <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_99])])).
% 2.18/0.66  fof(f3470,plain,(
% 2.18/0.66    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_85 | ~spl2_179)),
% 2.18/0.66    inference(unit_resulting_resolution,[],[f1068,f3454])).
% 2.18/0.66  fof(f3454,plain,(
% 2.18/0.66    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = X4 | ~r1_tarski(X3,X4)) ) | ~spl2_179),
% 2.18/0.66    inference(avatar_component_clause,[],[f3453])).
% 2.18/0.66  fof(f3453,plain,(
% 2.18/0.66    spl2_179 <=> ! [X3,X4] : (k2_xboole_0(X4,X3) = X4 | ~r1_tarski(X3,X4))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_179])])).
% 2.18/0.66  fof(f1068,plain,(
% 2.18/0.66    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_85),
% 2.18/0.66    inference(avatar_component_clause,[],[f1066])).
% 2.18/0.66  fof(f1066,plain,(
% 2.18/0.66    spl2_85 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_85])])).
% 2.18/0.66  fof(f3732,plain,(
% 2.18/0.66    ~spl2_14 | spl2_37 | ~spl2_55 | ~spl2_98 | ~spl2_107 | ~spl2_108),
% 2.18/0.66    inference(avatar_contradiction_clause,[],[f3731])).
% 2.18/0.66  fof(f3731,plain,(
% 2.18/0.66    $false | (~spl2_14 | spl2_37 | ~spl2_55 | ~spl2_98 | ~spl2_107 | ~spl2_108)),
% 2.18/0.66    inference(subsumption_resolution,[],[f340,f3730])).
% 2.18/0.66  fof(f3730,plain,(
% 2.18/0.66    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_14 | ~spl2_55 | ~spl2_98 | ~spl2_107 | ~spl2_108)),
% 2.18/0.66    inference(forward_demodulation,[],[f3729,f1399])).
% 2.18/0.66  fof(f1399,plain,(
% 2.18/0.66    sK1 = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) | ~spl2_108),
% 2.18/0.66    inference(avatar_component_clause,[],[f1397])).
% 2.18/0.66  fof(f1397,plain,(
% 2.18/0.66    spl2_108 <=> sK1 = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_108])])).
% 2.18/0.66  fof(f3729,plain,(
% 2.18/0.66    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) | (~spl2_14 | ~spl2_55 | ~spl2_98 | ~spl2_107)),
% 2.18/0.66    inference(forward_demodulation,[],[f1394,f1245])).
% 2.18/0.66  fof(f1245,plain,(
% 2.18/0.66    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_98),
% 2.18/0.66    inference(avatar_component_clause,[],[f1243])).
% 2.18/0.66  fof(f1243,plain,(
% 2.18/0.66    spl2_98 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).
% 2.18/0.66  fof(f1394,plain,(
% 2.18/0.66    k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_14 | ~spl2_55 | ~spl2_107)),
% 2.18/0.66    inference(forward_demodulation,[],[f1392,f539])).
% 2.18/0.66  fof(f539,plain,(
% 2.18/0.66    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) ) | (~spl2_14 | ~spl2_55)),
% 2.18/0.66    inference(superposition,[],[f535,f145])).
% 2.18/0.66  fof(f145,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) ) | ~spl2_14),
% 2.18/0.66    inference(avatar_component_clause,[],[f144])).
% 2.18/0.66  fof(f144,plain,(
% 2.18/0.66    spl2_14 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 2.18/0.66  fof(f535,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) ) | ~spl2_55),
% 2.18/0.66    inference(avatar_component_clause,[],[f534])).
% 2.18/0.66  fof(f534,plain,(
% 2.18/0.66    spl2_55 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 2.18/0.66  fof(f1392,plain,(
% 2.18/0.66    k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_107),
% 2.18/0.66    inference(avatar_component_clause,[],[f1390])).
% 2.18/0.66  fof(f1390,plain,(
% 2.18/0.66    spl2_107 <=> k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_107])])).
% 2.18/0.66  fof(f340,plain,(
% 2.18/0.66    sK1 != k2_pre_topc(sK0,sK1) | spl2_37),
% 2.18/0.66    inference(avatar_component_clause,[],[f338])).
% 2.18/0.66  fof(f338,plain,(
% 2.18/0.66    spl2_37 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 2.18/0.66  fof(f3704,plain,(
% 2.18/0.66    ~spl2_3 | spl2_5 | ~spl2_18 | ~spl2_24 | ~spl2_66 | ~spl2_86 | ~spl2_159),
% 2.18/0.66    inference(avatar_contradiction_clause,[],[f3703])).
% 2.18/0.66  fof(f3703,plain,(
% 2.18/0.66    $false | (~spl2_3 | spl2_5 | ~spl2_18 | ~spl2_24 | ~spl2_66 | ~spl2_86 | ~spl2_159)),
% 2.18/0.66    inference(subsumption_resolution,[],[f98,f3702])).
% 2.18/0.66  fof(f3702,plain,(
% 2.18/0.66    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_5 | ~spl2_18 | ~spl2_24 | ~spl2_66 | ~spl2_86 | ~spl2_159)),
% 2.18/0.66    inference(trivial_inequality_removal,[],[f3701])).
% 2.18/0.66  fof(f3701,plain,(
% 2.18/0.66    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_5 | ~spl2_18 | ~spl2_24 | ~spl2_66 | ~spl2_86 | ~spl2_159)),
% 2.18/0.66    inference(forward_demodulation,[],[f3700,f2685])).
% 2.18/0.66  fof(f2685,plain,(
% 2.18/0.66    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_66 | ~spl2_159)),
% 2.18/0.66    inference(unit_resulting_resolution,[],[f2399,f684])).
% 2.18/0.66  fof(f684,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_66),
% 2.18/0.66    inference(avatar_component_clause,[],[f683])).
% 2.18/0.66  fof(f683,plain,(
% 2.18/0.66    spl2_66 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).
% 2.18/0.66  fof(f2399,plain,(
% 2.18/0.66    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_159),
% 2.18/0.66    inference(avatar_component_clause,[],[f2397])).
% 2.18/0.66  fof(f2397,plain,(
% 2.18/0.66    spl2_159 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_159])])).
% 2.18/0.66  fof(f3700,plain,(
% 2.18/0.66    k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_5 | ~spl2_18 | ~spl2_24 | ~spl2_86)),
% 2.18/0.66    inference(forward_demodulation,[],[f1082,f1110])).
% 2.18/0.66  fof(f1110,plain,(
% 2.18/0.66    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_18 | ~spl2_86)),
% 2.18/0.66    inference(superposition,[],[f168,f1103])).
% 2.18/0.66  fof(f1103,plain,(
% 2.18/0.66    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_86),
% 2.18/0.66    inference(avatar_component_clause,[],[f1101])).
% 2.18/0.66  fof(f1101,plain,(
% 2.18/0.66    spl2_86 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).
% 2.18/0.66  fof(f168,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_18),
% 2.18/0.66    inference(avatar_component_clause,[],[f167])).
% 2.18/0.66  fof(f167,plain,(
% 2.18/0.66    spl2_18 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 2.18/0.66  fof(f1082,plain,(
% 2.18/0.66    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_5 | ~spl2_24)),
% 2.18/0.66    inference(superposition,[],[f106,f214])).
% 2.18/0.66  fof(f214,plain,(
% 2.18/0.66    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_24),
% 2.18/0.66    inference(avatar_component_clause,[],[f213])).
% 2.18/0.66  fof(f213,plain,(
% 2.18/0.66    spl2_24 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 2.18/0.66  fof(f106,plain,(
% 2.18/0.66    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_5),
% 2.18/0.66    inference(avatar_component_clause,[],[f105])).
% 2.18/0.66  fof(f105,plain,(
% 2.18/0.66    spl2_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.18/0.66  fof(f98,plain,(
% 2.18/0.66    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 2.18/0.66    inference(avatar_component_clause,[],[f96])).
% 2.18/0.66  fof(f96,plain,(
% 2.18/0.66    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.18/0.66  fof(f3455,plain,(
% 2.18/0.66    spl2_179 | ~spl2_6 | ~spl2_16 | ~spl2_144 | ~spl2_176),
% 2.18/0.66    inference(avatar_split_clause,[],[f3401,f3398,f2003,f158,f112,f3453])).
% 2.18/0.66  fof(f112,plain,(
% 2.18/0.66    spl2_6 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 2.18/0.66  fof(f158,plain,(
% 2.18/0.66    spl2_16 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 2.18/0.66  fof(f2003,plain,(
% 2.18/0.66    spl2_144 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_144])])).
% 2.18/0.66  fof(f3398,plain,(
% 2.18/0.66    spl2_176 <=> ! [X3,X4] : (k2_xboole_0(X4,X3) = k5_xboole_0(X4,k1_xboole_0) | ~r1_tarski(X3,X4))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_176])])).
% 2.18/0.66  fof(f3401,plain,(
% 2.18/0.66    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = X4 | ~r1_tarski(X3,X4)) ) | (~spl2_6 | ~spl2_16 | ~spl2_144 | ~spl2_176)),
% 2.18/0.66    inference(forward_demodulation,[],[f3399,f2022])).
% 2.18/0.66  fof(f2022,plain,(
% 2.18/0.66    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) ) | (~spl2_6 | ~spl2_16 | ~spl2_144)),
% 2.18/0.66    inference(forward_demodulation,[],[f2011,f113])).
% 2.18/0.66  fof(f113,plain,(
% 2.18/0.66    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_6),
% 2.18/0.66    inference(avatar_component_clause,[],[f112])).
% 2.18/0.66  fof(f2011,plain,(
% 2.18/0.66    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k1_xboole_0)) ) | (~spl2_16 | ~spl2_144)),
% 2.18/0.66    inference(superposition,[],[f159,f2004])).
% 2.18/0.66  fof(f2004,plain,(
% 2.18/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl2_144),
% 2.18/0.66    inference(avatar_component_clause,[],[f2003])).
% 2.18/0.66  fof(f159,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_16),
% 2.18/0.66    inference(avatar_component_clause,[],[f158])).
% 2.18/0.66  fof(f3399,plain,(
% 2.18/0.66    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k5_xboole_0(X4,k1_xboole_0) | ~r1_tarski(X3,X4)) ) | ~spl2_176),
% 2.18/0.66    inference(avatar_component_clause,[],[f3398])).
% 2.18/0.66  fof(f3400,plain,(
% 2.18/0.66    spl2_176 | ~spl2_16 | ~spl2_64),
% 2.18/0.66    inference(avatar_split_clause,[],[f664,f650,f158,f3398])).
% 2.18/0.66  fof(f650,plain,(
% 2.18/0.66    spl2_64 <=> ! [X1,X2] : (k1_xboole_0 = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).
% 2.18/0.66  fof(f664,plain,(
% 2.18/0.66    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k5_xboole_0(X4,k1_xboole_0) | ~r1_tarski(X3,X4)) ) | (~spl2_16 | ~spl2_64)),
% 2.18/0.66    inference(superposition,[],[f159,f651])).
% 2.18/0.66  fof(f651,plain,(
% 2.18/0.66    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) ) | ~spl2_64),
% 2.18/0.66    inference(avatar_component_clause,[],[f650])).
% 2.18/0.66  fof(f2400,plain,(
% 2.18/0.66    spl2_159 | ~spl2_12 | ~spl2_85),
% 2.18/0.66    inference(avatar_split_clause,[],[f1097,f1066,f136,f2397])).
% 2.18/0.66  fof(f136,plain,(
% 2.18/0.66    spl2_12 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 2.18/0.66  fof(f1097,plain,(
% 2.18/0.66    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | (~spl2_12 | ~spl2_85)),
% 2.18/0.66    inference(unit_resulting_resolution,[],[f1068,f137])).
% 2.18/0.66  fof(f137,plain,(
% 2.18/0.66    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_12),
% 2.18/0.66    inference(avatar_component_clause,[],[f136])).
% 2.18/0.66  fof(f2005,plain,(
% 2.18/0.66    spl2_144 | ~spl2_47 | ~spl2_64),
% 2.18/0.66    inference(avatar_split_clause,[],[f658,f650,f417,f2003])).
% 2.18/0.66  fof(f417,plain,(
% 2.18/0.66    spl2_47 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 2.18/0.66  fof(f658,plain,(
% 2.18/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl2_47 | ~spl2_64)),
% 2.18/0.66    inference(unit_resulting_resolution,[],[f418,f651])).
% 2.18/0.66  fof(f418,plain,(
% 2.18/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl2_47),
% 2.18/0.66    inference(avatar_component_clause,[],[f417])).
% 2.18/0.66  fof(f1400,plain,(
% 2.18/0.66    spl2_108 | ~spl2_14 | ~spl2_55 | ~spl2_99 | ~spl2_107),
% 2.18/0.66    inference(avatar_split_clause,[],[f1395,f1390,f1249,f534,f144,f1397])).
% 2.18/0.66  fof(f1395,plain,(
% 2.18/0.66    sK1 = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) | (~spl2_14 | ~spl2_55 | ~spl2_99 | ~spl2_107)),
% 2.18/0.66    inference(forward_demodulation,[],[f1394,f1251])).
% 2.18/0.66  fof(f1251,plain,(
% 2.18/0.66    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_99),
% 2.18/0.66    inference(avatar_component_clause,[],[f1249])).
% 2.18/0.66  fof(f1393,plain,(
% 2.18/0.66    spl2_107 | ~spl2_3 | ~spl2_29 | ~spl2_36),
% 2.18/0.66    inference(avatar_split_clause,[],[f327,f314,f249,f96,f1390])).
% 2.18/0.66  fof(f249,plain,(
% 2.18/0.66    spl2_29 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 2.18/0.66  fof(f314,plain,(
% 2.18/0.66    spl2_36 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 2.18/0.66  fof(f327,plain,(
% 2.18/0.66    k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_29 | ~spl2_36)),
% 2.18/0.66    inference(unit_resulting_resolution,[],[f98,f316,f250])).
% 2.18/0.66  fof(f250,plain,(
% 2.18/0.66    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_29),
% 2.18/0.66    inference(avatar_component_clause,[],[f249])).
% 2.18/0.66  fof(f316,plain,(
% 2.18/0.66    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_36),
% 2.18/0.66    inference(avatar_component_clause,[],[f314])).
% 2.18/0.66  fof(f1246,plain,(
% 2.18/0.66    spl2_98 | ~spl2_2 | ~spl2_3 | ~spl2_29 | ~spl2_33 | ~spl2_36),
% 2.18/0.66    inference(avatar_split_clause,[],[f334,f314,f278,f249,f96,f91,f1243])).
% 2.18/0.66  fof(f91,plain,(
% 2.18/0.66    spl2_2 <=> l1_pre_topc(sK0)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.18/0.66  fof(f278,plain,(
% 2.18/0.66    spl2_33 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 2.18/0.66  fof(f334,plain,(
% 2.18/0.66    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_29 | ~spl2_33 | ~spl2_36)),
% 2.18/0.66    inference(forward_demodulation,[],[f329,f300])).
% 2.18/0.66  fof(f300,plain,(
% 2.18/0.66    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_33)),
% 2.18/0.66    inference(unit_resulting_resolution,[],[f93,f98,f279])).
% 2.18/0.66  fof(f279,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_33),
% 2.18/0.66    inference(avatar_component_clause,[],[f278])).
% 2.18/0.66  fof(f93,plain,(
% 2.18/0.66    l1_pre_topc(sK0) | ~spl2_2),
% 2.18/0.66    inference(avatar_component_clause,[],[f91])).
% 2.18/0.66  fof(f329,plain,(
% 2.18/0.66    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_29 | ~spl2_36)),
% 2.18/0.66    inference(unit_resulting_resolution,[],[f98,f316,f250])).
% 2.18/0.66  fof(f1104,plain,(
% 2.18/0.66    spl2_86 | ~spl2_39 | ~spl2_44),
% 2.18/0.66    inference(avatar_split_clause,[],[f400,f396,f358,f1101])).
% 2.18/0.66  fof(f358,plain,(
% 2.18/0.66    spl2_39 <=> ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 2.18/0.66  fof(f396,plain,(
% 2.18/0.66    spl2_44 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 2.18/0.66  fof(f400,plain,(
% 2.18/0.66    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_39 | ~spl2_44)),
% 2.18/0.66    inference(superposition,[],[f398,f359])).
% 2.18/0.66  fof(f359,plain,(
% 2.18/0.66    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_39),
% 2.18/0.66    inference(avatar_component_clause,[],[f358])).
% 2.18/0.66  fof(f398,plain,(
% 2.18/0.66    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_44),
% 2.18/0.66    inference(avatar_component_clause,[],[f396])).
% 2.18/0.66  fof(f1099,plain,(
% 2.18/0.66    ~spl2_2 | spl2_85 | ~spl2_4 | ~spl2_3 | ~spl2_28),
% 2.18/0.66    inference(avatar_split_clause,[],[f262,f243,f96,f101,f1066,f91])).
% 2.18/0.66  fof(f101,plain,(
% 2.18/0.66    spl2_4 <=> v4_pre_topc(sK1,sK0)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.18/0.66  fof(f243,plain,(
% 2.18/0.66    spl2_28 <=> ! [X1,X0] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 2.18/0.66  fof(f262,plain,(
% 2.18/0.66    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_28)),
% 2.18/0.66    inference(resolution,[],[f244,f98])).
% 2.18/0.66  fof(f244,plain,(
% 2.18/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) ) | ~spl2_28),
% 2.18/0.66    inference(avatar_component_clause,[],[f243])).
% 2.18/0.66  fof(f1069,plain,(
% 2.18/0.66    spl2_85 | ~spl2_8 | ~spl2_46),
% 2.18/0.66    inference(avatar_split_clause,[],[f1052,f412,f120,f1066])).
% 2.18/0.66  fof(f120,plain,(
% 2.18/0.66    spl2_8 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 2.18/0.66  fof(f412,plain,(
% 2.18/0.66    spl2_46 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 2.18/0.66  fof(f1052,plain,(
% 2.18/0.66    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_8 | ~spl2_46)),
% 2.18/0.66    inference(superposition,[],[f121,f414])).
% 2.18/0.66  fof(f414,plain,(
% 2.18/0.66    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_46),
% 2.18/0.66    inference(avatar_component_clause,[],[f412])).
% 2.18/0.66  fof(f121,plain,(
% 2.18/0.66    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_8),
% 2.18/0.66    inference(avatar_component_clause,[],[f120])).
% 2.18/0.66  fof(f685,plain,(
% 2.18/0.66    spl2_66 | ~spl2_18 | ~spl2_22 | ~spl2_50 | ~spl2_65),
% 2.18/0.66    inference(avatar_split_clause,[],[f681,f678,f464,f203,f167,f683])).
% 2.18/0.66  fof(f203,plain,(
% 2.18/0.66    spl2_22 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 2.18/0.66  fof(f464,plain,(
% 2.18/0.66    spl2_50 <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 2.18/0.66  fof(f678,plain,(
% 2.18/0.66    spl2_65 <=> ! [X1,X0] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).
% 2.18/0.66  fof(f681,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl2_18 | ~spl2_22 | ~spl2_50 | ~spl2_65)),
% 2.18/0.66    inference(forward_demodulation,[],[f679,f491])).
% 2.18/0.66  fof(f491,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,X1))) ) | (~spl2_18 | ~spl2_22 | ~spl2_50)),
% 2.18/0.66    inference(forward_demodulation,[],[f472,f168])).
% 2.18/0.66  fof(f472,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1))) ) | (~spl2_22 | ~spl2_50)),
% 2.18/0.66    inference(unit_resulting_resolution,[],[f465,f204])).
% 2.18/0.66  fof(f204,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_22),
% 2.18/0.66    inference(avatar_component_clause,[],[f203])).
% 2.18/0.66  fof(f465,plain,(
% 2.18/0.66    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl2_50),
% 2.18/0.66    inference(avatar_component_clause,[],[f464])).
% 2.18/0.66  fof(f679,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_65),
% 2.18/0.66    inference(avatar_component_clause,[],[f678])).
% 2.18/0.66  fof(f680,plain,(
% 2.18/0.66    spl2_65 | ~spl2_22 | ~spl2_23),
% 2.18/0.66    inference(avatar_split_clause,[],[f229,f207,f203,f678])).
% 2.18/0.66  fof(f207,plain,(
% 2.18/0.66    spl2_23 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 2.18/0.66  fof(f229,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl2_22 | ~spl2_23)),
% 2.18/0.66    inference(duplicate_literal_removal,[],[f225])).
% 2.18/0.66  fof(f225,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl2_22 | ~spl2_23)),
% 2.18/0.66    inference(superposition,[],[f208,f204])).
% 2.18/0.66  fof(f208,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_23),
% 2.18/0.66    inference(avatar_component_clause,[],[f207])).
% 2.18/0.66  fof(f652,plain,(
% 2.18/0.66    spl2_64 | ~spl2_6 | ~spl2_7 | ~spl2_9 | ~spl2_15 | ~spl2_19),
% 2.18/0.66    inference(avatar_split_clause,[],[f197,f171,f148,f124,f116,f112,f650])).
% 2.18/0.66  fof(f116,plain,(
% 2.18/0.66    spl2_7 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 2.18/0.66  fof(f124,plain,(
% 2.18/0.66    spl2_9 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 2.18/0.66  fof(f148,plain,(
% 2.18/0.66    spl2_15 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 2.18/0.66  fof(f171,plain,(
% 2.18/0.66    spl2_19 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 2.18/0.66  fof(f197,plain,(
% 2.18/0.66    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) ) | (~spl2_6 | ~spl2_7 | ~spl2_9 | ~spl2_15 | ~spl2_19)),
% 2.18/0.66    inference(forward_demodulation,[],[f195,f196])).
% 2.18/0.66  fof(f196,plain,(
% 2.18/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | (~spl2_6 | ~spl2_7 | ~spl2_9 | ~spl2_19)),
% 2.18/0.66    inference(forward_demodulation,[],[f194,f151])).
% 2.18/0.66  fof(f151,plain,(
% 2.18/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl2_6 | ~spl2_9)),
% 2.18/0.66    inference(superposition,[],[f125,f113])).
% 2.18/0.66  fof(f125,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | ~spl2_9),
% 2.18/0.66    inference(avatar_component_clause,[],[f124])).
% 2.18/0.66  fof(f194,plain,(
% 2.18/0.66    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) ) | (~spl2_7 | ~spl2_19)),
% 2.18/0.66    inference(superposition,[],[f172,f117])).
% 2.18/0.66  fof(f117,plain,(
% 2.18/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl2_7),
% 2.18/0.66    inference(avatar_component_clause,[],[f116])).
% 2.18/0.66  fof(f172,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_19),
% 2.18/0.66    inference(avatar_component_clause,[],[f171])).
% 2.18/0.66  fof(f195,plain,(
% 2.18/0.66    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1) | ~r1_tarski(X1,X2)) ) | (~spl2_15 | ~spl2_19)),
% 2.18/0.66    inference(superposition,[],[f172,f149])).
% 2.18/0.66  fof(f149,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_15),
% 2.18/0.66    inference(avatar_component_clause,[],[f148])).
% 2.18/0.66  fof(f536,plain,(
% 2.18/0.66    spl2_55 | ~spl2_10 | ~spl2_14),
% 2.18/0.66    inference(avatar_split_clause,[],[f180,f144,f128,f534])).
% 2.18/0.66  fof(f128,plain,(
% 2.18/0.66    spl2_10 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 2.18/0.66  fof(f180,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) ) | (~spl2_10 | ~spl2_14)),
% 2.18/0.66    inference(superposition,[],[f145,f129])).
% 2.18/0.66  fof(f129,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_10),
% 2.18/0.66    inference(avatar_component_clause,[],[f128])).
% 2.18/0.66  fof(f466,plain,(
% 2.18/0.66    spl2_50 | ~spl2_8 | ~spl2_12),
% 2.18/0.66    inference(avatar_split_clause,[],[f155,f136,f120,f464])).
% 2.18/0.66  fof(f155,plain,(
% 2.18/0.66    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | (~spl2_8 | ~spl2_12)),
% 2.18/0.66    inference(unit_resulting_resolution,[],[f121,f137])).
% 2.18/0.66  fof(f419,plain,(
% 2.18/0.66    spl2_47 | ~spl2_8 | ~spl2_9),
% 2.18/0.66    inference(avatar_split_clause,[],[f152,f124,f120,f417])).
% 2.18/0.66  fof(f152,plain,(
% 2.18/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl2_8 | ~spl2_9)),
% 2.18/0.66    inference(superposition,[],[f121,f125])).
% 2.18/0.66  fof(f415,plain,(
% 2.18/0.66    ~spl2_3 | spl2_46 | ~spl2_5 | ~spl2_24),
% 2.18/0.66    inference(avatar_split_clause,[],[f232,f213,f105,f412,f96])).
% 2.18/0.66  fof(f232,plain,(
% 2.18/0.66    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_5 | ~spl2_24)),
% 2.18/0.66    inference(superposition,[],[f214,f107])).
% 2.18/0.66  fof(f107,plain,(
% 2.18/0.66    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_5),
% 2.18/0.66    inference(avatar_component_clause,[],[f105])).
% 2.18/0.66  fof(f399,plain,(
% 2.18/0.66    spl2_44 | ~spl2_2 | ~spl2_3 | ~spl2_32),
% 2.18/0.66    inference(avatar_split_clause,[],[f293,f274,f96,f91,f396])).
% 2.18/0.66  fof(f274,plain,(
% 2.18/0.66    spl2_32 <=> ! [X1,X0] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 2.18/0.66  fof(f293,plain,(
% 2.18/0.66    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_32)),
% 2.18/0.66    inference(unit_resulting_resolution,[],[f93,f98,f275])).
% 2.18/0.66  fof(f275,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_32),
% 2.18/0.66    inference(avatar_component_clause,[],[f274])).
% 2.18/0.66  fof(f360,plain,(
% 2.18/0.66    spl2_39 | ~spl2_3 | ~spl2_24),
% 2.18/0.66    inference(avatar_split_clause,[],[f231,f213,f96,f358])).
% 2.18/0.66  fof(f231,plain,(
% 2.18/0.66    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | (~spl2_3 | ~spl2_24)),
% 2.18/0.66    inference(unit_resulting_resolution,[],[f98,f214])).
% 2.18/0.66  fof(f341,plain,(
% 2.18/0.66    ~spl2_37 | ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_31),
% 2.18/0.66    inference(avatar_split_clause,[],[f288,f269,f101,f96,f91,f86,f338])).
% 2.18/0.66  fof(f86,plain,(
% 2.18/0.66    spl2_1 <=> v2_pre_topc(sK0)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.18/0.66  fof(f269,plain,(
% 2.18/0.66    spl2_31 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 2.18/0.66  fof(f288,plain,(
% 2.18/0.66    sK1 != k2_pre_topc(sK0,sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_31)),
% 2.18/0.66    inference(unit_resulting_resolution,[],[f93,f88,f102,f98,f270])).
% 2.18/0.66  fof(f270,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_31),
% 2.18/0.66    inference(avatar_component_clause,[],[f269])).
% 2.18/0.66  fof(f102,plain,(
% 2.18/0.66    ~v4_pre_topc(sK1,sK0) | spl2_4),
% 2.18/0.66    inference(avatar_component_clause,[],[f101])).
% 2.18/0.66  fof(f88,plain,(
% 2.18/0.66    v2_pre_topc(sK0) | ~spl2_1),
% 2.18/0.66    inference(avatar_component_clause,[],[f86])).
% 2.18/0.66  fof(f317,plain,(
% 2.18/0.66    spl2_36 | ~spl2_2 | ~spl2_3 | ~spl2_26),
% 2.18/0.66    inference(avatar_split_clause,[],[f246,f235,f96,f91,f314])).
% 2.18/0.66  fof(f235,plain,(
% 2.18/0.66    spl2_26 <=> ! [X1,X0] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 2.18/0.66  fof(f246,plain,(
% 2.18/0.66    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3 | ~spl2_26)),
% 2.18/0.66    inference(unit_resulting_resolution,[],[f93,f98,f236])).
% 2.18/0.66  fof(f236,plain,(
% 2.18/0.66    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_26),
% 2.18/0.66    inference(avatar_component_clause,[],[f235])).
% 2.18/0.66  fof(f280,plain,(
% 2.18/0.66    spl2_33),
% 2.18/0.66    inference(avatar_split_clause,[],[f62,f278])).
% 2.18/0.66  fof(f62,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f32])).
% 2.18/0.66  fof(f32,plain,(
% 2.18/0.66    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.66    inference(ennf_transformation,[],[f22])).
% 2.18/0.66  fof(f22,axiom,(
% 2.18/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.18/0.66  fof(f276,plain,(
% 2.18/0.66    spl2_32),
% 2.18/0.66    inference(avatar_split_clause,[],[f61,f274])).
% 2.18/0.66  fof(f61,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f31])).
% 2.18/0.66  fof(f31,plain,(
% 2.18/0.66    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.66    inference(ennf_transformation,[],[f24])).
% 2.18/0.66  fof(f24,axiom,(
% 2.18/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.18/0.66  fof(f271,plain,(
% 2.18/0.66    spl2_31),
% 2.18/0.66    inference(avatar_split_clause,[],[f64,f269])).
% 2.18/0.66  fof(f64,plain,(
% 2.18/0.66    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f34])).
% 2.18/0.66  fof(f34,plain,(
% 2.18/0.66    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.66    inference(flattening,[],[f33])).
% 2.18/0.66  fof(f33,plain,(
% 2.18/0.66    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.66    inference(ennf_transformation,[],[f19])).
% 2.18/0.66  fof(f19,axiom,(
% 2.18/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.18/0.66  fof(f251,plain,(
% 2.18/0.66    spl2_29),
% 2.18/0.66    inference(avatar_split_clause,[],[f84,f249])).
% 2.18/0.66  fof(f84,plain,(
% 2.18/0.66    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f47])).
% 2.18/0.66  fof(f47,plain,(
% 2.18/0.66    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.66    inference(flattening,[],[f46])).
% 2.18/0.66  fof(f46,plain,(
% 2.18/0.66    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.18/0.66    inference(ennf_transformation,[],[f15])).
% 2.18/0.66  fof(f15,axiom,(
% 2.18/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.18/0.66  fof(f245,plain,(
% 2.18/0.66    spl2_28),
% 2.18/0.66    inference(avatar_split_clause,[],[f65,f243])).
% 2.18/0.66  fof(f65,plain,(
% 2.18/0.66    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f36])).
% 2.18/0.66  fof(f36,plain,(
% 2.18/0.66    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.66    inference(flattening,[],[f35])).
% 2.18/0.66  fof(f35,plain,(
% 2.18/0.66    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.66    inference(ennf_transformation,[],[f23])).
% 2.18/0.66  fof(f23,axiom,(
% 2.18/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 2.18/0.66  fof(f237,plain,(
% 2.18/0.66    spl2_26),
% 2.18/0.66    inference(avatar_split_clause,[],[f79,f235])).
% 2.18/0.66  fof(f79,plain,(
% 2.18/0.66    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f42])).
% 2.18/0.66  fof(f42,plain,(
% 2.18/0.66    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.18/0.66    inference(flattening,[],[f41])).
% 2.18/0.66  fof(f41,plain,(
% 2.18/0.66    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.18/0.66    inference(ennf_transformation,[],[f20])).
% 2.18/0.66  fof(f20,axiom,(
% 2.18/0.66    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.18/0.66  fof(f215,plain,(
% 2.18/0.66    spl2_24),
% 2.18/0.66    inference(avatar_split_clause,[],[f82,f213])).
% 2.18/0.66  fof(f82,plain,(
% 2.18/0.66    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f43])).
% 2.18/0.66  fof(f43,plain,(
% 2.18/0.66    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.66    inference(ennf_transformation,[],[f16])).
% 2.18/0.66  fof(f16,axiom,(
% 2.18/0.66    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.18/0.66  fof(f209,plain,(
% 2.18/0.66    spl2_23),
% 2.18/0.66    inference(avatar_split_clause,[],[f78,f207])).
% 2.18/0.66  fof(f78,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f40])).
% 2.18/0.66  fof(f40,plain,(
% 2.18/0.66    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.66    inference(ennf_transformation,[],[f14])).
% 2.18/0.66  fof(f14,axiom,(
% 2.18/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.18/0.66  fof(f205,plain,(
% 2.18/0.66    spl2_22),
% 2.18/0.66    inference(avatar_split_clause,[],[f77,f203])).
% 2.18/0.66  fof(f77,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f39])).
% 2.18/0.66  fof(f39,plain,(
% 2.18/0.66    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.66    inference(ennf_transformation,[],[f12])).
% 2.18/0.66  fof(f12,axiom,(
% 2.18/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.18/0.66  fof(f173,plain,(
% 2.18/0.66    spl2_19),
% 2.18/0.66    inference(avatar_split_clause,[],[f74,f171])).
% 2.18/0.66  fof(f74,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f2])).
% 2.18/0.66  fof(f2,axiom,(
% 2.18/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.18/0.66  fof(f169,plain,(
% 2.18/0.66    spl2_18),
% 2.18/0.66    inference(avatar_split_clause,[],[f73,f167])).
% 2.18/0.66  fof(f73,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f8])).
% 2.18/0.66  fof(f8,axiom,(
% 2.18/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.18/0.66  fof(f160,plain,(
% 2.18/0.66    spl2_16),
% 2.18/0.66    inference(avatar_split_clause,[],[f72,f158])).
% 2.18/0.66  fof(f72,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f9])).
% 2.18/0.66  fof(f9,axiom,(
% 2.18/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.18/0.66  fof(f150,plain,(
% 2.18/0.66    spl2_15),
% 2.18/0.66    inference(avatar_split_clause,[],[f75,f148])).
% 2.18/0.66  fof(f75,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f37])).
% 2.18/0.66  fof(f37,plain,(
% 2.18/0.66    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.18/0.66    inference(ennf_transformation,[],[f5])).
% 2.18/0.66  fof(f5,axiom,(
% 2.18/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.18/0.66  fof(f146,plain,(
% 2.18/0.66    spl2_14),
% 2.18/0.66    inference(avatar_split_clause,[],[f71,f144])).
% 2.18/0.66  fof(f71,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f11])).
% 2.18/0.66  fof(f11,axiom,(
% 2.18/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.18/0.66  fof(f138,plain,(
% 2.18/0.66    spl2_12),
% 2.18/0.66    inference(avatar_split_clause,[],[f81,f136])).
% 2.18/0.66  fof(f81,plain,(
% 2.18/0.66    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f53])).
% 2.18/0.66  fof(f53,plain,(
% 2.18/0.66    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.18/0.66    inference(nnf_transformation,[],[f18])).
% 2.18/0.66  fof(f18,axiom,(
% 2.18/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.18/0.66  fof(f130,plain,(
% 2.18/0.66    spl2_10),
% 2.18/0.66    inference(avatar_split_clause,[],[f69,f128])).
% 2.18/0.66  fof(f69,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f10])).
% 2.18/0.66  fof(f10,axiom,(
% 2.18/0.66    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.18/0.66  fof(f126,plain,(
% 2.18/0.66    spl2_9),
% 2.18/0.66    inference(avatar_split_clause,[],[f68,f124])).
% 2.18/0.66  fof(f68,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.18/0.66    inference(cnf_transformation,[],[f7])).
% 2.18/0.66  fof(f7,axiom,(
% 2.18/0.66    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.18/0.66  fof(f122,plain,(
% 2.18/0.66    spl2_8),
% 2.18/0.66    inference(avatar_split_clause,[],[f67,f120])).
% 2.18/0.66  fof(f67,plain,(
% 2.18/0.66    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f6])).
% 2.18/0.66  fof(f6,axiom,(
% 2.18/0.66    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.18/0.66  fof(f118,plain,(
% 2.18/0.66    spl2_7),
% 2.18/0.66    inference(avatar_split_clause,[],[f66,f116])).
% 2.18/0.66  fof(f66,plain,(
% 2.18/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.18/0.66    inference(cnf_transformation,[],[f27])).
% 2.18/0.66  fof(f27,plain,(
% 2.18/0.66    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.18/0.66    inference(rectify,[],[f1])).
% 2.18/0.66  fof(f1,axiom,(
% 2.18/0.66    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.18/0.66  fof(f114,plain,(
% 2.18/0.66    spl2_6),
% 2.18/0.66    inference(avatar_split_clause,[],[f59,f112])).
% 2.18/0.66  fof(f59,plain,(
% 2.18/0.66    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.18/0.66    inference(cnf_transformation,[],[f3])).
% 2.18/0.66  fof(f3,axiom,(
% 2.18/0.66    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.18/0.66  fof(f110,plain,(
% 2.18/0.66    ~spl2_4 | ~spl2_5),
% 2.18/0.66    inference(avatar_split_clause,[],[f109,f105,f101])).
% 2.18/0.66  fof(f109,plain,(
% 2.18/0.66    ~v4_pre_topc(sK1,sK0) | ~spl2_5),
% 2.18/0.66    inference(subsumption_resolution,[],[f58,f107])).
% 2.18/0.66  fof(f58,plain,(
% 2.18/0.66    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.18/0.66    inference(cnf_transformation,[],[f52])).
% 2.18/0.66  fof(f52,plain,(
% 2.18/0.66    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.18/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).
% 2.18/0.66  fof(f50,plain,(
% 2.18/0.66    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.18/0.66    introduced(choice_axiom,[])).
% 2.18/0.66  fof(f51,plain,(
% 2.18/0.66    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.18/0.66    introduced(choice_axiom,[])).
% 2.18/0.66  fof(f49,plain,(
% 2.18/0.66    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.18/0.66    inference(flattening,[],[f48])).
% 2.18/0.66  fof(f48,plain,(
% 2.18/0.66    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.18/0.66    inference(nnf_transformation,[],[f29])).
% 2.18/0.66  fof(f29,plain,(
% 2.18/0.66    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.18/0.66    inference(flattening,[],[f28])).
% 2.18/0.66  fof(f28,plain,(
% 2.18/0.66    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.18/0.66    inference(ennf_transformation,[],[f26])).
% 2.18/0.66  fof(f26,negated_conjecture,(
% 2.18/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.18/0.66    inference(negated_conjecture,[],[f25])).
% 2.18/0.66  fof(f25,conjecture,(
% 2.18/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.18/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 2.18/0.66  fof(f108,plain,(
% 2.18/0.66    spl2_4 | spl2_5),
% 2.18/0.66    inference(avatar_split_clause,[],[f57,f105,f101])).
% 2.18/0.66  fof(f57,plain,(
% 2.18/0.66    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.18/0.66    inference(cnf_transformation,[],[f52])).
% 2.18/0.67  fof(f99,plain,(
% 2.18/0.67    spl2_3),
% 2.18/0.67    inference(avatar_split_clause,[],[f56,f96])).
% 2.18/0.67  fof(f56,plain,(
% 2.18/0.67    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.18/0.67    inference(cnf_transformation,[],[f52])).
% 2.18/0.67  fof(f94,plain,(
% 2.18/0.67    spl2_2),
% 2.18/0.67    inference(avatar_split_clause,[],[f55,f91])).
% 2.18/0.67  fof(f55,plain,(
% 2.18/0.67    l1_pre_topc(sK0)),
% 2.18/0.67    inference(cnf_transformation,[],[f52])).
% 2.18/0.67  fof(f89,plain,(
% 2.18/0.67    spl2_1),
% 2.18/0.67    inference(avatar_split_clause,[],[f54,f86])).
% 2.18/0.67  fof(f54,plain,(
% 2.18/0.67    v2_pre_topc(sK0)),
% 2.18/0.67    inference(cnf_transformation,[],[f52])).
% 2.18/0.67  % SZS output end Proof for theBenchmark
% 2.18/0.67  % (32751)------------------------------
% 2.18/0.67  % (32751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.67  % (32751)Termination reason: Refutation
% 2.18/0.67  
% 2.18/0.67  % (32751)Memory used [KB]: 8955
% 2.18/0.67  % (32751)Time elapsed: 0.246 s
% 2.18/0.67  % (32751)------------------------------
% 2.18/0.67  % (32751)------------------------------
% 2.18/0.67  % (32745)Success in time 0.314 s
%------------------------------------------------------------------------------
