%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 218 expanded)
%              Number of leaves         :   39 ( 103 expanded)
%              Depth                    :    8
%              Number of atoms          :  349 ( 579 expanded)
%              Number of equality atoms :   28 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f627,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f62,f66,f71,f75,f79,f83,f102,f106,f110,f114,f118,f130,f138,f157,f223,f236,f357,f365,f372,f475,f477,f511,f626])).

fof(f626,plain,
    ( ~ spl3_5
    | ~ spl3_11
    | ~ spl3_13
    | spl3_45 ),
    inference(avatar_contradiction_clause,[],[f625])).

fof(f625,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_13
    | spl3_45 ),
    inference(subsumption_resolution,[],[f101,f611])).

fof(f611,plain,
    ( ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5
    | ~ spl3_13
    | spl3_45 ),
    inference(unit_resulting_resolution,[],[f65,f510,f109])).

fof(f109,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f510,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_45 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl3_45
  <=> r1_tarski(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f65,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f101,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_11
  <=> r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f511,plain,
    ( ~ spl3_45
    | ~ spl3_9
    | spl3_38 ),
    inference(avatar_split_clause,[],[f366,f362,f81,f508])).

fof(f81,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f362,plain,
    ( spl3_38
  <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f366,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9
    | spl3_38 ),
    inference(unit_resulting_resolution,[],[f364,f82])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f81])).

fof(f364,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f362])).

fof(f477,plain,
    ( ~ spl3_7
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_15
    | spl3_39
    | ~ spl3_44 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_15
    | spl3_39
    | ~ spl3_44 ),
    inference(subsumption_resolution,[],[f382,f474])).

fof(f474,plain,
    ( ! [X4,X5] : r1_tarski(k3_tarski(X4),k3_tarski(k2_xboole_0(X4,X5)))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f473])).

fof(f473,plain,
    ( spl3_44
  <=> ! [X5,X4] : r1_tarski(k3_tarski(X4),k3_tarski(k2_xboole_0(X4,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f382,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK1,sK2)))
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_15
    | spl3_39 ),
    inference(forward_demodulation,[],[f381,f74])).

fof(f74,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_7
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f381,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1)))
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_15
    | spl3_39 ),
    inference(forward_demodulation,[],[f380,f105])).

fof(f105,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl3_12
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f380,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | ~ spl3_14
    | ~ spl3_15
    | spl3_39 ),
    inference(forward_demodulation,[],[f373,f113])).

fof(f113,plain,
    ( ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl3_14
  <=> ! [X1,X0] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f373,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2))))
    | ~ spl3_15
    | spl3_39 ),
    inference(unit_resulting_resolution,[],[f371,f117])).

fof(f117,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | r1_tarski(k4_xboole_0(X0,X1),X2) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f371,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))
    | spl3_39 ),
    inference(avatar_component_clause,[],[f369])).

fof(f369,plain,
    ( spl3_39
  <=> r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f475,plain,
    ( spl3_44
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f145,f112,f60,f473])).

fof(f60,plain,
    ( spl3_4
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f145,plain,
    ( ! [X4,X5] : r1_tarski(k3_tarski(X4),k3_tarski(k2_xboole_0(X4,X5)))
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(superposition,[],[f61,f113])).

fof(f61,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f372,plain,
    ( ~ spl3_39
    | ~ spl3_18
    | ~ spl3_23
    | ~ spl3_25
    | spl3_37 ),
    inference(avatar_split_clause,[],[f359,f354,f234,f220,f155,f369])).

fof(f155,plain,
    ( spl3_18
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f220,plain,
    ( spl3_23
  <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f234,plain,
    ( spl3_25
  <=> ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f354,plain,
    ( spl3_37
  <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f359,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))
    | ~ spl3_18
    | ~ spl3_23
    | ~ spl3_25
    | spl3_37 ),
    inference(forward_demodulation,[],[f358,f225])).

fof(f225,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X0) = k4_xboole_0(k3_tarski(sK1),X0)
    | ~ spl3_18
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f222,f156])).

fof(f156,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f155])).

fof(f222,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f220])).

fof(f358,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))
    | ~ spl3_25
    | spl3_37 ),
    inference(forward_demodulation,[],[f356,f235])).

fof(f235,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f234])).

fof(f356,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | spl3_37 ),
    inference(avatar_component_clause,[],[f354])).

fof(f365,plain,
    ( ~ spl3_38
    | ~ spl3_25
    | spl3_36 ),
    inference(avatar_split_clause,[],[f360,f350,f234,f362])).

fof(f350,plain,
    ( spl3_36
  <=> m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f360,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_25
    | spl3_36 ),
    inference(forward_demodulation,[],[f352,f235])).

fof(f352,plain,
    ( ~ m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_36 ),
    inference(avatar_component_clause,[],[f350])).

fof(f357,plain,
    ( ~ spl3_36
    | ~ spl3_37
    | ~ spl3_2
    | ~ spl3_3
    | spl3_6
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f166,f128,f68,f55,f50,f354,f350])).

fof(f50,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f55,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f68,plain,
    ( spl3_6
  <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f128,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( k3_tarski(X1) = k5_setfam_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f166,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | ~ m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_6
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f165,f158])).

fof(f158,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f52,f129])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( k3_tarski(X1) = k5_setfam_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f128])).

fof(f52,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f165,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | ~ m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3
    | spl3_6
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f162,f159])).

fof(f159,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2)
    | ~ spl3_3
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f57,f129])).

fof(f57,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f162,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | ~ m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_6
    | ~ spl3_16 ),
    inference(superposition,[],[f70,f129])).

fof(f70,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f236,plain,
    ( spl3_25
    | ~ spl3_2
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f174,f155,f50,f234])).

fof(f174,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0)
    | ~ spl3_2
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f52,f156])).

fof(f223,plain,
    ( spl3_23
    | ~ spl3_2
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f173,f136,f128,f50,f220])).

fof(f136,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f173,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f167,f158])).

fof(f167,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f52,f137])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f136])).

fof(f157,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f41,f155])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f138,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f38,f136])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f130,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f37,f128])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f118,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f42,f116])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f114,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f36,f112])).

fof(f36,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f110,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f43,f108])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f106,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f35,f104])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f102,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f91,f77,f50,f99])).

fof(f77,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f91,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f52,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f83,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f40,f81])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f79,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f39,f77])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f33,f73])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f71,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f30,f68])).

fof(f30,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tops_2)).

fof(f66,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f32,f64])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f62,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f31,f60])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f58,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f29,f55])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f28,f50])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:58:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (11830)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (11818)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (11825)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (11814)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (11816)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (11813)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (11828)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (11823)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (11829)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (11822)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (11818)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f627,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f53,f58,f62,f66,f71,f75,f79,f83,f102,f106,f110,f114,f118,f130,f138,f157,f223,f236,f357,f365,f372,f475,f477,f511,f626])).
% 0.22/0.50  fof(f626,plain,(
% 0.22/0.50    ~spl3_5 | ~spl3_11 | ~spl3_13 | spl3_45),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f625])).
% 0.22/0.50  fof(f625,plain,(
% 0.22/0.50    $false | (~spl3_5 | ~spl3_11 | ~spl3_13 | spl3_45)),
% 0.22/0.50    inference(subsumption_resolution,[],[f101,f611])).
% 0.22/0.50  fof(f611,plain,(
% 0.22/0.50    ~r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_5 | ~spl3_13 | spl3_45)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f65,f510,f109])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f108])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    spl3_13 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.50  fof(f510,plain,(
% 0.22/0.50    ~r1_tarski(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_45),
% 0.22/0.50    inference(avatar_component_clause,[],[f508])).
% 0.22/0.50  fof(f508,plain,(
% 0.22/0.50    spl3_45 <=> r1_tarski(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    spl3_5 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f99])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl3_11 <=> r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.50  fof(f511,plain,(
% 0.22/0.50    ~spl3_45 | ~spl3_9 | spl3_38),
% 0.22/0.50    inference(avatar_split_clause,[],[f366,f362,f81,f508])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    spl3_9 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f362,plain,(
% 0.22/0.50    spl3_38 <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.22/0.50  fof(f366,plain,(
% 0.22/0.50    ~r1_tarski(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_9 | spl3_38)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f364,f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f81])).
% 0.22/0.50  fof(f364,plain,(
% 0.22/0.50    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_38),
% 0.22/0.50    inference(avatar_component_clause,[],[f362])).
% 0.22/0.50  fof(f477,plain,(
% 0.22/0.50    ~spl3_7 | ~spl3_12 | ~spl3_14 | ~spl3_15 | spl3_39 | ~spl3_44),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f476])).
% 0.22/0.50  fof(f476,plain,(
% 0.22/0.50    $false | (~spl3_7 | ~spl3_12 | ~spl3_14 | ~spl3_15 | spl3_39 | ~spl3_44)),
% 0.22/0.50    inference(subsumption_resolution,[],[f382,f474])).
% 0.22/0.50  fof(f474,plain,(
% 0.22/0.50    ( ! [X4,X5] : (r1_tarski(k3_tarski(X4),k3_tarski(k2_xboole_0(X4,X5)))) ) | ~spl3_44),
% 0.22/0.50    inference(avatar_component_clause,[],[f473])).
% 0.22/0.50  fof(f473,plain,(
% 0.22/0.50    spl3_44 <=> ! [X5,X4] : r1_tarski(k3_tarski(X4),k3_tarski(k2_xboole_0(X4,X5)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.22/0.50  fof(f382,plain,(
% 0.22/0.50    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK1,sK2))) | (~spl3_7 | ~spl3_12 | ~spl3_14 | ~spl3_15 | spl3_39)),
% 0.22/0.50    inference(forward_demodulation,[],[f381,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl3_7 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f381,plain,(
% 0.22/0.50    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1))) | (~spl3_12 | ~spl3_14 | ~spl3_15 | spl3_39)),
% 0.22/0.50    inference(forward_demodulation,[],[f380,f105])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl3_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f104])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    spl3_12 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.50  fof(f380,plain,(
% 0.22/0.50    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | (~spl3_14 | ~spl3_15 | spl3_39)),
% 0.22/0.50    inference(forward_demodulation,[],[f373,f113])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) ) | ~spl3_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f112])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    spl3_14 <=> ! [X1,X0] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.50  fof(f373,plain,(
% 0.22/0.50    ~r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2)))) | (~spl3_15 | spl3_39)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f371,f117])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) ) | ~spl3_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f116])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    spl3_15 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.50  fof(f371,plain,(
% 0.22/0.50    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) | spl3_39),
% 0.22/0.50    inference(avatar_component_clause,[],[f369])).
% 0.22/0.50  fof(f369,plain,(
% 0.22/0.50    spl3_39 <=> r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.22/0.50  fof(f475,plain,(
% 0.22/0.50    spl3_44 | ~spl3_4 | ~spl3_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f145,f112,f60,f473])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl3_4 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    ( ! [X4,X5] : (r1_tarski(k3_tarski(X4),k3_tarski(k2_xboole_0(X4,X5)))) ) | (~spl3_4 | ~spl3_14)),
% 0.22/0.50    inference(superposition,[],[f61,f113])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f60])).
% 0.22/0.50  fof(f372,plain,(
% 0.22/0.50    ~spl3_39 | ~spl3_18 | ~spl3_23 | ~spl3_25 | spl3_37),
% 0.22/0.50    inference(avatar_split_clause,[],[f359,f354,f234,f220,f155,f369])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    spl3_18 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.50  fof(f220,plain,(
% 0.22/0.50    spl3_23 <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    spl3_25 <=> ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.50  fof(f354,plain,(
% 0.22/0.50    spl3_37 <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.22/0.50  fof(f359,plain,(
% 0.22/0.50    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) | (~spl3_18 | ~spl3_23 | ~spl3_25 | spl3_37)),
% 0.22/0.50    inference(forward_demodulation,[],[f358,f225])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X0) = k4_xboole_0(k3_tarski(sK1),X0)) ) | (~spl3_18 | ~spl3_23)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f222,f156])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f155])).
% 0.22/0.50  fof(f222,plain,(
% 0.22/0.50    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f220])).
% 0.22/0.50  fof(f358,plain,(
% 0.22/0.50    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) | (~spl3_25 | spl3_37)),
% 0.22/0.50    inference(forward_demodulation,[],[f356,f235])).
% 0.22/0.50  fof(f235,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0)) ) | ~spl3_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f234])).
% 0.22/0.50  fof(f356,plain,(
% 0.22/0.50    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) | spl3_37),
% 0.22/0.50    inference(avatar_component_clause,[],[f354])).
% 0.22/0.50  fof(f365,plain,(
% 0.22/0.50    ~spl3_38 | ~spl3_25 | spl3_36),
% 0.22/0.50    inference(avatar_split_clause,[],[f360,f350,f234,f362])).
% 0.22/0.50  fof(f350,plain,(
% 0.22/0.50    spl3_36 <=> m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.50  fof(f360,plain,(
% 0.22/0.50    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl3_25 | spl3_36)),
% 0.22/0.50    inference(forward_demodulation,[],[f352,f235])).
% 0.22/0.50  fof(f352,plain,(
% 0.22/0.50    ~m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_36),
% 0.22/0.50    inference(avatar_component_clause,[],[f350])).
% 0.22/0.50  fof(f357,plain,(
% 0.22/0.50    ~spl3_36 | ~spl3_37 | ~spl3_2 | ~spl3_3 | spl3_6 | ~spl3_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f166,f128,f68,f55,f50,f354,f350])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl3_6 <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    spl3_16 <=> ! [X1,X0] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) | ~m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl3_2 | ~spl3_3 | spl3_6 | ~spl3_16)),
% 0.22/0.50    inference(forward_demodulation,[],[f165,f158])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) | (~spl3_2 | ~spl3_16)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f52,f129])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f128])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f50])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) | ~m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl3_3 | spl3_6 | ~spl3_16)),
% 0.22/0.50    inference(forward_demodulation,[],[f162,f159])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) | (~spl3_3 | ~spl3_16)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f57,f129])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f55])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k3_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) | ~m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (spl3_6 | ~spl3_16)),
% 0.22/0.50    inference(superposition,[],[f70,f129])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) | spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f68])).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    spl3_25 | ~spl3_2 | ~spl3_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f174,f155,f50,f234])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0)) ) | (~spl3_2 | ~spl3_18)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f52,f156])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    spl3_23 | ~spl3_2 | ~spl3_16 | ~spl3_17),
% 0.22/0.50    inference(avatar_split_clause,[],[f173,f136,f128,f50,f220])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    spl3_17 <=> ! [X1,X0] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_16 | ~spl3_17)),
% 0.22/0.50    inference(forward_demodulation,[],[f167,f158])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_17)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f52,f137])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f136])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    spl3_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f41,f155])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    spl3_17),
% 0.22/0.50    inference(avatar_split_clause,[],[f38,f136])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    spl3_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f128])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    spl3_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f42,f116])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    spl3_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f36,f112])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    spl3_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f43,f108])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f35,f104])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    spl3_11 | ~spl3_2 | ~spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f91,f77,f50,f99])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    spl3_8 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_8)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f52,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl3_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f77])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f40,f81])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f39,f77])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f33,f73])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ~spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f68])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ((~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24,f23,f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f13])).
% 0.22/0.50  fof(f13,conjecture,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tops_2)).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f32,f64])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f31,f60])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f29,f55])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f50])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (11818)------------------------------
% 0.22/0.50  % (11818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (11818)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (11818)Memory used [KB]: 6524
% 0.22/0.50  % (11818)Time elapsed: 0.064 s
% 0.22/0.50  % (11818)------------------------------
% 0.22/0.50  % (11818)------------------------------
% 0.22/0.50  % (11810)Success in time 0.137 s
%------------------------------------------------------------------------------
