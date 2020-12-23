%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:48 EST 2020

% Result     : Theorem 3.07s
% Output     : Refutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 366 expanded)
%              Number of leaves         :   52 ( 167 expanded)
%              Depth                    :   10
%              Number of atoms          :  652 (1234 expanded)
%              Number of equality atoms :   96 ( 213 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (14424)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
fof(f1785,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f90,f95,f99,f108,f110,f114,f122,f126,f135,f139,f159,f167,f171,f204,f215,f232,f236,f246,f258,f268,f272,f305,f360,f374,f378,f383,f424,f447,f546,f784,f1084,f1154,f1384,f1389,f1763,f1781,f1784])).

% (14424)Refutation not found, incomplete strategy% (14424)------------------------------
% (14424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f1784,plain,
    ( ~ spl2_13
    | ~ spl2_91
    | spl2_92 ),
    inference(avatar_contradiction_clause,[],[f1783])).

fof(f1783,plain,
    ( $false
    | ~ spl2_13
    | ~ spl2_91
    | spl2_92 ),
    inference(subsumption_resolution,[],[f1151,f1157])).

fof(f1157,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_92 ),
    inference(avatar_component_clause,[],[f1156])).

fof(f1156,plain,
    ( spl2_92
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).

fof(f1151,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_13
    | ~ spl2_91 ),
    inference(unit_resulting_resolution,[],[f1083,f138])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f1083,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_91 ),
    inference(avatar_component_clause,[],[f1081])).

fof(f1081,plain,
    ( spl2_91
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_91])])).

fof(f1781,plain,
    ( ~ spl2_13
    | ~ spl2_43
    | ~ spl2_91
    | spl2_135 ),
    inference(avatar_contradiction_clause,[],[f1780])).

fof(f1780,plain,
    ( $false
    | ~ spl2_13
    | ~ spl2_43
    | ~ spl2_91
    | spl2_135 ),
    inference(subsumption_resolution,[],[f1142,f1764])).

fof(f1764,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_13
    | spl2_135 ),
    inference(unit_resulting_resolution,[],[f1762,f138])).

fof(f1762,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_135 ),
    inference(avatar_component_clause,[],[f1760])).

fof(f1760,plain,
    ( spl2_135
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_135])])).

fof(f1142,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_43
    | ~ spl2_91 ),
    inference(unit_resulting_resolution,[],[f1083,f377])).

fof(f377,plain,
    ( ! [X5] :
        ( r1_tarski(X5,u1_struct_0(sK0))
        | ~ r1_tarski(X5,sK1) )
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl2_43
  <=> ! [X5] :
        ( r1_tarski(X5,u1_struct_0(sK0))
        | ~ r1_tarski(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f1763,plain,
    ( ~ spl2_3
    | ~ spl2_135
    | ~ spl2_7
    | ~ spl2_10
    | ~ spl2_18
    | ~ spl2_27
    | ~ spl2_40
    | ~ spl2_49
    | ~ spl2_50
    | ~ spl2_56
    | ~ spl2_79
    | ~ spl2_92
    | spl2_109 ),
    inference(avatar_split_clause,[],[f1391,f1371,f1156,f782,f544,f445,f422,f357,f244,f165,f124,f112,f1760,f92])).

fof(f92,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f112,plain,
    ( spl2_7
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f124,plain,
    ( spl2_10
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f165,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f244,plain,
    ( spl2_27
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f357,plain,
    ( spl2_40
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f422,plain,
    ( spl2_49
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f445,plain,
    ( spl2_50
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f544,plain,
    ( spl2_56
  <=> ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f782,plain,
    ( spl2_79
  <=> ! [X3,X2,X4] :
        ( k4_subset_1(X2,k3_subset_1(X2,X3),X4) = k3_subset_1(X2,k4_xboole_0(X3,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_79])])).

fof(f1371,plain,
    ( spl2_109
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_109])])).

fof(f1391,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_7
    | ~ spl2_10
    | ~ spl2_18
    | ~ spl2_27
    | ~ spl2_40
    | ~ spl2_49
    | ~ spl2_50
    | ~ spl2_56
    | ~ spl2_79
    | ~ spl2_92
    | spl2_109 ),
    inference(subsumption_resolution,[],[f1386,f1372])).

fof(f1372,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_109 ),
    inference(avatar_component_clause,[],[f1371])).

fof(f1386,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_7
    | ~ spl2_10
    | ~ spl2_18
    | ~ spl2_27
    | ~ spl2_40
    | ~ spl2_49
    | ~ spl2_50
    | ~ spl2_56
    | ~ spl2_79
    | ~ spl2_92 ),
    inference(forward_demodulation,[],[f361,f1211])).

fof(f1211,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_7
    | ~ spl2_10
    | ~ spl2_18
    | ~ spl2_27
    | ~ spl2_49
    | ~ spl2_50
    | ~ spl2_56
    | ~ spl2_79
    | ~ spl2_92 ),
    inference(forward_demodulation,[],[f1168,f1193])).

fof(f1193,plain,
    ( sK1 = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_7
    | ~ spl2_10
    | ~ spl2_18
    | ~ spl2_49
    | ~ spl2_56
    | ~ spl2_79
    | ~ spl2_92 ),
    inference(forward_demodulation,[],[f1192,f545])).

fof(f545,plain,
    ( ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f544])).

fof(f1192,plain,
    ( k3_subset_1(sK1,k1_xboole_0) = k4_subset_1(sK1,k3_subset_1(sK1,k1_xboole_0),k2_tops_1(sK0,sK1))
    | ~ spl2_7
    | ~ spl2_10
    | ~ spl2_18
    | ~ spl2_49
    | ~ spl2_79
    | ~ spl2_92 ),
    inference(forward_demodulation,[],[f1183,f437])).

fof(f437,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_10
    | ~ spl2_18
    | ~ spl2_49 ),
    inference(unit_resulting_resolution,[],[f125,f423,f166])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f165])).

fof(f423,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f422])).

fof(f125,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f1183,plain,
    ( k4_subset_1(sK1,k3_subset_1(sK1,k1_xboole_0),k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k4_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1)))
    | ~ spl2_7
    | ~ spl2_79
    | ~ spl2_92 ),
    inference(unit_resulting_resolution,[],[f113,f1158,f783])).

fof(f783,plain,
    ( ! [X4,X2,X3] :
        ( k4_subset_1(X2,k3_subset_1(X2,X3),X4) = k3_subset_1(X2,k4_xboole_0(X3,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) )
    | ~ spl2_79 ),
    inference(avatar_component_clause,[],[f782])).

fof(f1158,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_92 ),
    inference(avatar_component_clause,[],[f1156])).

fof(f113,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f1168,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_27
    | ~ spl2_50
    | ~ spl2_92 ),
    inference(unit_resulting_resolution,[],[f446,f1158,f245])).

fof(f245,plain,
    ( ! [X2,X0,X1] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f244])).

fof(f446,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f445])).

fof(f361,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_27
    | ~ spl2_40 ),
    inference(superposition,[],[f359,f245])).

fof(f359,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f357])).

fof(f1389,plain,
    ( spl2_6
    | ~ spl2_44
    | ~ spl2_109 ),
    inference(avatar_contradiction_clause,[],[f1388])).

fof(f1388,plain,
    ( $false
    | spl2_6
    | ~ spl2_44
    | ~ spl2_109 ),
    inference(subsumption_resolution,[],[f1375,f106])).

fof(f106,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f1375,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_44
    | ~ spl2_109 ),
    inference(superposition,[],[f382,f1373])).

fof(f1373,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_109 ),
    inference(avatar_component_clause,[],[f1371])).

fof(f382,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f380])).

fof(f380,plain,
    ( spl2_44
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f1384,plain,
    ( spl2_5
    | ~ spl2_31
    | ~ spl2_109 ),
    inference(avatar_contradiction_clause,[],[f1383])).

fof(f1383,plain,
    ( $false
    | spl2_5
    | ~ spl2_31
    | ~ spl2_109 ),
    inference(subsumption_resolution,[],[f102,f1376])).

fof(f1376,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_31
    | ~ spl2_109 ),
    inference(superposition,[],[f304,f1373])).

fof(f304,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl2_31
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f102,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl2_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1154,plain,
    ( ~ spl2_2
    | spl2_91
    | ~ spl2_5
    | ~ spl2_3
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f250,f234,f92,f101,f1081,f87])).

fof(f87,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f234,plain,
    ( spl2_26
  <=> ! [X1,X0] :
        ( r1_tarski(k2_tops_1(X0,X1),X1)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f250,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_26 ),
    inference(resolution,[],[f235,f94])).

fof(f94,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | r1_tarski(k2_tops_1(X0,X1),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f234])).

fof(f1084,plain,
    ( spl2_91
    | ~ spl2_10
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f1078,f371,f124,f1081])).

fof(f371,plain,
    ( spl2_42
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f1078,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_10
    | ~ spl2_42 ),
    inference(superposition,[],[f125,f373])).

fof(f373,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f371])).

fof(f784,plain,
    ( spl2_79
    | ~ spl2_23
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f287,f270,f213,f782])).

fof(f213,plain,
    ( spl2_23
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f270,plain,
    ( spl2_30
  <=> ! [X1,X0,X2] :
        ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f287,plain,
    ( ! [X4,X2,X3] :
        ( k4_subset_1(X2,k3_subset_1(X2,X3),X4) = k3_subset_1(X2,k4_xboole_0(X3,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) )
    | ~ spl2_23
    | ~ spl2_30 ),
    inference(duplicate_literal_removal,[],[f283])).

fof(f283,plain,
    ( ! [X4,X2,X3] :
        ( k4_subset_1(X2,k3_subset_1(X2,X3),X4) = k3_subset_1(X2,k4_xboole_0(X3,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) )
    | ~ spl2_23
    | ~ spl2_30 ),
    inference(superposition,[],[f271,f214])).

fof(f214,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f213])).

fof(f271,plain,
    ( ! [X2,X0,X1] :
        ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f270])).

fof(f546,plain,
    ( spl2_56
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f220,f202,f120,f112,f544])).

fof(f120,plain,
    ( spl2_9
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f202,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f220,plain,
    ( ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f217,f121])).

fof(f121,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f217,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)
    | ~ spl2_7
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f113,f203])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f202])).

fof(f447,plain,
    ( spl2_50
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f152,f137,f97,f445])).

fof(f97,plain,
    ( spl2_4
  <=> ! [X1] : r1_tarski(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f152,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(unit_resulting_resolution,[],[f98,f138])).

fof(f98,plain,
    ( ! [X1] : r1_tarski(X1,X1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f424,plain,
    ( spl2_49
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f149,f133,f112,f422])).

fof(f133,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f149,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f113,f134])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f383,plain,
    ( spl2_44
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f273,f266,f92,f87,f380])).

fof(f266,plain,
    ( spl2_29
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f273,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_29 ),
    inference(unit_resulting_resolution,[],[f89,f94,f267])).

fof(f267,plain,
    ( ! [X0,X1] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f266])).

fof(f89,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f378,plain,
    ( spl2_43
    | ~ spl2_16
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f200,f169,f156,f376])).

fof(f156,plain,
    ( spl2_16
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f169,plain,
    ( spl2_19
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f200,plain,
    ( ! [X5] :
        ( r1_tarski(X5,u1_struct_0(sK0))
        | ~ r1_tarski(X5,sK1) )
    | ~ spl2_16
    | ~ spl2_19 ),
    inference(resolution,[],[f170,f158])).

fof(f158,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f170,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f169])).

fof(f374,plain,
    ( ~ spl2_3
    | spl2_42
    | ~ spl2_6
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f223,f213,f105,f371,f92])).

fof(f223,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6
    | ~ spl2_23 ),
    inference(superposition,[],[f214,f107])).

fof(f107,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f360,plain,
    ( spl2_40
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f259,f256,f92,f87,f357])).

fof(f256,plain,
    ( spl2_28
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f259,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(unit_resulting_resolution,[],[f89,f94,f257])).

fof(f257,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f256])).

fof(f305,plain,
    ( spl2_31
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f237,f230,f92,f87,f82,f302])).

fof(f82,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f230,plain,
    ( spl2_25
  <=> ! [X1,X0] :
        ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f237,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_25 ),
    inference(unit_resulting_resolution,[],[f84,f89,f94,f231])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(k2_pre_topc(X0,X1),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f230])).

fof(f84,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f272,plain,(
    spl2_30 ),
    inference(avatar_split_clause,[],[f68,f270])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

fof(f268,plain,(
    spl2_29 ),
    inference(avatar_split_clause,[],[f59,f266])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f258,plain,(
    spl2_28 ),
    inference(avatar_split_clause,[],[f58,f256])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f246,plain,(
    spl2_27 ),
    inference(avatar_split_clause,[],[f78,f244])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f236,plain,(
    spl2_26 ),
    inference(avatar_split_clause,[],[f60,f234])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f232,plain,(
    spl2_25 ),
    inference(avatar_split_clause,[],[f69,f230])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f215,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f75,f213])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f204,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f67,f202])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f171,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f77,f169])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f167,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f72,f165])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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

fof(f159,plain,
    ( spl2_16
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f148,f133,f92,f156])).

fof(f148,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f94,f134])).

fof(f139,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f74,f137])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f135,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f73,f133])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f126,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f61,f124])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f122,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f57,f120])).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f114,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f55,f112])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f110,plain,
    ( ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f109,f105,f101])).

fof(f109,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f54,f107])).

fof(f54,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).

fof(f44,plain,
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

fof(f45,plain,
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

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f108,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f53,f105,f101])).

fof(f53,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f99,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f79,f97])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f95,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f52,f92])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f51,f87])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f50,f82])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:46:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (14400)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.48  % (14411)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.51  % (14392)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (14395)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (14396)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (14401)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (14402)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (14413)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (14405)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (14409)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (14410)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (14416)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (14420)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (14399)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (14397)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (14404)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (14403)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (14408)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (14414)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (14412)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (14418)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (14393)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (14394)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (14393)Refutation not found, incomplete strategy% (14393)------------------------------
% 0.20/0.53  % (14393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (14393)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (14393)Memory used [KB]: 1791
% 0.20/0.53  % (14393)Time elapsed: 0.130 s
% 0.20/0.53  % (14393)------------------------------
% 0.20/0.53  % (14393)------------------------------
% 0.20/0.54  % (14419)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (14417)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (14406)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.43/0.54  % (14407)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.43/0.55  % (14415)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.43/0.55  % (14421)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.43/0.55  % (14421)Refutation not found, incomplete strategy% (14421)------------------------------
% 1.43/0.55  % (14421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (14421)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (14421)Memory used [KB]: 1663
% 1.43/0.55  % (14421)Time elapsed: 0.141 s
% 1.43/0.55  % (14421)------------------------------
% 1.43/0.55  % (14421)------------------------------
% 1.43/0.55  % (14398)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.10/0.65  % (14395)Refutation not found, incomplete strategy% (14395)------------------------------
% 2.10/0.65  % (14395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.33/0.67  % (14395)Termination reason: Refutation not found, incomplete strategy
% 2.33/0.67  
% 2.33/0.67  % (14395)Memory used [KB]: 6140
% 2.33/0.67  % (14395)Time elapsed: 0.252 s
% 2.33/0.67  % (14395)------------------------------
% 2.33/0.67  % (14395)------------------------------
% 2.33/0.69  % (14422)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.33/0.71  % (14423)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.07/0.79  % (14422)Refutation found. Thanks to Tanya!
% 3.07/0.79  % SZS status Theorem for theBenchmark
% 3.07/0.79  % SZS output start Proof for theBenchmark
% 3.07/0.79  % (14424)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.07/0.80  fof(f1785,plain,(
% 3.07/0.80    $false),
% 3.07/0.80    inference(avatar_sat_refutation,[],[f85,f90,f95,f99,f108,f110,f114,f122,f126,f135,f139,f159,f167,f171,f204,f215,f232,f236,f246,f258,f268,f272,f305,f360,f374,f378,f383,f424,f447,f546,f784,f1084,f1154,f1384,f1389,f1763,f1781,f1784])).
% 3.07/0.80  % (14424)Refutation not found, incomplete strategy% (14424)------------------------------
% 3.07/0.80  % (14424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.80  fof(f1784,plain,(
% 3.07/0.80    ~spl2_13 | ~spl2_91 | spl2_92),
% 3.07/0.80    inference(avatar_contradiction_clause,[],[f1783])).
% 3.07/0.80  fof(f1783,plain,(
% 3.07/0.80    $false | (~spl2_13 | ~spl2_91 | spl2_92)),
% 3.07/0.80    inference(subsumption_resolution,[],[f1151,f1157])).
% 3.07/0.80  fof(f1157,plain,(
% 3.07/0.80    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_92),
% 3.07/0.80    inference(avatar_component_clause,[],[f1156])).
% 3.07/0.80  fof(f1156,plain,(
% 3.07/0.80    spl2_92 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).
% 3.07/0.80  fof(f1151,plain,(
% 3.07/0.80    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | (~spl2_13 | ~spl2_91)),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f1083,f138])).
% 3.07/0.80  fof(f138,plain,(
% 3.07/0.80    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_13),
% 3.07/0.80    inference(avatar_component_clause,[],[f137])).
% 3.07/0.80  fof(f137,plain,(
% 3.07/0.80    spl2_13 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 3.07/0.80  fof(f1083,plain,(
% 3.07/0.80    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_91),
% 3.07/0.80    inference(avatar_component_clause,[],[f1081])).
% 3.07/0.80  fof(f1081,plain,(
% 3.07/0.80    spl2_91 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_91])])).
% 3.07/0.80  fof(f1781,plain,(
% 3.07/0.80    ~spl2_13 | ~spl2_43 | ~spl2_91 | spl2_135),
% 3.07/0.80    inference(avatar_contradiction_clause,[],[f1780])).
% 3.07/0.80  fof(f1780,plain,(
% 3.07/0.80    $false | (~spl2_13 | ~spl2_43 | ~spl2_91 | spl2_135)),
% 3.07/0.80    inference(subsumption_resolution,[],[f1142,f1764])).
% 3.07/0.80  fof(f1764,plain,(
% 3.07/0.80    ~r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_13 | spl2_135)),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f1762,f138])).
% 3.07/0.80  fof(f1762,plain,(
% 3.07/0.80    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_135),
% 3.07/0.80    inference(avatar_component_clause,[],[f1760])).
% 3.07/0.80  fof(f1760,plain,(
% 3.07/0.80    spl2_135 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_135])])).
% 3.07/0.80  fof(f1142,plain,(
% 3.07/0.80    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_43 | ~spl2_91)),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f1083,f377])).
% 3.07/0.80  fof(f377,plain,(
% 3.07/0.80    ( ! [X5] : (r1_tarski(X5,u1_struct_0(sK0)) | ~r1_tarski(X5,sK1)) ) | ~spl2_43),
% 3.07/0.80    inference(avatar_component_clause,[],[f376])).
% 3.07/0.80  fof(f376,plain,(
% 3.07/0.80    spl2_43 <=> ! [X5] : (r1_tarski(X5,u1_struct_0(sK0)) | ~r1_tarski(X5,sK1))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 3.07/0.80  fof(f1763,plain,(
% 3.07/0.80    ~spl2_3 | ~spl2_135 | ~spl2_7 | ~spl2_10 | ~spl2_18 | ~spl2_27 | ~spl2_40 | ~spl2_49 | ~spl2_50 | ~spl2_56 | ~spl2_79 | ~spl2_92 | spl2_109),
% 3.07/0.80    inference(avatar_split_clause,[],[f1391,f1371,f1156,f782,f544,f445,f422,f357,f244,f165,f124,f112,f1760,f92])).
% 3.07/0.80  fof(f92,plain,(
% 3.07/0.80    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 3.07/0.80  fof(f112,plain,(
% 3.07/0.80    spl2_7 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 3.07/0.80  fof(f124,plain,(
% 3.07/0.80    spl2_10 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 3.07/0.80  fof(f165,plain,(
% 3.07/0.80    spl2_18 <=> ! [X1,X0] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 3.07/0.80  fof(f244,plain,(
% 3.07/0.80    spl2_27 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 3.07/0.80  fof(f357,plain,(
% 3.07/0.80    spl2_40 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 3.07/0.80  fof(f422,plain,(
% 3.07/0.80    spl2_49 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 3.07/0.80  fof(f445,plain,(
% 3.07/0.80    spl2_50 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 3.07/0.80  fof(f544,plain,(
% 3.07/0.80    spl2_56 <=> ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 3.07/0.80  fof(f782,plain,(
% 3.07/0.80    spl2_79 <=> ! [X3,X2,X4] : (k4_subset_1(X2,k3_subset_1(X2,X3),X4) = k3_subset_1(X2,k4_xboole_0(X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2)))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_79])])).
% 3.07/0.80  fof(f1371,plain,(
% 3.07/0.80    spl2_109 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_109])])).
% 3.07/0.80  fof(f1391,plain,(
% 3.07/0.80    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_7 | ~spl2_10 | ~spl2_18 | ~spl2_27 | ~spl2_40 | ~spl2_49 | ~spl2_50 | ~spl2_56 | ~spl2_79 | ~spl2_92 | spl2_109)),
% 3.07/0.80    inference(subsumption_resolution,[],[f1386,f1372])).
% 3.07/0.80  fof(f1372,plain,(
% 3.07/0.80    sK1 != k2_pre_topc(sK0,sK1) | spl2_109),
% 3.07/0.80    inference(avatar_component_clause,[],[f1371])).
% 3.07/0.80  fof(f1386,plain,(
% 3.07/0.80    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_7 | ~spl2_10 | ~spl2_18 | ~spl2_27 | ~spl2_40 | ~spl2_49 | ~spl2_50 | ~spl2_56 | ~spl2_79 | ~spl2_92)),
% 3.07/0.80    inference(forward_demodulation,[],[f361,f1211])).
% 3.07/0.80  fof(f1211,plain,(
% 3.07/0.80    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_7 | ~spl2_10 | ~spl2_18 | ~spl2_27 | ~spl2_49 | ~spl2_50 | ~spl2_56 | ~spl2_79 | ~spl2_92)),
% 3.07/0.80    inference(forward_demodulation,[],[f1168,f1193])).
% 3.07/0.80  fof(f1193,plain,(
% 3.07/0.80    sK1 = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | (~spl2_7 | ~spl2_10 | ~spl2_18 | ~spl2_49 | ~spl2_56 | ~spl2_79 | ~spl2_92)),
% 3.07/0.80    inference(forward_demodulation,[],[f1192,f545])).
% 3.07/0.80  fof(f545,plain,(
% 3.07/0.80    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) ) | ~spl2_56),
% 3.07/0.80    inference(avatar_component_clause,[],[f544])).
% 3.07/0.80  fof(f1192,plain,(
% 3.07/0.80    k3_subset_1(sK1,k1_xboole_0) = k4_subset_1(sK1,k3_subset_1(sK1,k1_xboole_0),k2_tops_1(sK0,sK1)) | (~spl2_7 | ~spl2_10 | ~spl2_18 | ~spl2_49 | ~spl2_79 | ~spl2_92)),
% 3.07/0.80    inference(forward_demodulation,[],[f1183,f437])).
% 3.07/0.80  fof(f437,plain,(
% 3.07/0.80    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl2_10 | ~spl2_18 | ~spl2_49)),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f125,f423,f166])).
% 3.07/0.80  fof(f166,plain,(
% 3.07/0.80    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) ) | ~spl2_18),
% 3.07/0.80    inference(avatar_component_clause,[],[f165])).
% 3.07/0.80  fof(f423,plain,(
% 3.07/0.80    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl2_49),
% 3.07/0.80    inference(avatar_component_clause,[],[f422])).
% 3.07/0.80  fof(f125,plain,(
% 3.07/0.80    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_10),
% 3.07/0.80    inference(avatar_component_clause,[],[f124])).
% 3.07/0.80  fof(f1183,plain,(
% 3.07/0.80    k4_subset_1(sK1,k3_subset_1(sK1,k1_xboole_0),k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k4_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1))) | (~spl2_7 | ~spl2_79 | ~spl2_92)),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f113,f1158,f783])).
% 3.07/0.80  fof(f783,plain,(
% 3.07/0.80    ( ! [X4,X2,X3] : (k4_subset_1(X2,k3_subset_1(X2,X3),X4) = k3_subset_1(X2,k4_xboole_0(X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) ) | ~spl2_79),
% 3.07/0.80    inference(avatar_component_clause,[],[f782])).
% 3.07/0.80  fof(f1158,plain,(
% 3.07/0.80    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_92),
% 3.07/0.80    inference(avatar_component_clause,[],[f1156])).
% 3.07/0.80  fof(f113,plain,(
% 3.07/0.80    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl2_7),
% 3.07/0.80    inference(avatar_component_clause,[],[f112])).
% 3.07/0.80  fof(f1168,plain,(
% 3.07/0.80    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | (~spl2_27 | ~spl2_50 | ~spl2_92)),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f446,f1158,f245])).
% 3.07/0.80  fof(f245,plain,(
% 3.07/0.80    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_27),
% 3.07/0.80    inference(avatar_component_clause,[],[f244])).
% 3.07/0.80  fof(f446,plain,(
% 3.07/0.80    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl2_50),
% 3.07/0.80    inference(avatar_component_clause,[],[f445])).
% 3.07/0.80  fof(f361,plain,(
% 3.07/0.80    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_27 | ~spl2_40)),
% 3.07/0.80    inference(superposition,[],[f359,f245])).
% 3.07/0.80  fof(f359,plain,(
% 3.07/0.80    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_40),
% 3.07/0.80    inference(avatar_component_clause,[],[f357])).
% 3.07/0.80  fof(f1389,plain,(
% 3.07/0.80    spl2_6 | ~spl2_44 | ~spl2_109),
% 3.07/0.80    inference(avatar_contradiction_clause,[],[f1388])).
% 3.07/0.80  fof(f1388,plain,(
% 3.07/0.80    $false | (spl2_6 | ~spl2_44 | ~spl2_109)),
% 3.07/0.80    inference(subsumption_resolution,[],[f1375,f106])).
% 3.07/0.80  fof(f106,plain,(
% 3.07/0.80    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_6),
% 3.07/0.80    inference(avatar_component_clause,[],[f105])).
% 3.07/0.80  fof(f105,plain,(
% 3.07/0.80    spl2_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 3.07/0.80  fof(f1375,plain,(
% 3.07/0.80    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_44 | ~spl2_109)),
% 3.07/0.80    inference(superposition,[],[f382,f1373])).
% 3.07/0.80  fof(f1373,plain,(
% 3.07/0.80    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_109),
% 3.07/0.80    inference(avatar_component_clause,[],[f1371])).
% 3.07/0.80  fof(f382,plain,(
% 3.07/0.80    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_44),
% 3.07/0.80    inference(avatar_component_clause,[],[f380])).
% 3.07/0.80  fof(f380,plain,(
% 3.07/0.80    spl2_44 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 3.07/0.80  fof(f1384,plain,(
% 3.07/0.80    spl2_5 | ~spl2_31 | ~spl2_109),
% 3.07/0.80    inference(avatar_contradiction_clause,[],[f1383])).
% 3.07/0.80  fof(f1383,plain,(
% 3.07/0.80    $false | (spl2_5 | ~spl2_31 | ~spl2_109)),
% 3.07/0.80    inference(subsumption_resolution,[],[f102,f1376])).
% 3.07/0.80  fof(f1376,plain,(
% 3.07/0.80    v4_pre_topc(sK1,sK0) | (~spl2_31 | ~spl2_109)),
% 3.07/0.80    inference(superposition,[],[f304,f1373])).
% 3.07/0.80  fof(f304,plain,(
% 3.07/0.80    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~spl2_31),
% 3.07/0.80    inference(avatar_component_clause,[],[f302])).
% 3.07/0.80  fof(f302,plain,(
% 3.07/0.80    spl2_31 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 3.07/0.80  fof(f102,plain,(
% 3.07/0.80    ~v4_pre_topc(sK1,sK0) | spl2_5),
% 3.07/0.80    inference(avatar_component_clause,[],[f101])).
% 3.07/0.80  fof(f101,plain,(
% 3.07/0.80    spl2_5 <=> v4_pre_topc(sK1,sK0)),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 3.07/0.80  fof(f1154,plain,(
% 3.07/0.80    ~spl2_2 | spl2_91 | ~spl2_5 | ~spl2_3 | ~spl2_26),
% 3.07/0.80    inference(avatar_split_clause,[],[f250,f234,f92,f101,f1081,f87])).
% 3.07/0.80  fof(f87,plain,(
% 3.07/0.80    spl2_2 <=> l1_pre_topc(sK0)),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.07/0.80  fof(f234,plain,(
% 3.07/0.80    spl2_26 <=> ! [X1,X0] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 3.07/0.80  fof(f250,plain,(
% 3.07/0.80    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_26)),
% 3.07/0.80    inference(resolution,[],[f235,f94])).
% 3.07/0.80  fof(f94,plain,(
% 3.07/0.80    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 3.07/0.80    inference(avatar_component_clause,[],[f92])).
% 3.07/0.80  fof(f235,plain,(
% 3.07/0.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) ) | ~spl2_26),
% 3.07/0.80    inference(avatar_component_clause,[],[f234])).
% 3.07/0.80  fof(f1084,plain,(
% 3.07/0.80    spl2_91 | ~spl2_10 | ~spl2_42),
% 3.07/0.80    inference(avatar_split_clause,[],[f1078,f371,f124,f1081])).
% 3.07/0.80  fof(f371,plain,(
% 3.07/0.80    spl2_42 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 3.07/0.80  fof(f1078,plain,(
% 3.07/0.80    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_10 | ~spl2_42)),
% 3.07/0.80    inference(superposition,[],[f125,f373])).
% 3.07/0.80  fof(f373,plain,(
% 3.07/0.80    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_42),
% 3.07/0.80    inference(avatar_component_clause,[],[f371])).
% 3.07/0.80  fof(f784,plain,(
% 3.07/0.80    spl2_79 | ~spl2_23 | ~spl2_30),
% 3.07/0.80    inference(avatar_split_clause,[],[f287,f270,f213,f782])).
% 3.07/0.80  fof(f213,plain,(
% 3.07/0.80    spl2_23 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 3.07/0.80  fof(f270,plain,(
% 3.07/0.80    spl2_30 <=> ! [X1,X0,X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 3.07/0.80  fof(f287,plain,(
% 3.07/0.80    ( ! [X4,X2,X3] : (k4_subset_1(X2,k3_subset_1(X2,X3),X4) = k3_subset_1(X2,k4_xboole_0(X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) ) | (~spl2_23 | ~spl2_30)),
% 3.07/0.80    inference(duplicate_literal_removal,[],[f283])).
% 3.07/0.80  fof(f283,plain,(
% 3.07/0.80    ( ! [X4,X2,X3] : (k4_subset_1(X2,k3_subset_1(X2,X3),X4) = k3_subset_1(X2,k4_xboole_0(X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) ) | (~spl2_23 | ~spl2_30)),
% 3.07/0.80    inference(superposition,[],[f271,f214])).
% 3.07/0.80  fof(f214,plain,(
% 3.07/0.80    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_23),
% 3.07/0.80    inference(avatar_component_clause,[],[f213])).
% 3.07/0.80  fof(f271,plain,(
% 3.07/0.80    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_30),
% 3.07/0.80    inference(avatar_component_clause,[],[f270])).
% 3.07/0.80  fof(f546,plain,(
% 3.07/0.80    spl2_56 | ~spl2_7 | ~spl2_9 | ~spl2_22),
% 3.07/0.80    inference(avatar_split_clause,[],[f220,f202,f120,f112,f544])).
% 3.07/0.80  fof(f120,plain,(
% 3.07/0.80    spl2_9 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 3.07/0.80  fof(f202,plain,(
% 3.07/0.80    spl2_22 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 3.07/0.80  fof(f220,plain,(
% 3.07/0.80    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) ) | (~spl2_7 | ~spl2_9 | ~spl2_22)),
% 3.07/0.80    inference(forward_demodulation,[],[f217,f121])).
% 3.07/0.80  fof(f121,plain,(
% 3.07/0.80    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_9),
% 3.07/0.80    inference(avatar_component_clause,[],[f120])).
% 3.07/0.80  fof(f217,plain,(
% 3.07/0.80    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) ) | (~spl2_7 | ~spl2_22)),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f113,f203])).
% 3.07/0.80  fof(f203,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_22),
% 3.07/0.80    inference(avatar_component_clause,[],[f202])).
% 3.07/0.80  fof(f447,plain,(
% 3.07/0.80    spl2_50 | ~spl2_4 | ~spl2_13),
% 3.07/0.80    inference(avatar_split_clause,[],[f152,f137,f97,f445])).
% 3.07/0.80  fof(f97,plain,(
% 3.07/0.80    spl2_4 <=> ! [X1] : r1_tarski(X1,X1)),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 3.07/0.80  fof(f152,plain,(
% 3.07/0.80    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | (~spl2_4 | ~spl2_13)),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f98,f138])).
% 3.07/0.80  fof(f98,plain,(
% 3.07/0.80    ( ! [X1] : (r1_tarski(X1,X1)) ) | ~spl2_4),
% 3.07/0.80    inference(avatar_component_clause,[],[f97])).
% 3.07/0.80  fof(f424,plain,(
% 3.07/0.80    spl2_49 | ~spl2_7 | ~spl2_12),
% 3.07/0.80    inference(avatar_split_clause,[],[f149,f133,f112,f422])).
% 3.07/0.80  fof(f133,plain,(
% 3.07/0.80    spl2_12 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 3.07/0.80  fof(f149,plain,(
% 3.07/0.80    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl2_7 | ~spl2_12)),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f113,f134])).
% 3.07/0.80  fof(f134,plain,(
% 3.07/0.80    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_12),
% 3.07/0.80    inference(avatar_component_clause,[],[f133])).
% 3.07/0.80  fof(f383,plain,(
% 3.07/0.80    spl2_44 | ~spl2_2 | ~spl2_3 | ~spl2_29),
% 3.07/0.80    inference(avatar_split_clause,[],[f273,f266,f92,f87,f380])).
% 3.07/0.80  fof(f266,plain,(
% 3.07/0.80    spl2_29 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 3.07/0.80  fof(f273,plain,(
% 3.07/0.80    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_29)),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f89,f94,f267])).
% 3.07/0.80  fof(f267,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_29),
% 3.07/0.80    inference(avatar_component_clause,[],[f266])).
% 3.07/0.80  fof(f89,plain,(
% 3.07/0.80    l1_pre_topc(sK0) | ~spl2_2),
% 3.07/0.80    inference(avatar_component_clause,[],[f87])).
% 3.07/0.80  fof(f378,plain,(
% 3.07/0.80    spl2_43 | ~spl2_16 | ~spl2_19),
% 3.07/0.80    inference(avatar_split_clause,[],[f200,f169,f156,f376])).
% 3.07/0.80  fof(f156,plain,(
% 3.07/0.80    spl2_16 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 3.07/0.80  fof(f169,plain,(
% 3.07/0.80    spl2_19 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 3.07/0.80  fof(f200,plain,(
% 3.07/0.80    ( ! [X5] : (r1_tarski(X5,u1_struct_0(sK0)) | ~r1_tarski(X5,sK1)) ) | (~spl2_16 | ~spl2_19)),
% 3.07/0.80    inference(resolution,[],[f170,f158])).
% 3.07/0.80  fof(f158,plain,(
% 3.07/0.80    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_16),
% 3.07/0.80    inference(avatar_component_clause,[],[f156])).
% 3.07/0.80  fof(f170,plain,(
% 3.07/0.80    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl2_19),
% 3.07/0.80    inference(avatar_component_clause,[],[f169])).
% 3.07/0.80  fof(f374,plain,(
% 3.07/0.80    ~spl2_3 | spl2_42 | ~spl2_6 | ~spl2_23),
% 3.07/0.80    inference(avatar_split_clause,[],[f223,f213,f105,f371,f92])).
% 3.07/0.80  fof(f223,plain,(
% 3.07/0.80    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_6 | ~spl2_23)),
% 3.07/0.80    inference(superposition,[],[f214,f107])).
% 3.07/0.80  fof(f107,plain,(
% 3.07/0.80    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 3.07/0.80    inference(avatar_component_clause,[],[f105])).
% 3.07/0.80  fof(f360,plain,(
% 3.07/0.80    spl2_40 | ~spl2_2 | ~spl2_3 | ~spl2_28),
% 3.07/0.80    inference(avatar_split_clause,[],[f259,f256,f92,f87,f357])).
% 3.07/0.80  fof(f256,plain,(
% 3.07/0.80    spl2_28 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 3.07/0.80  fof(f259,plain,(
% 3.07/0.80    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_28)),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f89,f94,f257])).
% 3.07/0.80  fof(f257,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_28),
% 3.07/0.80    inference(avatar_component_clause,[],[f256])).
% 3.07/0.80  fof(f305,plain,(
% 3.07/0.80    spl2_31 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_25),
% 3.07/0.80    inference(avatar_split_clause,[],[f237,f230,f92,f87,f82,f302])).
% 3.07/0.80  fof(f82,plain,(
% 3.07/0.80    spl2_1 <=> v2_pre_topc(sK0)),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.07/0.80  fof(f230,plain,(
% 3.07/0.80    spl2_25 <=> ! [X1,X0] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.07/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 3.07/0.80  fof(f237,plain,(
% 3.07/0.80    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_25)),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f84,f89,f94,f231])).
% 3.07/0.80  fof(f231,plain,(
% 3.07/0.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl2_25),
% 3.07/0.80    inference(avatar_component_clause,[],[f230])).
% 3.07/0.80  fof(f84,plain,(
% 3.07/0.80    v2_pre_topc(sK0) | ~spl2_1),
% 3.07/0.80    inference(avatar_component_clause,[],[f82])).
% 3.07/0.80  fof(f272,plain,(
% 3.07/0.80    spl2_30),
% 3.07/0.80    inference(avatar_split_clause,[],[f68,f270])).
% 3.07/0.80  fof(f68,plain,(
% 3.07/0.80    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.07/0.80    inference(cnf_transformation,[],[f32])).
% 3.07/0.80  fof(f32,plain,(
% 3.07/0.80    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.07/0.80    inference(ennf_transformation,[],[f13])).
% 3.07/0.80  fof(f13,axiom,(
% 3.07/0.80    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 3.07/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).
% 3.07/0.80  fof(f268,plain,(
% 3.07/0.80    spl2_29),
% 3.07/0.80    inference(avatar_split_clause,[],[f59,f266])).
% 3.07/0.80  fof(f59,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.07/0.80    inference(cnf_transformation,[],[f27])).
% 3.07/0.80  fof(f27,plain,(
% 3.07/0.80    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.07/0.80    inference(ennf_transformation,[],[f19])).
% 3.07/0.80  fof(f19,axiom,(
% 3.07/0.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 3.07/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 3.07/0.80  fof(f258,plain,(
% 3.07/0.80    spl2_28),
% 3.07/0.80    inference(avatar_split_clause,[],[f58,f256])).
% 3.07/0.80  fof(f58,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.07/0.80    inference(cnf_transformation,[],[f26])).
% 3.07/0.80  fof(f26,plain,(
% 3.07/0.80    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.07/0.80    inference(ennf_transformation,[],[f20])).
% 3.07/0.80  fof(f20,axiom,(
% 3.07/0.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.07/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 3.07/0.80  fof(f246,plain,(
% 3.07/0.80    spl2_27),
% 3.07/0.80    inference(avatar_split_clause,[],[f78,f244])).
% 3.07/0.80  fof(f78,plain,(
% 3.07/0.80    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.07/0.80    inference(cnf_transformation,[],[f41])).
% 3.07/0.80  fof(f41,plain,(
% 3.07/0.80    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.07/0.80    inference(flattening,[],[f40])).
% 3.07/0.80  fof(f40,plain,(
% 3.07/0.80    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.07/0.80    inference(ennf_transformation,[],[f11])).
% 3.07/0.80  fof(f11,axiom,(
% 3.07/0.80    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 3.07/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.07/0.80  fof(f236,plain,(
% 3.07/0.80    spl2_26),
% 3.07/0.80    inference(avatar_split_clause,[],[f60,f234])).
% 3.07/0.80  fof(f60,plain,(
% 3.07/0.80    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.07/0.80    inference(cnf_transformation,[],[f29])).
% 3.07/0.80  fof(f29,plain,(
% 3.07/0.80    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.07/0.80    inference(flattening,[],[f28])).
% 3.07/0.80  fof(f28,plain,(
% 3.07/0.80    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.07/0.80    inference(ennf_transformation,[],[f21])).
% 3.07/0.80  fof(f21,axiom,(
% 3.07/0.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.07/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 3.07/0.80  fof(f232,plain,(
% 3.07/0.80    spl2_25),
% 3.07/0.80    inference(avatar_split_clause,[],[f69,f230])).
% 3.07/0.80  fof(f69,plain,(
% 3.07/0.80    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.07/0.80    inference(cnf_transformation,[],[f34])).
% 3.07/0.80  fof(f34,plain,(
% 3.07/0.80    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.07/0.80    inference(flattening,[],[f33])).
% 3.07/0.80  fof(f33,plain,(
% 3.07/0.80    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.07/0.80    inference(ennf_transformation,[],[f18])).
% 3.07/0.80  fof(f18,axiom,(
% 3.07/0.80    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 3.07/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 3.07/0.80  fof(f215,plain,(
% 3.07/0.80    spl2_23),
% 3.07/0.80    inference(avatar_split_clause,[],[f75,f213])).
% 3.07/0.80  fof(f75,plain,(
% 3.07/0.80    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.07/0.80    inference(cnf_transformation,[],[f35])).
% 3.07/0.80  fof(f35,plain,(
% 3.07/0.80    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.07/0.80    inference(ennf_transformation,[],[f12])).
% 3.07/0.80  fof(f12,axiom,(
% 3.07/0.80    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.07/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.07/0.80  fof(f204,plain,(
% 3.07/0.80    spl2_22),
% 3.07/0.80    inference(avatar_split_clause,[],[f67,f202])).
% 3.07/0.80  fof(f67,plain,(
% 3.07/0.80    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.07/0.80    inference(cnf_transformation,[],[f31])).
% 3.07/0.80  fof(f31,plain,(
% 3.07/0.80    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.07/0.80    inference(ennf_transformation,[],[f9])).
% 3.07/0.80  fof(f9,axiom,(
% 3.07/0.80    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.07/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 3.07/0.80  fof(f171,plain,(
% 3.07/0.80    spl2_19),
% 3.07/0.80    inference(avatar_split_clause,[],[f77,f169])).
% 3.07/0.80  fof(f77,plain,(
% 3.07/0.80    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.07/0.80    inference(cnf_transformation,[],[f39])).
% 3.07/0.80  fof(f39,plain,(
% 3.07/0.80    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.07/0.80    inference(flattening,[],[f38])).
% 3.07/0.80  fof(f38,plain,(
% 3.07/0.80    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.07/0.80    inference(ennf_transformation,[],[f3])).
% 3.07/0.80  fof(f3,axiom,(
% 3.07/0.80    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.07/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.07/0.80  fof(f167,plain,(
% 3.07/0.80    spl2_18),
% 3.07/0.80    inference(avatar_split_clause,[],[f72,f165])).
% 3.07/0.80  fof(f72,plain,(
% 3.07/0.80    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.07/0.80    inference(cnf_transformation,[],[f48])).
% 3.07/0.80  fof(f48,plain,(
% 3.07/0.80    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.07/0.80    inference(flattening,[],[f47])).
% 3.07/0.80  fof(f47,plain,(
% 3.07/0.80    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.07/0.80    inference(nnf_transformation,[],[f1])).
% 3.07/0.80  fof(f1,axiom,(
% 3.07/0.80    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.07/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.07/0.80  fof(f159,plain,(
% 3.07/0.80    spl2_16 | ~spl2_3 | ~spl2_12),
% 3.07/0.80    inference(avatar_split_clause,[],[f148,f133,f92,f156])).
% 3.07/0.80  fof(f148,plain,(
% 3.07/0.80    r1_tarski(sK1,u1_struct_0(sK0)) | (~spl2_3 | ~spl2_12)),
% 3.07/0.80    inference(unit_resulting_resolution,[],[f94,f134])).
% 3.07/0.80  fof(f139,plain,(
% 3.07/0.80    spl2_13),
% 3.07/0.80    inference(avatar_split_clause,[],[f74,f137])).
% 3.07/0.80  fof(f74,plain,(
% 3.07/0.80    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.07/0.80    inference(cnf_transformation,[],[f49])).
% 3.07/0.80  fof(f49,plain,(
% 3.07/0.80    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.07/0.80    inference(nnf_transformation,[],[f16])).
% 3.07/0.80  fof(f16,axiom,(
% 3.07/0.80    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.07/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.07/0.80  fof(f135,plain,(
% 3.07/0.80    spl2_12),
% 3.07/0.80    inference(avatar_split_clause,[],[f73,f133])).
% 3.07/0.80  fof(f73,plain,(
% 3.07/0.80    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.07/0.80    inference(cnf_transformation,[],[f49])).
% 3.07/0.80  fof(f126,plain,(
% 3.07/0.80    spl2_10),
% 3.07/0.80    inference(avatar_split_clause,[],[f61,f124])).
% 3.07/0.80  fof(f61,plain,(
% 3.07/0.80    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.07/0.80    inference(cnf_transformation,[],[f5])).
% 3.07/0.80  fof(f5,axiom,(
% 3.07/0.80    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.07/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.07/0.80  fof(f122,plain,(
% 3.07/0.80    spl2_9),
% 3.07/0.80    inference(avatar_split_clause,[],[f57,f120])).
% 3.07/0.80  fof(f57,plain,(
% 3.07/0.80    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.07/0.80    inference(cnf_transformation,[],[f6])).
% 3.07/0.80  fof(f6,axiom,(
% 3.07/0.80    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.07/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 3.07/0.80  fof(f114,plain,(
% 3.07/0.80    spl2_7),
% 3.07/0.80    inference(avatar_split_clause,[],[f55,f112])).
% 3.07/0.80  fof(f55,plain,(
% 3.07/0.80    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.07/0.80    inference(cnf_transformation,[],[f14])).
% 3.07/0.80  fof(f14,axiom,(
% 3.07/0.80    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.07/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 3.07/0.80  fof(f110,plain,(
% 3.07/0.80    ~spl2_5 | ~spl2_6),
% 3.07/0.80    inference(avatar_split_clause,[],[f109,f105,f101])).
% 3.07/0.80  fof(f109,plain,(
% 3.07/0.80    ~v4_pre_topc(sK1,sK0) | ~spl2_6),
% 3.07/0.80    inference(subsumption_resolution,[],[f54,f107])).
% 3.07/0.80  fof(f54,plain,(
% 3.07/0.80    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 3.07/0.80    inference(cnf_transformation,[],[f46])).
% 3.07/0.80  fof(f46,plain,(
% 3.07/0.80    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.07/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).
% 3.07/0.80  fof(f44,plain,(
% 3.07/0.80    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.07/0.80    introduced(choice_axiom,[])).
% 3.07/0.80  fof(f45,plain,(
% 3.07/0.80    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.07/0.80    introduced(choice_axiom,[])).
% 3.07/0.80  fof(f43,plain,(
% 3.07/0.80    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.07/0.80    inference(flattening,[],[f42])).
% 3.07/0.80  fof(f42,plain,(
% 3.07/0.80    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.07/0.80    inference(nnf_transformation,[],[f25])).
% 3.07/0.80  fof(f25,plain,(
% 3.07/0.80    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.07/0.80    inference(flattening,[],[f24])).
% 3.07/0.80  fof(f24,plain,(
% 3.07/0.80    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.07/0.80    inference(ennf_transformation,[],[f23])).
% 3.07/0.80  fof(f23,negated_conjecture,(
% 3.07/0.80    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 3.07/0.80    inference(negated_conjecture,[],[f22])).
% 3.07/0.80  fof(f22,conjecture,(
% 3.07/0.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 3.07/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 3.07/0.80  fof(f108,plain,(
% 3.07/0.80    spl2_5 | spl2_6),
% 3.07/0.80    inference(avatar_split_clause,[],[f53,f105,f101])).
% 3.07/0.80  fof(f53,plain,(
% 3.07/0.80    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 3.07/0.80    inference(cnf_transformation,[],[f46])).
% 3.07/0.80  fof(f99,plain,(
% 3.07/0.80    spl2_4),
% 3.07/0.80    inference(avatar_split_clause,[],[f79,f97])).
% 3.07/0.80  fof(f79,plain,(
% 3.07/0.80    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.07/0.80    inference(equality_resolution,[],[f71])).
% 3.07/0.80  fof(f71,plain,(
% 3.07/0.80    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.07/0.80    inference(cnf_transformation,[],[f48])).
% 3.07/0.80  fof(f95,plain,(
% 3.07/0.80    spl2_3),
% 3.07/0.80    inference(avatar_split_clause,[],[f52,f92])).
% 3.07/0.80  fof(f52,plain,(
% 3.07/0.80    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.07/0.80    inference(cnf_transformation,[],[f46])).
% 3.07/0.80  fof(f90,plain,(
% 3.07/0.80    spl2_2),
% 3.07/0.80    inference(avatar_split_clause,[],[f51,f87])).
% 3.07/0.80  fof(f51,plain,(
% 3.07/0.80    l1_pre_topc(sK0)),
% 3.07/0.80    inference(cnf_transformation,[],[f46])).
% 3.07/0.80  fof(f85,plain,(
% 3.07/0.80    spl2_1),
% 3.07/0.80    inference(avatar_split_clause,[],[f50,f82])).
% 3.07/0.80  fof(f50,plain,(
% 3.07/0.80    v2_pre_topc(sK0)),
% 3.07/0.80    inference(cnf_transformation,[],[f46])).
% 3.07/0.80  % SZS output end Proof for theBenchmark
% 3.07/0.80  % (14422)------------------------------
% 3.07/0.80  % (14422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.80  % (14422)Termination reason: Refutation
% 3.07/0.80  
% 3.07/0.80  % (14422)Memory used [KB]: 7547
% 3.07/0.80  % (14422)Time elapsed: 0.189 s
% 3.07/0.80  % (14422)------------------------------
% 3.07/0.80  % (14422)------------------------------
% 3.07/0.80  % (14391)Success in time 0.446 s
%------------------------------------------------------------------------------
