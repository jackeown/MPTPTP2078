%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:17 EST 2020

% Result     : Theorem 3.22s
% Output     : Refutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 382 expanded)
%              Number of leaves         :   53 ( 171 expanded)
%              Depth                    :   10
%              Number of atoms          :  655 (1225 expanded)
%              Number of equality atoms :   56 ( 110 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2226,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f94,f100,f108,f116,f120,f137,f141,f145,f149,f153,f157,f165,f169,f188,f239,f266,f270,f275,f326,f339,f349,f357,f369,f399,f421,f499,f588,f696,f748,f1130,f1290,f1666,f1668,f1909,f2139,f2171,f2218,f2225])).

fof(f2225,plain,
    ( ~ spl4_10
    | spl4_47
    | ~ spl4_105 ),
    inference(avatar_contradiction_clause,[],[f2224])).

fof(f2224,plain,
    ( $false
    | ~ spl4_10
    | spl4_47
    | ~ spl4_105 ),
    inference(subsumption_resolution,[],[f2168,f1908])).

fof(f1908,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_105 ),
    inference(avatar_component_clause,[],[f1906])).

fof(f1906,plain,
    ( spl4_105
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_105])])).

fof(f2168,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_10
    | spl4_47 ),
    inference(unit_resulting_resolution,[],[f586,f119])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f586,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | spl4_47 ),
    inference(avatar_component_clause,[],[f585])).

fof(f585,plain,
    ( spl4_47
  <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f2218,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | ~ spl4_17
    | ~ spl4_24
    | ~ spl4_28
    | ~ spl4_39
    | ~ spl4_61
    | ~ spl4_80
    | spl4_105 ),
    inference(avatar_contradiction_clause,[],[f2217])).

fof(f2217,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_17
    | ~ spl4_24
    | ~ spl4_28
    | ~ spl4_39
    | ~ spl4_61
    | ~ spl4_80
    | spl4_105 ),
    inference(subsumption_resolution,[],[f89,f2216])).

fof(f2216,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl4_5
    | ~ spl4_17
    | ~ spl4_24
    | ~ spl4_28
    | ~ spl4_39
    | ~ spl4_61
    | ~ spl4_80
    | spl4_105 ),
    inference(forward_demodulation,[],[f2204,f761])).

fof(f761,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl4_5
    | ~ spl4_17
    | ~ spl4_24
    | ~ spl4_28
    | ~ spl4_39
    | ~ spl4_61 ),
    inference(subsumption_resolution,[],[f404,f755])).

fof(f755,plain,
    ( ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl4_5
    | ~ spl4_17
    | ~ spl4_61 ),
    inference(unit_resulting_resolution,[],[f99,f747,f148])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f747,plain,
    ( ! [X0,X1] : r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f746])).

fof(f746,plain,
    ( spl4_61
  <=> ! [X1,X0] : r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f99,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_5
  <=> ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f404,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_24
    | ~ spl4_28
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f401,f187])).

fof(f187,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl4_24
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f401,plain,
    ( sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_28
    | ~ spl4_39 ),
    inference(superposition,[],[f398,f265])).

fof(f265,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl4_28
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f398,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl4_39
  <=> sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f2204,plain,
    ( ~ r1_tarski(sK1,k3_xboole_0(sK0,sK2))
    | ~ spl4_80
    | spl4_105 ),
    inference(unit_resulting_resolution,[],[f1907,f1129])).

fof(f1129,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,k3_xboole_0(X0,X1))
        | r1_xboole_0(X2,k4_xboole_0(X0,X1)) )
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f1128])).

fof(f1128,plain,
    ( spl4_80
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X2,k3_xboole_0(X0,X1))
        | r1_xboole_0(X2,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f1907,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl4_105 ),
    inference(avatar_component_clause,[],[f1906])).

fof(f89,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f2171,plain,
    ( ~ spl4_41
    | ~ spl4_15
    | spl4_45 ),
    inference(avatar_split_clause,[],[f514,f496,f139,f418])).

fof(f418,plain,
    ( spl4_41
  <=> r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f139,plain,
    ( spl4_15
  <=> ! [X3,X0] :
        ( r1_tarski(X3,X0)
        | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f496,plain,
    ( spl4_45
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f514,plain,
    ( ~ r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))
    | ~ spl4_15
    | spl4_45 ),
    inference(unit_resulting_resolution,[],[f498,f140])).

fof(f140,plain,
    ( ! [X0,X3] :
        ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
        | r1_tarski(X3,X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f139])).

fof(f498,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl4_45 ),
    inference(avatar_component_clause,[],[f496])).

fof(f2139,plain,
    ( ~ spl4_5
    | ~ spl4_17
    | ~ spl4_24
    | ~ spl4_28
    | ~ spl4_33
    | ~ spl4_39
    | ~ spl4_57
    | ~ spl4_61
    | ~ spl4_88
    | ~ spl4_99
    | ~ spl4_105 ),
    inference(avatar_contradiction_clause,[],[f2138])).

fof(f2138,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_17
    | ~ spl4_24
    | ~ spl4_28
    | ~ spl4_33
    | ~ spl4_39
    | ~ spl4_57
    | ~ spl4_61
    | ~ spl4_88
    | ~ spl4_99
    | ~ spl4_105 ),
    inference(subsumption_resolution,[],[f1891,f2137])).

fof(f2137,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_5
    | ~ spl4_17
    | ~ spl4_24
    | ~ spl4_28
    | ~ spl4_33
    | ~ spl4_39
    | ~ spl4_61
    | ~ spl4_88
    | ~ spl4_105 ),
    inference(forward_demodulation,[],[f2136,f761])).

fof(f2136,plain,
    ( r1_tarski(sK1,k3_xboole_0(sK0,sK2))
    | ~ spl4_24
    | ~ spl4_33
    | ~ spl4_88
    | ~ spl4_105 ),
    inference(forward_demodulation,[],[f2121,f187])).

fof(f2121,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl4_33
    | ~ spl4_88
    | ~ spl4_105 ),
    inference(unit_resulting_resolution,[],[f325,f1908,f1289])).

fof(f1289,plain,
    ( ! [X4,X2,X3] :
        ( r1_tarski(X2,k4_xboole_0(X4,X3))
        | ~ r1_tarski(X2,X4)
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl4_88 ),
    inference(avatar_component_clause,[],[f1288])).

fof(f1288,plain,
    ( spl4_88
  <=> ! [X3,X2,X4] :
        ( r1_tarski(X2,k4_xboole_0(X4,X3))
        | ~ r1_tarski(X2,X4)
        | ~ r1_xboole_0(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f325,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl4_33
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f1891,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl4_57
    | ~ spl4_99 ),
    inference(superposition,[],[f1665,f695])).

fof(f695,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f694])).

fof(f694,plain,
    ( spl4_57
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f1665,plain,
    ( ! [X1] : ~ r1_tarski(sK1,k3_xboole_0(sK2,X1))
    | ~ spl4_99 ),
    inference(avatar_component_clause,[],[f1664])).

fof(f1664,plain,
    ( spl4_99
  <=> ! [X1] : ~ r1_tarski(sK1,k3_xboole_0(sK2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).

fof(f1909,plain,
    ( spl4_105
    | ~ spl4_10
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f590,f585,f118,f1906])).

fof(f590,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_10
    | ~ spl4_47 ),
    inference(unit_resulting_resolution,[],[f587,f119])).

fof(f587,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f585])).

fof(f1668,plain,
    ( ~ spl4_9
    | spl4_45
    | ~ spl4_47
    | ~ spl4_88 ),
    inference(avatar_contradiction_clause,[],[f1667])).

fof(f1667,plain,
    ( $false
    | ~ spl4_9
    | spl4_45
    | ~ spl4_47
    | ~ spl4_88 ),
    inference(subsumption_resolution,[],[f1297,f498])).

fof(f1297,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_9
    | ~ spl4_47
    | ~ spl4_88 ),
    inference(unit_resulting_resolution,[],[f587,f115,f1289])).

fof(f115,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_9
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1666,plain,
    ( spl4_99
    | ~ spl4_24
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f344,f337,f186,f1664])).

fof(f337,plain,
    ( spl4_35
  <=> ! [X0] : ~ r1_tarski(sK1,k4_xboole_0(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f344,plain,
    ( ! [X1] : ~ r1_tarski(sK1,k3_xboole_0(sK2,X1))
    | ~ spl4_24
    | ~ spl4_35 ),
    inference(superposition,[],[f338,f187])).

fof(f338,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k4_xboole_0(sK2,X0))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f337])).

fof(f1290,plain,
    ( spl4_88
    | ~ spl4_19
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f284,f237,f155,f1288])).

fof(f155,plain,
    ( spl4_19
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f237,plain,
    ( spl4_27
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f284,plain,
    ( ! [X4,X2,X3] :
        ( r1_tarski(X2,k4_xboole_0(X4,X3))
        | ~ r1_tarski(X2,X4)
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl4_19
    | ~ spl4_27 ),
    inference(superposition,[],[f238,f156])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f155])).

fof(f238,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f237])).

fof(f1130,plain,
    ( spl4_80
    | ~ spl4_22
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f244,f186,f167,f1128])).

fof(f167,plain,
    ( spl4_22
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f244,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,k3_xboole_0(X0,X1))
        | r1_xboole_0(X2,k4_xboole_0(X0,X1)) )
    | ~ spl4_22
    | ~ spl4_24 ),
    inference(superposition,[],[f168,f187])).

fof(f168,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        | r1_xboole_0(X0,X2) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f167])).

fof(f748,plain,
    ( spl4_61
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f175,f135,f114,f746])).

fof(f135,plain,
    ( spl4_14
  <=> ! [X3,X0] :
        ( r2_hidden(X3,k1_zfmisc_1(X0))
        | ~ r1_tarski(X3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f175,plain,
    ( ! [X0,X1] : r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f115,f136])).

fof(f136,plain,
    ( ! [X0,X3] :
        ( r2_hidden(X3,k1_zfmisc_1(X0))
        | ~ r1_tarski(X3,X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f696,plain,
    ( spl4_57
    | ~ spl4_7
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f203,f151,f106,f694])).

fof(f106,plain,
    ( spl4_7
  <=> ! [X1] : r1_tarski(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f151,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f203,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl4_7
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f107,f152])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f151])).

fof(f107,plain,
    ( ! [X1] : r1_tarski(X1,X1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f588,plain,
    ( spl4_47
    | ~ spl4_22
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f559,f496,f167,f585])).

fof(f559,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl4_22
    | ~ spl4_45 ),
    inference(unit_resulting_resolution,[],[f497,f168])).

fof(f497,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f496])).

fof(f499,plain,
    ( ~ spl4_3
    | ~ spl4_45
    | ~ spl4_36
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f460,f354,f346,f496,f87])).

fof(f346,plain,
    ( spl4_36
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f354,plain,
    ( spl4_37
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f460,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK1,sK2)
    | ~ spl4_36
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f459,f356])).

fof(f356,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f354])).

fof(f459,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK1,sK2)
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f44,f348])).

fof(f348,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f346])).

fof(f44,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f31,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | ~ r1_tarski(sK1,X2) )
        & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | r1_tarski(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | ~ r1_tarski(sK1,sK2) )
      & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | r1_tarski(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f421,plain,
    ( spl4_41
    | ~ spl4_36
    | ~ spl4_37
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f378,f366,f354,f346,f418])).

fof(f366,plain,
    ( spl4_38
  <=> r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(k3_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f378,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))
    | ~ spl4_36
    | ~ spl4_37
    | ~ spl4_38 ),
    inference(forward_demodulation,[],[f377,f356])).

fof(f377,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))
    | ~ spl4_36
    | ~ spl4_38 ),
    inference(forward_demodulation,[],[f368,f348])).

fof(f368,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(k3_subset_1(sK0,sK1)))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f366])).

fof(f399,plain,
    ( spl4_39
    | ~ spl4_2
    | ~ spl4_28
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f303,f268,f264,f82,f396])).

fof(f82,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f268,plain,
    ( spl4_29
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f303,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_2
    | ~ spl4_28
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f298,f292])).

fof(f292,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_2
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f84,f265])).

fof(f84,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f298,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl4_2
    | ~ spl4_29 ),
    inference(unit_resulting_resolution,[],[f84,f269])).

fof(f269,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f268])).

fof(f369,plain,
    ( spl4_38
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f177,f135,f91,f366])).

fof(f91,plain,
    ( spl4_4
  <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f177,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(k3_subset_1(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f93,f136])).

fof(f93,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f357,plain,
    ( spl4_37
    | ~ spl4_2
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f292,f264,f82,f354])).

fof(f349,plain,
    ( spl4_36
    | ~ spl4_1
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f291,f264,f77,f346])).

fof(f77,plain,
    ( spl4_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f291,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_1
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f79,f265])).

fof(f79,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f339,plain,
    ( spl4_35
    | spl4_3
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f219,f163,f87,f337])).

fof(f163,plain,
    ( spl4_21
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X1)
        | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f219,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k4_xboole_0(sK2,X0))
    | spl4_3
    | ~ spl4_21 ),
    inference(unit_resulting_resolution,[],[f88,f164])).

fof(f164,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        | r1_tarski(X0,X1) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f163])).

fof(f88,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f326,plain,
    ( spl4_33
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f318,f272,f139,f323])).

fof(f272,plain,
    ( spl4_30
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f318,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(unit_resulting_resolution,[],[f274,f140])).

fof(f274,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f272])).

fof(f275,plain,
    ( spl4_30
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f197,f143,f98,f77,f272])).

fof(f143,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f197,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f99,f79,f144])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | r2_hidden(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f143])).

fof(f270,plain,(
    spl4_29 ),
    inference(avatar_split_clause,[],[f59,f268])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f266,plain,(
    spl4_28 ),
    inference(avatar_split_clause,[],[f58,f264])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f239,plain,(
    spl4_27 ),
    inference(avatar_split_clause,[],[f69,f237])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

fof(f188,plain,(
    spl4_24 ),
    inference(avatar_split_clause,[],[f50,f186])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f169,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f71,f167])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f165,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f70,f163])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f157,plain,(
    spl4_19 ),
    inference(avatar_split_clause,[],[f63,f155])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f153,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f57,f151])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f149,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f53,f147])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f145,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f52,f143])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f141,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f75,f139])).

fof(f75,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f137,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f74,f135])).

fof(f74,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f120,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f56,f118])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f116,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f48,f114])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f108,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f72,f106])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f100,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f45,f98])).

fof(f45,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f94,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f43,f91,f87])).

fof(f43,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f42,f82])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f41,f77])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:19:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.50  % (25430)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (25422)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.50  % (25421)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.50  % (25414)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (25408)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (25410)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (25437)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (25419)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (25423)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (25429)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (25435)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (25437)Refutation not found, incomplete strategy% (25437)------------------------------
% 0.21/0.52  % (25437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (25437)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (25437)Memory used [KB]: 1663
% 0.21/0.52  % (25437)Time elapsed: 0.003 s
% 0.21/0.52  % (25437)------------------------------
% 0.21/0.52  % (25437)------------------------------
% 0.21/0.53  % (25415)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (25427)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (25432)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (25412)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (25409)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (25409)Refutation not found, incomplete strategy% (25409)------------------------------
% 0.21/0.53  % (25409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (25409)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (25409)Memory used [KB]: 1663
% 0.21/0.53  % (25409)Time elapsed: 0.125 s
% 0.21/0.53  % (25409)------------------------------
% 0.21/0.53  % (25409)------------------------------
% 0.21/0.53  % (25411)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (25424)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (25418)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (25433)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (25424)Refutation not found, incomplete strategy% (25424)------------------------------
% 0.21/0.54  % (25424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25424)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25424)Memory used [KB]: 10618
% 0.21/0.54  % (25424)Time elapsed: 0.137 s
% 0.21/0.54  % (25424)------------------------------
% 0.21/0.54  % (25424)------------------------------
% 0.21/0.54  % (25418)Refutation not found, incomplete strategy% (25418)------------------------------
% 0.21/0.54  % (25418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25418)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25418)Memory used [KB]: 10746
% 0.21/0.54  % (25418)Time elapsed: 0.135 s
% 0.21/0.54  % (25418)------------------------------
% 0.21/0.54  % (25418)------------------------------
% 0.21/0.54  % (25416)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (25434)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (25425)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (25413)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (25426)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (25426)Refutation not found, incomplete strategy% (25426)------------------------------
% 0.21/0.55  % (25426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (25426)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (25426)Memory used [KB]: 1791
% 0.21/0.55  % (25426)Time elapsed: 0.149 s
% 0.21/0.55  % (25426)------------------------------
% 0.21/0.55  % (25426)------------------------------
% 0.21/0.55  % (25417)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (25420)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (25431)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (25436)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.56  % (25436)Refutation not found, incomplete strategy% (25436)------------------------------
% 0.21/0.56  % (25436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (25436)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (25436)Memory used [KB]: 10746
% 0.21/0.56  % (25436)Time elapsed: 0.161 s
% 0.21/0.56  % (25436)------------------------------
% 0.21/0.56  % (25436)------------------------------
% 0.21/0.57  % (25428)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 2.08/0.67  % (25439)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.08/0.67  % (25438)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.08/0.67  % (25440)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.08/0.67  % (25441)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.08/0.69  % (25442)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.08/0.69  % (25411)Refutation not found, incomplete strategy% (25411)------------------------------
% 2.08/0.69  % (25411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.70  % (25411)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.70  
% 2.08/0.70  % (25411)Memory used [KB]: 6268
% 2.08/0.70  % (25411)Time elapsed: 0.261 s
% 2.08/0.70  % (25411)------------------------------
% 2.08/0.70  % (25411)------------------------------
% 2.66/0.73  % (25443)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 3.22/0.80  % (25438)Refutation found. Thanks to Tanya!
% 3.22/0.80  % SZS status Theorem for theBenchmark
% 3.22/0.80  % (25432)Time limit reached!
% 3.22/0.80  % (25432)------------------------------
% 3.22/0.80  % (25432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.22/0.82  % (25432)Termination reason: Time limit
% 3.22/0.82  % (25432)Termination phase: Saturation
% 3.22/0.82  
% 3.22/0.82  % (25432)Memory used [KB]: 12792
% 3.22/0.82  % (25432)Time elapsed: 0.400 s
% 3.22/0.82  % (25432)------------------------------
% 3.22/0.82  % (25432)------------------------------
% 3.22/0.82  % SZS output start Proof for theBenchmark
% 3.22/0.82  fof(f2226,plain,(
% 3.22/0.82    $false),
% 3.22/0.82    inference(avatar_sat_refutation,[],[f80,f85,f94,f100,f108,f116,f120,f137,f141,f145,f149,f153,f157,f165,f169,f188,f239,f266,f270,f275,f326,f339,f349,f357,f369,f399,f421,f499,f588,f696,f748,f1130,f1290,f1666,f1668,f1909,f2139,f2171,f2218,f2225])).
% 3.22/0.82  fof(f2225,plain,(
% 3.22/0.82    ~spl4_10 | spl4_47 | ~spl4_105),
% 3.22/0.82    inference(avatar_contradiction_clause,[],[f2224])).
% 3.22/0.82  fof(f2224,plain,(
% 3.22/0.82    $false | (~spl4_10 | spl4_47 | ~spl4_105)),
% 3.22/0.82    inference(subsumption_resolution,[],[f2168,f1908])).
% 3.22/0.82  fof(f1908,plain,(
% 3.22/0.82    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl4_105),
% 3.22/0.82    inference(avatar_component_clause,[],[f1906])).
% 3.22/0.82  fof(f1906,plain,(
% 3.22/0.82    spl4_105 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_105])])).
% 3.22/0.82  fof(f2168,plain,(
% 3.22/0.82    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | (~spl4_10 | spl4_47)),
% 3.22/0.82    inference(unit_resulting_resolution,[],[f586,f119])).
% 3.22/0.82  fof(f119,plain,(
% 3.22/0.82    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl4_10),
% 3.22/0.82    inference(avatar_component_clause,[],[f118])).
% 3.22/0.82  fof(f118,plain,(
% 3.22/0.82    spl4_10 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 3.22/0.82  fof(f586,plain,(
% 3.22/0.82    ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | spl4_47),
% 3.22/0.82    inference(avatar_component_clause,[],[f585])).
% 3.22/0.82  fof(f585,plain,(
% 3.22/0.82    spl4_47 <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 3.22/0.82  fof(f2218,plain,(
% 3.22/0.82    ~spl4_3 | ~spl4_5 | ~spl4_17 | ~spl4_24 | ~spl4_28 | ~spl4_39 | ~spl4_61 | ~spl4_80 | spl4_105),
% 3.22/0.82    inference(avatar_contradiction_clause,[],[f2217])).
% 3.22/0.82  fof(f2217,plain,(
% 3.22/0.82    $false | (~spl4_3 | ~spl4_5 | ~spl4_17 | ~spl4_24 | ~spl4_28 | ~spl4_39 | ~spl4_61 | ~spl4_80 | spl4_105)),
% 3.22/0.82    inference(subsumption_resolution,[],[f89,f2216])).
% 3.22/0.82  fof(f2216,plain,(
% 3.22/0.82    ~r1_tarski(sK1,sK2) | (~spl4_5 | ~spl4_17 | ~spl4_24 | ~spl4_28 | ~spl4_39 | ~spl4_61 | ~spl4_80 | spl4_105)),
% 3.22/0.82    inference(forward_demodulation,[],[f2204,f761])).
% 3.22/0.82  fof(f761,plain,(
% 3.22/0.82    sK2 = k3_xboole_0(sK0,sK2) | (~spl4_5 | ~spl4_17 | ~spl4_24 | ~spl4_28 | ~spl4_39 | ~spl4_61)),
% 3.22/0.82    inference(subsumption_resolution,[],[f404,f755])).
% 3.22/0.82  fof(f755,plain,(
% 3.22/0.82    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | (~spl4_5 | ~spl4_17 | ~spl4_61)),
% 3.22/0.82    inference(unit_resulting_resolution,[],[f99,f747,f148])).
% 3.22/0.82  fof(f148,plain,(
% 3.22/0.82    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl4_17),
% 3.22/0.82    inference(avatar_component_clause,[],[f147])).
% 3.22/0.82  fof(f147,plain,(
% 3.22/0.82    spl4_17 <=> ! [X1,X0] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 3.22/0.82  fof(f747,plain,(
% 3.22/0.82    ( ! [X0,X1] : (r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl4_61),
% 3.22/0.82    inference(avatar_component_clause,[],[f746])).
% 3.22/0.82  fof(f746,plain,(
% 3.22/0.82    spl4_61 <=> ! [X1,X0] : r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 3.22/0.82  fof(f99,plain,(
% 3.22/0.82    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) ) | ~spl4_5),
% 3.22/0.82    inference(avatar_component_clause,[],[f98])).
% 3.22/0.82  fof(f98,plain,(
% 3.22/0.82    spl4_5 <=> ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 3.22/0.82  fof(f404,plain,(
% 3.22/0.82    sK2 = k3_xboole_0(sK0,sK2) | ~m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | (~spl4_24 | ~spl4_28 | ~spl4_39)),
% 3.22/0.82    inference(forward_demodulation,[],[f401,f187])).
% 3.22/0.82  fof(f187,plain,(
% 3.22/0.82    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl4_24),
% 3.22/0.82    inference(avatar_component_clause,[],[f186])).
% 3.22/0.82  fof(f186,plain,(
% 3.22/0.82    spl4_24 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 3.22/0.82  fof(f401,plain,(
% 3.22/0.82    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | (~spl4_28 | ~spl4_39)),
% 3.22/0.82    inference(superposition,[],[f398,f265])).
% 3.22/0.82  fof(f265,plain,(
% 3.22/0.82    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_28),
% 3.22/0.82    inference(avatar_component_clause,[],[f264])).
% 3.22/0.82  fof(f264,plain,(
% 3.22/0.82    spl4_28 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 3.22/0.82  fof(f398,plain,(
% 3.22/0.82    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | ~spl4_39),
% 3.22/0.82    inference(avatar_component_clause,[],[f396])).
% 3.22/0.82  fof(f396,plain,(
% 3.22/0.82    spl4_39 <=> sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 3.22/0.82  fof(f2204,plain,(
% 3.22/0.82    ~r1_tarski(sK1,k3_xboole_0(sK0,sK2)) | (~spl4_80 | spl4_105)),
% 3.22/0.82    inference(unit_resulting_resolution,[],[f1907,f1129])).
% 3.22/0.82  fof(f1129,plain,(
% 3.22/0.82    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_xboole_0(X0,X1)) | r1_xboole_0(X2,k4_xboole_0(X0,X1))) ) | ~spl4_80),
% 3.22/0.82    inference(avatar_component_clause,[],[f1128])).
% 3.22/0.82  fof(f1128,plain,(
% 3.22/0.82    spl4_80 <=> ! [X1,X0,X2] : (~r1_tarski(X2,k3_xboole_0(X0,X1)) | r1_xboole_0(X2,k4_xboole_0(X0,X1)))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).
% 3.22/0.82  fof(f1907,plain,(
% 3.22/0.82    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl4_105),
% 3.22/0.82    inference(avatar_component_clause,[],[f1906])).
% 3.22/0.82  fof(f89,plain,(
% 3.22/0.82    r1_tarski(sK1,sK2) | ~spl4_3),
% 3.22/0.82    inference(avatar_component_clause,[],[f87])).
% 3.22/0.82  fof(f87,plain,(
% 3.22/0.82    spl4_3 <=> r1_tarski(sK1,sK2)),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 3.22/0.82  fof(f2171,plain,(
% 3.22/0.82    ~spl4_41 | ~spl4_15 | spl4_45),
% 3.22/0.82    inference(avatar_split_clause,[],[f514,f496,f139,f418])).
% 3.22/0.82  fof(f418,plain,(
% 3.22/0.82    spl4_41 <=> r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 3.22/0.82  fof(f139,plain,(
% 3.22/0.82    spl4_15 <=> ! [X3,X0] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0)))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 3.22/0.82  fof(f496,plain,(
% 3.22/0.82    spl4_45 <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 3.22/0.82  fof(f514,plain,(
% 3.22/0.82    ~r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) | (~spl4_15 | spl4_45)),
% 3.22/0.82    inference(unit_resulting_resolution,[],[f498,f140])).
% 3.22/0.82  fof(f140,plain,(
% 3.22/0.82    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) ) | ~spl4_15),
% 3.22/0.82    inference(avatar_component_clause,[],[f139])).
% 3.22/0.82  fof(f498,plain,(
% 3.22/0.82    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl4_45),
% 3.22/0.82    inference(avatar_component_clause,[],[f496])).
% 3.22/0.82  fof(f2139,plain,(
% 3.22/0.82    ~spl4_5 | ~spl4_17 | ~spl4_24 | ~spl4_28 | ~spl4_33 | ~spl4_39 | ~spl4_57 | ~spl4_61 | ~spl4_88 | ~spl4_99 | ~spl4_105),
% 3.22/0.82    inference(avatar_contradiction_clause,[],[f2138])).
% 3.22/0.82  fof(f2138,plain,(
% 3.22/0.82    $false | (~spl4_5 | ~spl4_17 | ~spl4_24 | ~spl4_28 | ~spl4_33 | ~spl4_39 | ~spl4_57 | ~spl4_61 | ~spl4_88 | ~spl4_99 | ~spl4_105)),
% 3.22/0.82    inference(subsumption_resolution,[],[f1891,f2137])).
% 3.22/0.82  fof(f2137,plain,(
% 3.22/0.82    r1_tarski(sK1,sK2) | (~spl4_5 | ~spl4_17 | ~spl4_24 | ~spl4_28 | ~spl4_33 | ~spl4_39 | ~spl4_61 | ~spl4_88 | ~spl4_105)),
% 3.22/0.82    inference(forward_demodulation,[],[f2136,f761])).
% 3.22/0.82  fof(f2136,plain,(
% 3.22/0.82    r1_tarski(sK1,k3_xboole_0(sK0,sK2)) | (~spl4_24 | ~spl4_33 | ~spl4_88 | ~spl4_105)),
% 3.22/0.82    inference(forward_demodulation,[],[f2121,f187])).
% 3.22/0.82  fof(f2121,plain,(
% 3.22/0.82    r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | (~spl4_33 | ~spl4_88 | ~spl4_105)),
% 3.22/0.82    inference(unit_resulting_resolution,[],[f325,f1908,f1289])).
% 3.22/0.82  fof(f1289,plain,(
% 3.22/0.82    ( ! [X4,X2,X3] : (r1_tarski(X2,k4_xboole_0(X4,X3)) | ~r1_tarski(X2,X4) | ~r1_xboole_0(X2,X3)) ) | ~spl4_88),
% 3.22/0.82    inference(avatar_component_clause,[],[f1288])).
% 3.22/0.82  fof(f1288,plain,(
% 3.22/0.82    spl4_88 <=> ! [X3,X2,X4] : (r1_tarski(X2,k4_xboole_0(X4,X3)) | ~r1_tarski(X2,X4) | ~r1_xboole_0(X2,X3))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).
% 3.22/0.82  fof(f325,plain,(
% 3.22/0.82    r1_tarski(sK1,sK0) | ~spl4_33),
% 3.22/0.82    inference(avatar_component_clause,[],[f323])).
% 3.22/0.82  fof(f323,plain,(
% 3.22/0.82    spl4_33 <=> r1_tarski(sK1,sK0)),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 3.22/0.82  fof(f1891,plain,(
% 3.22/0.82    ~r1_tarski(sK1,sK2) | (~spl4_57 | ~spl4_99)),
% 3.22/0.82    inference(superposition,[],[f1665,f695])).
% 3.22/0.82  fof(f695,plain,(
% 3.22/0.82    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl4_57),
% 3.22/0.82    inference(avatar_component_clause,[],[f694])).
% 3.22/0.82  fof(f694,plain,(
% 3.22/0.82    spl4_57 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 3.22/0.82  fof(f1665,plain,(
% 3.22/0.82    ( ! [X1] : (~r1_tarski(sK1,k3_xboole_0(sK2,X1))) ) | ~spl4_99),
% 3.22/0.82    inference(avatar_component_clause,[],[f1664])).
% 3.22/0.82  fof(f1664,plain,(
% 3.22/0.82    spl4_99 <=> ! [X1] : ~r1_tarski(sK1,k3_xboole_0(sK2,X1))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).
% 3.22/0.82  fof(f1909,plain,(
% 3.22/0.82    spl4_105 | ~spl4_10 | ~spl4_47),
% 3.22/0.82    inference(avatar_split_clause,[],[f590,f585,f118,f1906])).
% 3.22/0.82  fof(f590,plain,(
% 3.22/0.82    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | (~spl4_10 | ~spl4_47)),
% 3.22/0.82    inference(unit_resulting_resolution,[],[f587,f119])).
% 3.22/0.82  fof(f587,plain,(
% 3.22/0.82    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl4_47),
% 3.22/0.82    inference(avatar_component_clause,[],[f585])).
% 3.22/0.82  fof(f1668,plain,(
% 3.22/0.82    ~spl4_9 | spl4_45 | ~spl4_47 | ~spl4_88),
% 3.22/0.82    inference(avatar_contradiction_clause,[],[f1667])).
% 3.22/0.82  fof(f1667,plain,(
% 3.22/0.82    $false | (~spl4_9 | spl4_45 | ~spl4_47 | ~spl4_88)),
% 3.22/0.82    inference(subsumption_resolution,[],[f1297,f498])).
% 3.22/0.82  fof(f1297,plain,(
% 3.22/0.82    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | (~spl4_9 | ~spl4_47 | ~spl4_88)),
% 3.22/0.82    inference(unit_resulting_resolution,[],[f587,f115,f1289])).
% 3.22/0.82  fof(f115,plain,(
% 3.22/0.82    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl4_9),
% 3.22/0.82    inference(avatar_component_clause,[],[f114])).
% 3.22/0.82  fof(f114,plain,(
% 3.22/0.82    spl4_9 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 3.22/0.82  fof(f1666,plain,(
% 3.22/0.82    spl4_99 | ~spl4_24 | ~spl4_35),
% 3.22/0.82    inference(avatar_split_clause,[],[f344,f337,f186,f1664])).
% 3.22/0.82  fof(f337,plain,(
% 3.22/0.82    spl4_35 <=> ! [X0] : ~r1_tarski(sK1,k4_xboole_0(sK2,X0))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 3.22/0.82  fof(f344,plain,(
% 3.22/0.82    ( ! [X1] : (~r1_tarski(sK1,k3_xboole_0(sK2,X1))) ) | (~spl4_24 | ~spl4_35)),
% 3.22/0.82    inference(superposition,[],[f338,f187])).
% 3.22/0.82  fof(f338,plain,(
% 3.22/0.82    ( ! [X0] : (~r1_tarski(sK1,k4_xboole_0(sK2,X0))) ) | ~spl4_35),
% 3.22/0.82    inference(avatar_component_clause,[],[f337])).
% 3.22/0.82  fof(f1290,plain,(
% 3.22/0.82    spl4_88 | ~spl4_19 | ~spl4_27),
% 3.22/0.82    inference(avatar_split_clause,[],[f284,f237,f155,f1288])).
% 3.22/0.82  fof(f155,plain,(
% 3.22/0.82    spl4_19 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 3.22/0.82  fof(f237,plain,(
% 3.22/0.82    spl4_27 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 3.22/0.82  fof(f284,plain,(
% 3.22/0.82    ( ! [X4,X2,X3] : (r1_tarski(X2,k4_xboole_0(X4,X3)) | ~r1_tarski(X2,X4) | ~r1_xboole_0(X2,X3)) ) | (~spl4_19 | ~spl4_27)),
% 3.22/0.82    inference(superposition,[],[f238,f156])).
% 3.22/0.82  fof(f156,plain,(
% 3.22/0.82    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl4_19),
% 3.22/0.82    inference(avatar_component_clause,[],[f155])).
% 3.22/0.82  fof(f238,plain,(
% 3.22/0.82    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) ) | ~spl4_27),
% 3.22/0.82    inference(avatar_component_clause,[],[f237])).
% 3.22/0.82  fof(f1130,plain,(
% 3.22/0.82    spl4_80 | ~spl4_22 | ~spl4_24),
% 3.22/0.82    inference(avatar_split_clause,[],[f244,f186,f167,f1128])).
% 3.22/0.82  fof(f167,plain,(
% 3.22/0.82    spl4_22 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 3.22/0.82  fof(f244,plain,(
% 3.22/0.82    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_xboole_0(X0,X1)) | r1_xboole_0(X2,k4_xboole_0(X0,X1))) ) | (~spl4_22 | ~spl4_24)),
% 3.22/0.82    inference(superposition,[],[f168,f187])).
% 3.22/0.82  fof(f168,plain,(
% 3.22/0.82    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) ) | ~spl4_22),
% 3.22/0.82    inference(avatar_component_clause,[],[f167])).
% 3.22/0.82  fof(f748,plain,(
% 3.22/0.82    spl4_61 | ~spl4_9 | ~spl4_14),
% 3.22/0.82    inference(avatar_split_clause,[],[f175,f135,f114,f746])).
% 3.22/0.82  fof(f135,plain,(
% 3.22/0.82    spl4_14 <=> ! [X3,X0] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 3.22/0.82  fof(f175,plain,(
% 3.22/0.82    ( ! [X0,X1] : (r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | (~spl4_9 | ~spl4_14)),
% 3.22/0.82    inference(unit_resulting_resolution,[],[f115,f136])).
% 3.22/0.82  fof(f136,plain,(
% 3.22/0.82    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) ) | ~spl4_14),
% 3.22/0.82    inference(avatar_component_clause,[],[f135])).
% 3.22/0.82  fof(f696,plain,(
% 3.22/0.82    spl4_57 | ~spl4_7 | ~spl4_18),
% 3.22/0.82    inference(avatar_split_clause,[],[f203,f151,f106,f694])).
% 3.22/0.82  fof(f106,plain,(
% 3.22/0.82    spl4_7 <=> ! [X1] : r1_tarski(X1,X1)),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 3.22/0.82  fof(f151,plain,(
% 3.22/0.82    spl4_18 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 3.22/0.82  fof(f203,plain,(
% 3.22/0.82    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | (~spl4_7 | ~spl4_18)),
% 3.22/0.82    inference(unit_resulting_resolution,[],[f107,f152])).
% 3.22/0.82  fof(f152,plain,(
% 3.22/0.82    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl4_18),
% 3.22/0.82    inference(avatar_component_clause,[],[f151])).
% 3.22/0.82  fof(f107,plain,(
% 3.22/0.82    ( ! [X1] : (r1_tarski(X1,X1)) ) | ~spl4_7),
% 3.22/0.82    inference(avatar_component_clause,[],[f106])).
% 3.22/0.82  fof(f588,plain,(
% 3.22/0.82    spl4_47 | ~spl4_22 | ~spl4_45),
% 3.22/0.82    inference(avatar_split_clause,[],[f559,f496,f167,f585])).
% 3.22/0.82  fof(f559,plain,(
% 3.22/0.82    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | (~spl4_22 | ~spl4_45)),
% 3.22/0.82    inference(unit_resulting_resolution,[],[f497,f168])).
% 3.22/0.82  fof(f497,plain,(
% 3.22/0.82    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl4_45),
% 3.22/0.82    inference(avatar_component_clause,[],[f496])).
% 3.22/0.82  fof(f499,plain,(
% 3.22/0.82    ~spl4_3 | ~spl4_45 | ~spl4_36 | ~spl4_37),
% 3.22/0.82    inference(avatar_split_clause,[],[f460,f354,f346,f496,f87])).
% 3.22/0.82  fof(f346,plain,(
% 3.22/0.82    spl4_36 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 3.22/0.82  fof(f354,plain,(
% 3.22/0.82    spl4_37 <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 3.22/0.82  fof(f460,plain,(
% 3.22/0.82    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~r1_tarski(sK1,sK2) | (~spl4_36 | ~spl4_37)),
% 3.22/0.82    inference(forward_demodulation,[],[f459,f356])).
% 3.22/0.82  fof(f356,plain,(
% 3.22/0.82    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl4_37),
% 3.22/0.82    inference(avatar_component_clause,[],[f354])).
% 3.22/0.82  fof(f459,plain,(
% 3.22/0.82    ~r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~r1_tarski(sK1,sK2) | ~spl4_36),
% 3.22/0.82    inference(forward_demodulation,[],[f44,f348])).
% 3.22/0.82  fof(f348,plain,(
% 3.22/0.82    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl4_36),
% 3.22/0.82    inference(avatar_component_clause,[],[f346])).
% 3.22/0.82  fof(f44,plain,(
% 3.22/0.82    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 3.22/0.82    inference(cnf_transformation,[],[f32])).
% 3.22/0.82  fof(f32,plain,(
% 3.22/0.82    ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 3.22/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f31,f30])).
% 3.22/0.82  fof(f30,plain,(
% 3.22/0.82    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 3.22/0.82    introduced(choice_axiom,[])).
% 3.22/0.82  fof(f31,plain,(
% 3.22/0.82    ? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 3.22/0.82    introduced(choice_axiom,[])).
% 3.22/0.82  fof(f29,plain,(
% 3.22/0.82    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.82    inference(flattening,[],[f28])).
% 3.22/0.82  fof(f28,plain,(
% 3.22/0.82    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.82    inference(nnf_transformation,[],[f20])).
% 3.22/0.82  fof(f20,plain,(
% 3.22/0.82    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.82    inference(ennf_transformation,[],[f19])).
% 3.22/0.82  fof(f19,negated_conjecture,(
% 3.22/0.82    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.22/0.82    inference(negated_conjecture,[],[f18])).
% 3.22/0.82  fof(f18,conjecture,(
% 3.22/0.82    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.22/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 3.22/0.82  fof(f421,plain,(
% 3.22/0.82    spl4_41 | ~spl4_36 | ~spl4_37 | ~spl4_38),
% 3.22/0.82    inference(avatar_split_clause,[],[f378,f366,f354,f346,f418])).
% 3.22/0.82  fof(f366,plain,(
% 3.22/0.82    spl4_38 <=> r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(k3_subset_1(sK0,sK1)))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 3.22/0.82  fof(f378,plain,(
% 3.22/0.82    r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) | (~spl4_36 | ~spl4_37 | ~spl4_38)),
% 3.22/0.82    inference(forward_demodulation,[],[f377,f356])).
% 3.22/0.82  fof(f377,plain,(
% 3.22/0.82    r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) | (~spl4_36 | ~spl4_38)),
% 3.22/0.82    inference(forward_demodulation,[],[f368,f348])).
% 3.22/0.82  fof(f368,plain,(
% 3.22/0.82    r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(k3_subset_1(sK0,sK1))) | ~spl4_38),
% 3.22/0.82    inference(avatar_component_clause,[],[f366])).
% 3.22/0.82  fof(f399,plain,(
% 3.22/0.82    spl4_39 | ~spl4_2 | ~spl4_28 | ~spl4_29),
% 3.22/0.82    inference(avatar_split_clause,[],[f303,f268,f264,f82,f396])).
% 3.22/0.82  fof(f82,plain,(
% 3.22/0.82    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 3.22/0.82  fof(f268,plain,(
% 3.22/0.82    spl4_29 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 3.22/0.82  fof(f303,plain,(
% 3.22/0.82    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | (~spl4_2 | ~spl4_28 | ~spl4_29)),
% 3.22/0.82    inference(forward_demodulation,[],[f298,f292])).
% 3.22/0.82  fof(f292,plain,(
% 3.22/0.82    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | (~spl4_2 | ~spl4_28)),
% 3.22/0.82    inference(unit_resulting_resolution,[],[f84,f265])).
% 3.22/0.82  fof(f84,plain,(
% 3.22/0.82    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_2),
% 3.22/0.82    inference(avatar_component_clause,[],[f82])).
% 3.22/0.82  fof(f298,plain,(
% 3.22/0.82    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) | (~spl4_2 | ~spl4_29)),
% 3.22/0.82    inference(unit_resulting_resolution,[],[f84,f269])).
% 3.22/0.82  fof(f269,plain,(
% 3.22/0.82    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_29),
% 3.22/0.82    inference(avatar_component_clause,[],[f268])).
% 3.22/0.82  fof(f369,plain,(
% 3.22/0.82    spl4_38 | ~spl4_4 | ~spl4_14),
% 3.22/0.82    inference(avatar_split_clause,[],[f177,f135,f91,f366])).
% 3.22/0.82  fof(f91,plain,(
% 3.22/0.82    spl4_4 <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 3.22/0.82  fof(f177,plain,(
% 3.22/0.82    r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(k3_subset_1(sK0,sK1))) | (~spl4_4 | ~spl4_14)),
% 3.22/0.82    inference(unit_resulting_resolution,[],[f93,f136])).
% 3.22/0.82  fof(f93,plain,(
% 3.22/0.82    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~spl4_4),
% 3.22/0.82    inference(avatar_component_clause,[],[f91])).
% 3.22/0.82  fof(f357,plain,(
% 3.22/0.82    spl4_37 | ~spl4_2 | ~spl4_28),
% 3.22/0.82    inference(avatar_split_clause,[],[f292,f264,f82,f354])).
% 3.22/0.82  fof(f349,plain,(
% 3.22/0.82    spl4_36 | ~spl4_1 | ~spl4_28),
% 3.22/0.82    inference(avatar_split_clause,[],[f291,f264,f77,f346])).
% 3.22/0.82  fof(f77,plain,(
% 3.22/0.82    spl4_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 3.22/0.82  fof(f291,plain,(
% 3.22/0.82    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | (~spl4_1 | ~spl4_28)),
% 3.22/0.82    inference(unit_resulting_resolution,[],[f79,f265])).
% 3.22/0.82  fof(f79,plain,(
% 3.22/0.82    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_1),
% 3.22/0.82    inference(avatar_component_clause,[],[f77])).
% 3.22/0.82  fof(f339,plain,(
% 3.22/0.82    spl4_35 | spl4_3 | ~spl4_21),
% 3.22/0.82    inference(avatar_split_clause,[],[f219,f163,f87,f337])).
% 3.22/0.82  fof(f163,plain,(
% 3.22/0.82    spl4_21 <=> ! [X1,X0,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 3.22/0.82  fof(f219,plain,(
% 3.22/0.82    ( ! [X0] : (~r1_tarski(sK1,k4_xboole_0(sK2,X0))) ) | (spl4_3 | ~spl4_21)),
% 3.22/0.82    inference(unit_resulting_resolution,[],[f88,f164])).
% 3.22/0.82  fof(f164,plain,(
% 3.22/0.82    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) ) | ~spl4_21),
% 3.22/0.82    inference(avatar_component_clause,[],[f163])).
% 3.22/0.82  fof(f88,plain,(
% 3.22/0.82    ~r1_tarski(sK1,sK2) | spl4_3),
% 3.22/0.82    inference(avatar_component_clause,[],[f87])).
% 3.22/0.82  fof(f326,plain,(
% 3.22/0.82    spl4_33 | ~spl4_15 | ~spl4_30),
% 3.22/0.82    inference(avatar_split_clause,[],[f318,f272,f139,f323])).
% 3.22/0.82  fof(f272,plain,(
% 3.22/0.82    spl4_30 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 3.22/0.82  fof(f318,plain,(
% 3.22/0.82    r1_tarski(sK1,sK0) | (~spl4_15 | ~spl4_30)),
% 3.22/0.82    inference(unit_resulting_resolution,[],[f274,f140])).
% 3.22/0.82  fof(f274,plain,(
% 3.22/0.82    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_30),
% 3.22/0.82    inference(avatar_component_clause,[],[f272])).
% 3.22/0.82  fof(f275,plain,(
% 3.22/0.82    spl4_30 | ~spl4_1 | ~spl4_5 | ~spl4_16),
% 3.22/0.82    inference(avatar_split_clause,[],[f197,f143,f98,f77,f272])).
% 3.22/0.82  fof(f143,plain,(
% 3.22/0.82    spl4_16 <=> ! [X1,X0] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.22/0.82    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 3.22/0.82  fof(f197,plain,(
% 3.22/0.82    r2_hidden(sK1,k1_zfmisc_1(sK0)) | (~spl4_1 | ~spl4_5 | ~spl4_16)),
% 3.22/0.82    inference(unit_resulting_resolution,[],[f99,f79,f144])).
% 3.22/0.82  fof(f144,plain,(
% 3.22/0.82    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) ) | ~spl4_16),
% 3.22/0.82    inference(avatar_component_clause,[],[f143])).
% 3.22/0.82  fof(f270,plain,(
% 3.22/0.82    spl4_29),
% 3.22/0.82    inference(avatar_split_clause,[],[f59,f268])).
% 3.22/0.82  fof(f59,plain,(
% 3.22/0.82    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.82    inference(cnf_transformation,[],[f25])).
% 3.22/0.82  fof(f25,plain,(
% 3.22/0.82    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.82    inference(ennf_transformation,[],[f17])).
% 3.22/0.82  fof(f17,axiom,(
% 3.22/0.82    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.22/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 3.22/0.82  fof(f266,plain,(
% 3.22/0.82    spl4_28),
% 3.22/0.82    inference(avatar_split_clause,[],[f58,f264])).
% 3.22/0.82  fof(f58,plain,(
% 3.22/0.82    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.82    inference(cnf_transformation,[],[f24])).
% 3.22/0.82  fof(f24,plain,(
% 3.22/0.82    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.82    inference(ennf_transformation,[],[f15])).
% 3.22/0.82  fof(f15,axiom,(
% 3.22/0.82    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.22/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 3.22/0.82  fof(f239,plain,(
% 3.22/0.82    spl4_27),
% 3.22/0.82    inference(avatar_split_clause,[],[f69,f237])).
% 3.22/0.82  fof(f69,plain,(
% 3.22/0.82    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 3.22/0.82    inference(cnf_transformation,[],[f26])).
% 3.22/0.82  fof(f26,plain,(
% 3.22/0.82    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 3.22/0.82    inference(ennf_transformation,[],[f8])).
% 3.22/0.82  fof(f8,axiom,(
% 3.22/0.82    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)))),
% 3.22/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).
% 3.22/0.82  fof(f188,plain,(
% 3.22/0.82    spl4_24),
% 3.22/0.82    inference(avatar_split_clause,[],[f50,f186])).
% 3.22/0.82  fof(f50,plain,(
% 3.22/0.82    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.22/0.82    inference(cnf_transformation,[],[f11])).
% 3.22/0.82  fof(f11,axiom,(
% 3.22/0.82    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.22/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.22/0.82  fof(f169,plain,(
% 3.22/0.82    spl4_22),
% 3.22/0.82    inference(avatar_split_clause,[],[f71,f167])).
% 3.22/0.82  fof(f71,plain,(
% 3.22/0.82    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 3.22/0.82    inference(cnf_transformation,[],[f27])).
% 3.22/0.82  fof(f27,plain,(
% 3.22/0.82    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.22/0.82    inference(ennf_transformation,[],[f5])).
% 3.22/0.82  fof(f5,axiom,(
% 3.22/0.82    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.22/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 3.22/0.82  fof(f165,plain,(
% 3.22/0.82    spl4_21),
% 3.22/0.82    inference(avatar_split_clause,[],[f70,f163])).
% 3.22/0.82  fof(f70,plain,(
% 3.22/0.82    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 3.22/0.82    inference(cnf_transformation,[],[f27])).
% 3.22/0.82  fof(f157,plain,(
% 3.22/0.82    spl4_19),
% 3.22/0.82    inference(avatar_split_clause,[],[f63,f155])).
% 3.22/0.82  fof(f63,plain,(
% 3.22/0.82    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.22/0.82    inference(cnf_transformation,[],[f36])).
% 3.22/0.82  fof(f36,plain,(
% 3.22/0.82    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.22/0.82    inference(nnf_transformation,[],[f12])).
% 3.22/0.82  fof(f12,axiom,(
% 3.22/0.82    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.22/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 3.22/0.82  fof(f153,plain,(
% 3.22/0.82    spl4_18),
% 3.22/0.82    inference(avatar_split_clause,[],[f57,f151])).
% 3.22/0.82  fof(f57,plain,(
% 3.22/0.82    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.22/0.82    inference(cnf_transformation,[],[f23])).
% 3.22/0.82  fof(f23,plain,(
% 3.22/0.82    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.22/0.82    inference(ennf_transformation,[],[f6])).
% 3.22/0.82  fof(f6,axiom,(
% 3.22/0.82    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.22/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.22/0.82  fof(f149,plain,(
% 3.22/0.82    spl4_17),
% 3.22/0.82    inference(avatar_split_clause,[],[f53,f147])).
% 3.22/0.82  fof(f53,plain,(
% 3.22/0.82    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.22/0.82    inference(cnf_transformation,[],[f33])).
% 3.22/0.82  fof(f33,plain,(
% 3.22/0.82    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.22/0.82    inference(nnf_transformation,[],[f21])).
% 3.22/0.82  fof(f21,plain,(
% 3.22/0.82    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.22/0.82    inference(ennf_transformation,[],[f14])).
% 3.22/0.82  fof(f14,axiom,(
% 3.22/0.82    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.22/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 3.22/0.82  fof(f145,plain,(
% 3.22/0.82    spl4_16),
% 3.22/0.82    inference(avatar_split_clause,[],[f52,f143])).
% 3.22/0.82  fof(f52,plain,(
% 3.22/0.82    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.22/0.82    inference(cnf_transformation,[],[f33])).
% 3.22/0.82  fof(f141,plain,(
% 3.22/0.82    spl4_15),
% 3.22/0.82    inference(avatar_split_clause,[],[f75,f139])).
% 3.22/0.82  fof(f75,plain,(
% 3.22/0.82    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.22/0.82    inference(equality_resolution,[],[f65])).
% 3.22/0.82  fof(f65,plain,(
% 3.22/0.82    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.22/0.82    inference(cnf_transformation,[],[f40])).
% 3.22/0.82  fof(f40,plain,(
% 3.22/0.82    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.22/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 3.22/0.82  fof(f39,plain,(
% 3.22/0.82    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 3.22/0.82    introduced(choice_axiom,[])).
% 3.22/0.82  fof(f38,plain,(
% 3.22/0.82    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.22/0.82    inference(rectify,[],[f37])).
% 3.22/0.82  fof(f37,plain,(
% 3.22/0.82    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.22/0.82    inference(nnf_transformation,[],[f13])).
% 3.22/0.82  fof(f13,axiom,(
% 3.22/0.82    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.22/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 3.22/0.82  fof(f137,plain,(
% 3.22/0.82    spl4_14),
% 3.22/0.82    inference(avatar_split_clause,[],[f74,f135])).
% 3.22/0.82  fof(f74,plain,(
% 3.22/0.82    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.22/0.82    inference(equality_resolution,[],[f66])).
% 3.22/0.82  fof(f66,plain,(
% 3.22/0.82    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.22/0.82    inference(cnf_transformation,[],[f40])).
% 3.22/0.82  fof(f120,plain,(
% 3.22/0.82    spl4_10),
% 3.22/0.82    inference(avatar_split_clause,[],[f56,f118])).
% 3.22/0.82  fof(f56,plain,(
% 3.22/0.82    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.22/0.82    inference(cnf_transformation,[],[f22])).
% 3.22/0.82  fof(f22,plain,(
% 3.22/0.82    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.22/0.82    inference(ennf_transformation,[],[f2])).
% 3.22/0.82  fof(f2,axiom,(
% 3.22/0.82    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.22/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 3.22/0.82  fof(f116,plain,(
% 3.22/0.82    spl4_9),
% 3.22/0.82    inference(avatar_split_clause,[],[f48,f114])).
% 3.22/0.82  fof(f48,plain,(
% 3.22/0.82    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.22/0.82    inference(cnf_transformation,[],[f9])).
% 3.22/0.82  fof(f9,axiom,(
% 3.22/0.82    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.22/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.22/0.82  fof(f108,plain,(
% 3.22/0.82    spl4_7),
% 3.22/0.82    inference(avatar_split_clause,[],[f72,f106])).
% 3.22/0.82  fof(f72,plain,(
% 3.22/0.82    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.22/0.82    inference(equality_resolution,[],[f61])).
% 3.22/0.82  fof(f61,plain,(
% 3.22/0.82    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.22/0.82    inference(cnf_transformation,[],[f35])).
% 3.22/0.82  fof(f35,plain,(
% 3.22/0.82    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.22/0.82    inference(flattening,[],[f34])).
% 3.22/0.82  fof(f34,plain,(
% 3.22/0.82    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.22/0.82    inference(nnf_transformation,[],[f3])).
% 3.22/0.82  fof(f3,axiom,(
% 3.22/0.82    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.22/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.22/0.82  fof(f100,plain,(
% 3.22/0.82    spl4_5),
% 3.22/0.82    inference(avatar_split_clause,[],[f45,f98])).
% 3.22/0.82  fof(f45,plain,(
% 3.22/0.82    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.22/0.82    inference(cnf_transformation,[],[f16])).
% 3.22/0.82  fof(f16,axiom,(
% 3.22/0.82    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.22/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 3.22/0.82  fof(f94,plain,(
% 3.22/0.82    spl4_3 | spl4_4),
% 3.22/0.82    inference(avatar_split_clause,[],[f43,f91,f87])).
% 3.22/0.82  fof(f43,plain,(
% 3.22/0.82    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 3.22/0.82    inference(cnf_transformation,[],[f32])).
% 3.22/0.82  fof(f85,plain,(
% 3.22/0.82    spl4_2),
% 3.22/0.82    inference(avatar_split_clause,[],[f42,f82])).
% 3.22/0.82  fof(f42,plain,(
% 3.22/0.82    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 3.22/0.82    inference(cnf_transformation,[],[f32])).
% 3.22/0.82  fof(f80,plain,(
% 3.22/0.82    spl4_1),
% 3.22/0.82    inference(avatar_split_clause,[],[f41,f77])).
% 3.22/0.82  fof(f41,plain,(
% 3.22/0.82    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 3.22/0.82    inference(cnf_transformation,[],[f32])).
% 3.22/0.82  % SZS output end Proof for theBenchmark
% 3.22/0.82  % (25438)------------------------------
% 3.22/0.82  % (25438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.22/0.82  % (25438)Termination reason: Refutation
% 3.22/0.82  
% 3.22/0.82  % (25438)Memory used [KB]: 7547
% 3.22/0.82  % (25438)Time elapsed: 0.245 s
% 3.22/0.82  % (25438)------------------------------
% 3.22/0.82  % (25438)------------------------------
% 3.22/0.82  % (25407)Success in time 0.462 s
%------------------------------------------------------------------------------
