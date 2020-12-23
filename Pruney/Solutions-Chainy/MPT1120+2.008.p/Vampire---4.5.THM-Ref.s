%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 212 expanded)
%              Number of leaves         :   33 ( 101 expanded)
%              Depth                    :    8
%              Number of atoms          :  374 ( 648 expanded)
%              Number of equality atoms :   24 (  47 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1052,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f57,f61,f65,f69,f73,f77,f81,f88,f99,f103,f138,f150,f286,f727,f763,f898,f1039,f1045,f1051])).

fof(f1051,plain,
    ( ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_22
    | spl3_149 ),
    inference(avatar_contradiction_clause,[],[f1050])).

fof(f1050,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_22
    | spl3_149 ),
    inference(subsumption_resolution,[],[f1049,f52])).

fof(f52,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1049,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_22
    | spl3_149 ),
    inference(subsumption_resolution,[],[f1048,f148])).

fof(f148,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl3_22
  <=> ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f1048,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_12
    | spl3_149 ),
    inference(subsumption_resolution,[],[f1047,f42])).

fof(f42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1047,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_5
    | ~ spl3_12
    | spl3_149 ),
    inference(subsumption_resolution,[],[f1046,f86])).

fof(f86,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_12
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f1046,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_5
    | spl3_149 ),
    inference(resolution,[],[f1038,f56])).

fof(f56,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f1038,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2))
    | spl3_149 ),
    inference(avatar_component_clause,[],[f1036])).

fof(f1036,plain,
    ( spl3_149
  <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_149])])).

fof(f1045,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_22
    | spl3_148 ),
    inference(avatar_contradiction_clause,[],[f1044])).

fof(f1044,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_22
    | spl3_148 ),
    inference(subsumption_resolution,[],[f1043,f52])).

fof(f1043,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_22
    | spl3_148 ),
    inference(subsumption_resolution,[],[f1042,f148])).

fof(f1042,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | spl3_148 ),
    inference(subsumption_resolution,[],[f1041,f47])).

fof(f47,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1041,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_5
    | ~ spl3_6
    | spl3_148 ),
    inference(subsumption_resolution,[],[f1040,f60])).

fof(f60,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_6
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1040,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_5
    | spl3_148 ),
    inference(resolution,[],[f1034,f56])).

fof(f1034,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1))
    | spl3_148 ),
    inference(avatar_component_clause,[],[f1032])).

fof(f1032,plain,
    ( spl3_148
  <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_148])])).

fof(f1039,plain,
    ( ~ spl3_148
    | ~ spl3_149
    | ~ spl3_11
    | spl3_125 ),
    inference(avatar_split_clause,[],[f1030,f893,f79,f1036,f1032])).

fof(f79,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f893,plain,
    ( spl3_125
  <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_125])])).

fof(f1030,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1))
    | ~ spl3_11
    | spl3_125 ),
    inference(resolution,[],[f895,f80])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f895,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | spl3_125 ),
    inference(avatar_component_clause,[],[f893])).

fof(f898,plain,
    ( ~ spl3_125
    | spl3_1
    | ~ spl3_13
    | ~ spl3_93 ),
    inference(avatar_split_clause,[],[f897,f761,f97,f35,f893])).

fof(f35,plain,
    ( spl3_1
  <=> r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f97,plain,
    ( spl3_13
  <=> ! [X0] : k3_xboole_0(X0,sK2) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f761,plain,
    ( spl3_93
  <=> ! [X0] : k3_xboole_0(X0,k2_pre_topc(sK0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).

fof(f897,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | spl3_1
    | ~ spl3_13
    | ~ spl3_93 ),
    inference(forward_demodulation,[],[f890,f98])).

fof(f98,plain,
    ( ! [X0] : k3_xboole_0(X0,sK2) = k9_subset_1(u1_struct_0(sK0),X0,sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f97])).

fof(f890,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | spl3_1
    | ~ spl3_93 ),
    inference(superposition,[],[f37,f762])).

fof(f762,plain,
    ( ! [X0] : k3_xboole_0(X0,k2_pre_topc(sK0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2))
    | ~ spl3_93 ),
    inference(avatar_component_clause,[],[f761])).

fof(f37,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f763,plain,
    ( spl3_93
    | ~ spl3_2
    | ~ spl3_92 ),
    inference(avatar_split_clause,[],[f728,f725,f40,f761])).

fof(f725,plain,
    ( spl3_92
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(X1,k2_pre_topc(sK0,X0)) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).

fof(f728,plain,
    ( ! [X0] : k3_xboole_0(X0,k2_pre_topc(sK0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_92 ),
    inference(resolution,[],[f726,f42])).

fof(f726,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(X1,k2_pre_topc(sK0,X0)) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) )
    | ~ spl3_92 ),
    inference(avatar_component_clause,[],[f725])).

fof(f727,plain,
    ( spl3_92
    | ~ spl3_4
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f723,f284,f50,f725])).

fof(f284,plain,
    ( spl3_40
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k3_xboole_0(X2,k2_pre_topc(X1,X0)) = k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f723,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(X1,k2_pre_topc(sK0,X0)) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) )
    | ~ spl3_4
    | ~ spl3_40 ),
    inference(resolution,[],[f285,f52])).

fof(f285,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | k3_xboole_0(X2,k2_pre_topc(X1,X0)) = k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X0)) )
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f284])).

fof(f286,plain,
    ( spl3_40
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f282,f75,f67,f284])).

fof(f67,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f75,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f282,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k3_xboole_0(X2,k2_pre_topc(X1,X0)) = k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X0)) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(resolution,[],[f68,f76])).

fof(f76,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f150,plain,
    ( spl3_22
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f141,f136,f63,f147])).

fof(f63,plain,
    ( spl3_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f136,plain,
    ( spl3_20
  <=> ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f141,plain,
    ( ! [X1] : m1_subset_1(k3_xboole_0(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(superposition,[],[f137,f64])).

fof(f64,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f137,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f136])).

fof(f138,plain,
    ( spl3_20
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f134,f101,f71,f45,f136])).

fof(f71,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f101,plain,
    ( spl3_14
  <=> ! [X1] : k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK0),X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f134,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f133,f47])).

fof(f133,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(superposition,[],[f72,f102])).

fof(f102,plain,
    ( ! [X1] : k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK0),X1,sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f101])).

fof(f72,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f103,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f94,f75,f45,f101])).

fof(f94,plain,
    ( ! [X1] : k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK0),X1,sK1)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(resolution,[],[f76,f47])).

fof(f99,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f93,f75,f40,f97])).

fof(f93,plain,
    ( ! [X0] : k3_xboole_0(X0,sK2) = k9_subset_1(u1_struct_0(sK0),X0,sK2)
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(resolution,[],[f76,f42])).

fof(f88,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f83,f63,f59,f85])).

fof(f83,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(superposition,[],[f60,f64])).

fof(f81,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f33,f79])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f77,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f32,f75])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f73,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f31,f71])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f69,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f30,f67])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f65,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f61,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f28,f59])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f57,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f27,f55])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f53,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

fof(f48,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f40])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f26,f35])).

fof(f26,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:12:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (1729)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.45  % (1726)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.45  % (1727)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.46  % (1722)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.47  % (1721)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.48  % (1726)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f1052,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f57,f61,f65,f69,f73,f77,f81,f88,f99,f103,f138,f150,f286,f727,f763,f898,f1039,f1045,f1051])).
% 0.21/0.48  fof(f1051,plain,(
% 0.21/0.48    ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_12 | ~spl3_22 | spl3_149),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f1050])).
% 0.21/0.48  fof(f1050,plain,(
% 0.21/0.48    $false | (~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_12 | ~spl3_22 | spl3_149)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1049,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    l1_pre_topc(sK0) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl3_4 <=> l1_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f1049,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | (~spl3_2 | ~spl3_5 | ~spl3_12 | ~spl3_22 | spl3_149)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1048,f148])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f147])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    spl3_22 <=> ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.48  fof(f1048,plain,(
% 0.21/0.48    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_2 | ~spl3_5 | ~spl3_12 | spl3_149)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1047,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f1047,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_5 | ~spl3_12 | spl3_149)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1046,f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | ~spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl3_12 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f1046,plain,(
% 0.21/0.48    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_5 | spl3_149)),
% 0.21/0.48    inference(resolution,[],[f1038,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl3_5 <=> ! [X1,X0,X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f1038,plain,(
% 0.21/0.48    ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2)) | spl3_149),
% 0.21/0.48    inference(avatar_component_clause,[],[f1036])).
% 0.21/0.48  fof(f1036,plain,(
% 0.21/0.48    spl3_149 <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_149])])).
% 0.21/0.48  fof(f1045,plain,(
% 0.21/0.48    ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_22 | spl3_148),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f1044])).
% 0.21/0.48  fof(f1044,plain,(
% 0.21/0.48    $false | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_22 | spl3_148)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1043,f52])).
% 0.21/0.48  fof(f1043,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | (~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_22 | spl3_148)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1042,f148])).
% 0.21/0.48  fof(f1042,plain,(
% 0.21/0.48    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_3 | ~spl3_5 | ~spl3_6 | spl3_148)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1041,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f1041,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_5 | ~spl3_6 | spl3_148)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1040,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl3_6 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f1040,plain,(
% 0.21/0.48    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_5 | spl3_148)),
% 0.21/0.48    inference(resolution,[],[f1034,f56])).
% 0.21/0.48  fof(f1034,plain,(
% 0.21/0.48    ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1)) | spl3_148),
% 0.21/0.48    inference(avatar_component_clause,[],[f1032])).
% 0.21/0.48  fof(f1032,plain,(
% 0.21/0.48    spl3_148 <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_148])])).
% 0.21/0.48  fof(f1039,plain,(
% 0.21/0.48    ~spl3_148 | ~spl3_149 | ~spl3_11 | spl3_125),
% 0.21/0.48    inference(avatar_split_clause,[],[f1030,f893,f79,f1036,f1032])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl3_11 <=> ! [X1,X0,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f893,plain,(
% 0.21/0.48    spl3_125 <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_125])])).
% 0.21/0.48  fof(f1030,plain,(
% 0.21/0.48    ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2)) | ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1)) | (~spl3_11 | spl3_125)),
% 0.21/0.48    inference(resolution,[],[f895,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f895,plain,(
% 0.21/0.48    ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) | spl3_125),
% 0.21/0.48    inference(avatar_component_clause,[],[f893])).
% 0.21/0.48  fof(f898,plain,(
% 0.21/0.48    ~spl3_125 | spl3_1 | ~spl3_13 | ~spl3_93),
% 0.21/0.48    inference(avatar_split_clause,[],[f897,f761,f97,f35,f893])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    spl3_1 <=> r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl3_13 <=> ! [X0] : k3_xboole_0(X0,sK2) = k9_subset_1(u1_struct_0(sK0),X0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.48  fof(f761,plain,(
% 0.21/0.48    spl3_93 <=> ! [X0] : k3_xboole_0(X0,k2_pre_topc(sK0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).
% 0.21/0.48  fof(f897,plain,(
% 0.21/0.48    ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) | (spl3_1 | ~spl3_13 | ~spl3_93)),
% 0.21/0.48    inference(forward_demodulation,[],[f890,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(X0,sK2) = k9_subset_1(u1_struct_0(sK0),X0,sK2)) ) | ~spl3_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f97])).
% 0.21/0.48  fof(f890,plain,(
% 0.21/0.48    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) | (spl3_1 | ~spl3_93)),
% 0.21/0.48    inference(superposition,[],[f37,f762])).
% 0.21/0.48  fof(f762,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(X0,k2_pre_topc(sK0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2))) ) | ~spl3_93),
% 0.21/0.48    inference(avatar_component_clause,[],[f761])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f35])).
% 0.21/0.48  fof(f763,plain,(
% 0.21/0.48    spl3_93 | ~spl3_2 | ~spl3_92),
% 0.21/0.48    inference(avatar_split_clause,[],[f728,f725,f40,f761])).
% 0.21/0.48  fof(f725,plain,(
% 0.21/0.48    spl3_92 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_xboole_0(X1,k2_pre_topc(sK0,X0)) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).
% 0.21/0.48  fof(f728,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(X0,k2_pre_topc(sK0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2))) ) | (~spl3_2 | ~spl3_92)),
% 0.21/0.48    inference(resolution,[],[f726,f42])).
% 0.21/0.48  fof(f726,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_xboole_0(X1,k2_pre_topc(sK0,X0)) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0))) ) | ~spl3_92),
% 0.21/0.48    inference(avatar_component_clause,[],[f725])).
% 0.21/0.48  fof(f727,plain,(
% 0.21/0.48    spl3_92 | ~spl3_4 | ~spl3_40),
% 0.21/0.48    inference(avatar_split_clause,[],[f723,f284,f50,f725])).
% 0.21/0.48  fof(f284,plain,(
% 0.21/0.48    spl3_40 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k3_xboole_0(X2,k2_pre_topc(X1,X0)) = k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.48  fof(f723,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_xboole_0(X1,k2_pre_topc(sK0,X0)) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0))) ) | (~spl3_4 | ~spl3_40)),
% 0.21/0.48    inference(resolution,[],[f285,f52])).
% 0.21/0.48  fof(f285,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k3_xboole_0(X2,k2_pre_topc(X1,X0)) = k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X0))) ) | ~spl3_40),
% 0.21/0.48    inference(avatar_component_clause,[],[f284])).
% 0.21/0.48  fof(f286,plain,(
% 0.21/0.48    spl3_40 | ~spl3_8 | ~spl3_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f282,f75,f67,f284])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl3_8 <=> ! [X1,X0] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl3_10 <=> ! [X1,X0,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  fof(f282,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k3_xboole_0(X2,k2_pre_topc(X1,X0)) = k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X0))) ) | (~spl3_8 | ~spl3_10)),
% 0.21/0.48    inference(resolution,[],[f68,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)) ) | ~spl3_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f75])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f67])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    spl3_22 | ~spl3_7 | ~spl3_20),
% 0.21/0.48    inference(avatar_split_clause,[],[f141,f136,f63,f147])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl3_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    spl3_20 <=> ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ( ! [X1] : (m1_subset_1(k3_xboole_0(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_7 | ~spl3_20)),
% 0.21/0.48    inference(superposition,[],[f137,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f63])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f136])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    spl3_20 | ~spl3_3 | ~spl3_9 | ~spl3_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f134,f101,f71,f45,f136])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl3_9 <=> ! [X1,X0,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl3_14 <=> ! [X1] : k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK0),X1,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_3 | ~spl3_9 | ~spl3_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f133,f47])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_9 | ~spl3_14)),
% 0.21/0.48    inference(superposition,[],[f72,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X1] : (k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK0),X1,sK1)) ) | ~spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f101])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f71])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl3_14 | ~spl3_3 | ~spl3_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f94,f75,f45,f101])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ( ! [X1] : (k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK0),X1,sK1)) ) | (~spl3_3 | ~spl3_10)),
% 0.21/0.48    inference(resolution,[],[f76,f47])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl3_13 | ~spl3_2 | ~spl3_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f93,f75,f40,f97])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(X0,sK2) = k9_subset_1(u1_struct_0(sK0),X0,sK2)) ) | (~spl3_2 | ~spl3_10)),
% 0.21/0.48    inference(resolution,[],[f76,f42])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl3_12 | ~spl3_6 | ~spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f83,f63,f59,f85])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | (~spl3_6 | ~spl3_7)),
% 0.21/0.48    inference(superposition,[],[f60,f64])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f79])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl3_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f75])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f71])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f67])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f63])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f59])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f55])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f23,f50])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ((~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f21,f20,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f45])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f40])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ~spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f35])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (1726)------------------------------
% 0.21/0.49  % (1726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1726)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (1726)Memory used [KB]: 11385
% 0.21/0.49  % (1726)Time elapsed: 0.057 s
% 0.21/0.49  % (1726)------------------------------
% 0.21/0.49  % (1726)------------------------------
% 0.21/0.49  % (1731)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.49  % (1719)Success in time 0.132 s
%------------------------------------------------------------------------------
