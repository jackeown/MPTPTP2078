%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:53 EST 2020

% Result     : Theorem 2.58s
% Output     : Refutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  376 (1995 expanded)
%              Number of leaves         :  103 ( 767 expanded)
%              Depth                    :   15
%              Number of atoms          : 1536 (5887 expanded)
%              Number of equality atoms :  114 (1077 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1144,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f62,f67,f75,f80,f94,f100,f106,f112,f118,f124,f162,f171,f182,f187,f209,f214,f218,f222,f226,f230,f234,f238,f245,f260,f265,f269,f273,f277,f281,f286,f300,f306,f310,f314,f318,f322,f323,f330,f335,f339,f365,f378,f391,f398,f399,f406,f407,f412,f419,f424,f436,f442,f633,f637,f644,f648,f889,f919,f1025,f1029,f1033,f1037,f1041,f1045,f1049,f1053,f1057,f1061,f1065,f1069,f1073,f1077,f1081,f1085,f1089,f1093,f1097,f1101,f1105,f1109,f1113,f1117,f1121,f1125,f1129,f1133,f1137,f1142,f1143])).

fof(f1143,plain,
    ( spl3_54
    | ~ spl3_62
    | ~ spl3_49
    | ~ spl3_53
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f930,f433,f409,f375,f886,f421])).

fof(f421,plain,
    ( spl3_54
  <=> k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f886,plain,
    ( spl3_62
  <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f375,plain,
    ( spl3_49
  <=> k3_xboole_0(sK2,sK1) = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f409,plain,
    ( spl3_53
  <=> m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f433,plain,
    ( spl3_55
  <=> r1_tarski(k3_xboole_0(sK1,sK2),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f930,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_49
    | ~ spl3_53
    | ~ spl3_55 ),
    inference(resolution,[],[f844,f435])).

fof(f435,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f433])).

fof(f844,plain,
    ( ! [X28] :
        ( ~ r1_tarski(k3_xboole_0(sK1,sK2),X28)
        | ~ r1_tarski(X28,k3_xboole_0(sK1,sK2))
        | k3_xboole_0(sK1,sK2) = X28 )
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f843,f376])).

fof(f376,plain,
    ( k3_xboole_0(sK2,sK1) = k3_xboole_0(sK1,sK2)
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f375])).

fof(f843,plain,
    ( ! [X28] :
        ( ~ r1_tarski(X28,k3_xboole_0(sK1,sK2))
        | k3_xboole_0(sK1,sK2) = X28
        | ~ r1_tarski(k3_xboole_0(sK2,sK1),X28) )
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f842,f376])).

fof(f842,plain,
    ( ! [X28] :
        ( k3_xboole_0(sK1,sK2) = X28
        | ~ r1_tarski(X28,k3_xboole_0(sK2,sK1))
        | ~ r1_tarski(k3_xboole_0(sK2,sK1),X28) )
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f834,f376])).

fof(f834,plain,
    ( ! [X28] :
        ( k3_xboole_0(sK2,sK1) = X28
        | ~ r1_tarski(X28,k3_xboole_0(sK2,sK1))
        | ~ r1_tarski(k3_xboole_0(sK2,sK1),X28) )
    | ~ spl3_53 ),
    inference(resolution,[],[f802,f411])).

fof(f411,plain,
    ( m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f409])).

fof(f802,plain,(
    ! [X12,X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X12))
      | X10 = X11
      | ~ r1_tarski(X11,X10)
      | ~ r1_tarski(X10,X11) ) ),
    inference(superposition,[],[f799,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f799,plain,(
    ! [X6,X4,X5] :
      ( k3_xboole_0(X5,X4) = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(X6))
      | ~ r1_tarski(X4,X5) ) ),
    inference(global_subsumption,[],[f84,f785])).

fof(f785,plain,(
    ! [X6,X4,X5] :
      ( k3_xboole_0(X5,X4) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X6))
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f142,f34])).

fof(f142,plain,(
    ! [X10,X11,X9] :
      ( k3_xboole_0(X10,X11) = k3_xboole_0(X11,X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | ~ m1_subset_1(X11,k1_zfmisc_1(X9)) ) ),
    inference(superposition,[],[f133,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f133,plain,(
    ! [X6,X8,X7] :
      ( k3_xboole_0(X7,X8) = k9_subset_1(X6,X8,X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X6)) ) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X6,X8,X7] :
      ( k3_xboole_0(X7,X8) = k9_subset_1(X6,X8,X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X6)) ) ),
    inference(superposition,[],[f37,f36])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,k1_zfmisc_1(X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f82,f34])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f35,f36])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f1142,plain,
    ( ~ spl3_92
    | spl3_54
    | ~ spl3_62
    | ~ spl3_9
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f931,f409,f375,f92,f886,f421,f1139])).

fof(f1139,plain,
    ( spl3_92
  <=> r1_tarski(k3_xboole_0(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).

fof(f92,plain,
    ( spl3_9
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | r1_tarski(X0,k2_pre_topc(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f931,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ spl3_9
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(resolution,[],[f844,f93])).

fof(f93,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_pre_topc(sK0,X0))
        | ~ r1_tarski(X0,sK2) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f1137,plain,
    ( spl3_91
    | spl3_54
    | ~ spl3_62
    | ~ spl3_11
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f933,f409,f375,f104,f886,f421,f1135])).

fof(f1135,plain,
    ( spl3_91
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).

fof(f104,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,sK2)
        | r1_tarski(X1,k2_pre_topc(sK0,X1))
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f933,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
        | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0) )
    | ~ spl3_11
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(resolution,[],[f844,f105])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,k2_pre_topc(sK0,X1))
        | ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(X1,X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f1133,plain,
    ( spl3_90
    | spl3_54
    | ~ spl3_62
    | ~ spl3_12
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f934,f409,f375,f110,f886,f421,f1131])).

fof(f1131,plain,
    ( spl3_90
  <=> ! [X1] :
        ( ~ r1_tarski(X1,sK1)
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).

fof(f110,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,sK1)
        | r1_tarski(X1,k2_pre_topc(sK0,X1))
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f934,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
        | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(X1,sK1)
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X1) )
    | ~ spl3_12
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(resolution,[],[f844,f111])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,k2_pre_topc(sK0,X1))
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f1129,plain,
    ( spl3_89
    | spl3_54
    | ~ spl3_62
    | ~ spl3_13
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f935,f409,f375,f116,f886,f421,f1127])).

fof(f1127,plain,
    ( spl3_89
  <=> ! [X3,X2] :
        ( ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X3,sK2)
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).

fof(f116,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(X2,k2_pre_topc(sK0,X2))
        | ~ r1_tarski(X2,X0)
        | ~ r1_tarski(X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f935,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
        | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X2)
        | ~ r1_tarski(X3,sK2) )
    | ~ spl3_13
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(resolution,[],[f844,f117])).

fof(f117,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X2,k2_pre_topc(sK0,X2))
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X2,X0)
        | ~ r1_tarski(X1,sK2) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f116])).

fof(f1125,plain,
    ( spl3_88
    | spl3_54
    | ~ spl3_62
    | ~ spl3_14
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f936,f409,f375,f122,f886,f421,f1123])).

fof(f1123,plain,
    ( spl3_88
  <=> ! [X5,X4] :
        ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,sK1)
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).

fof(f122,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(X2,k2_pre_topc(sK0,X2))
        | ~ r1_tarski(X2,X0)
        | ~ r1_tarski(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f936,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
        | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(X4,X5)
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X4)
        | ~ r1_tarski(X5,sK1) )
    | ~ spl3_14
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(resolution,[],[f844,f123])).

fof(f123,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X2,k2_pre_topc(sK0,X2))
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X2,X0)
        | ~ r1_tarski(X1,sK1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f1121,plain,
    ( spl3_87
    | spl3_54
    | ~ spl3_62
    | ~ spl3_49
    | ~ spl3_53
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f937,f635,f409,f375,f886,f421,f1119])).

fof(f1119,plain,
    ( spl3_87
  <=> ! [X7,X8,X6] :
        ( ~ r1_tarski(X6,sK2)
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X7)
        | ~ r1_tarski(X8,X6)
        | ~ r1_tarski(X7,X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).

fof(f635,plain,
    ( spl3_58
  <=> ! [X5,X7,X4,X6] :
        ( ~ r1_tarski(X4,sK2)
        | r1_tarski(X7,k2_pre_topc(sK0,X7))
        | ~ r1_tarski(X7,X5)
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f937,plain,
    ( ! [X6,X8,X7] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
        | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(X6,sK2)
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X7)
        | ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X6) )
    | ~ spl3_49
    | ~ spl3_53
    | ~ spl3_58 ),
    inference(resolution,[],[f844,f636])).

fof(f636,plain,
    ( ! [X6,X4,X7,X5] :
        ( r1_tarski(X7,k2_pre_topc(sK0,X7))
        | ~ r1_tarski(X4,sK2)
        | ~ r1_tarski(X7,X5)
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X4) )
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f635])).

fof(f1117,plain,
    ( spl3_86
    | spl3_54
    | ~ spl3_62
    | ~ spl3_49
    | ~ spl3_53
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f938,f646,f409,f375,f886,f421,f1115])).

fof(f1115,plain,
    ( spl3_86
  <=> ! [X9,X11,X10] :
        ( ~ r1_tarski(X9,sK1)
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X10)
        | ~ r1_tarski(X11,X9)
        | ~ r1_tarski(X10,X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).

fof(f646,plain,
    ( spl3_60
  <=> ! [X5,X7,X4,X6] :
        ( ~ r1_tarski(X4,sK1)
        | r1_tarski(X7,k2_pre_topc(sK0,X7))
        | ~ r1_tarski(X7,X5)
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f938,plain,
    ( ! [X10,X11,X9] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
        | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(X9,sK1)
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X10)
        | ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X9) )
    | ~ spl3_49
    | ~ spl3_53
    | ~ spl3_60 ),
    inference(resolution,[],[f844,f647])).

fof(f647,plain,
    ( ! [X6,X4,X7,X5] :
        ( r1_tarski(X7,k2_pre_topc(sK0,X7))
        | ~ r1_tarski(X4,sK1)
        | ~ r1_tarski(X7,X5)
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X4) )
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f646])).

fof(f1113,plain,
    ( ~ spl3_6
    | spl3_85
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f1012,f232,f1111,f64])).

fof(f64,plain,
    ( spl3_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1111,plain,
    ( spl3_85
  <=> ! [X18,X19] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X19,X18)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X19),X18))
        | ~ v4_pre_topc(X18,sK0)
        | ~ r1_tarski(X18,sK1)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).

fof(f232,plain,
    ( spl3_27
  <=> ! [X10] :
        ( ~ v4_pre_topc(X10,sK0)
        | ~ r1_tarski(X10,sK1)
        | k2_pre_topc(sK0,X10) = X10 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f1012,plain,
    ( ! [X19,X18] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X19,X18)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X19),X18))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X18,sK1)
        | ~ v4_pre_topc(X18,sK0) )
    | ~ spl3_27 ),
    inference(superposition,[],[f33,f233])).

fof(f233,plain,
    ( ! [X10] :
        ( k2_pre_topc(sK0,X10) = X10
        | ~ r1_tarski(X10,sK1)
        | ~ v4_pre_topc(X10,sK0) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f232])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

fof(f1109,plain,
    ( ~ spl3_6
    | spl3_84
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f1011,f236,f1107,f64])).

fof(f1107,plain,
    ( spl3_84
  <=> ! [X16,X17] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X17,X16)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X17),X16))
        | ~ v4_pre_topc(X16,sK0)
        | ~ r1_tarski(X16,sK2)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).

fof(f236,plain,
    ( spl3_28
  <=> ! [X11] :
        ( ~ v4_pre_topc(X11,sK0)
        | ~ r1_tarski(X11,sK2)
        | k2_pre_topc(sK0,X11) = X11 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f1011,plain,
    ( ! [X17,X16] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X17,X16)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X17),X16))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X16,sK2)
        | ~ v4_pre_topc(X16,sK0) )
    | ~ spl3_28 ),
    inference(superposition,[],[f33,f237])).

fof(f237,plain,
    ( ! [X11] :
        ( k2_pre_topc(sK0,X11) = X11
        | ~ r1_tarski(X11,sK2)
        | ~ v4_pre_topc(X11,sK0) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f236])).

fof(f1105,plain,
    ( ~ spl3_6
    | spl3_83
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f1010,f224,f1103,f64])).

fof(f1103,plain,
    ( spl3_83
  <=> ! [X13,X15,X14] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X14,X13)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X14),X13))
        | ~ v4_pre_topc(X13,sK0)
        | ~ r1_tarski(X15,sK1)
        | ~ r1_tarski(X13,X15)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f224,plain,
    ( spl3_25
  <=> ! [X7,X6] :
        ( ~ v4_pre_topc(X6,sK0)
        | ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,sK1)
        | k2_pre_topc(sK0,X6) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f1010,plain,
    ( ! [X14,X15,X13] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X14,X13)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X14),X13))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X13,X15)
        | ~ r1_tarski(X15,sK1)
        | ~ v4_pre_topc(X13,sK0) )
    | ~ spl3_25 ),
    inference(superposition,[],[f33,f225])).

fof(f225,plain,
    ( ! [X6,X7] :
        ( k2_pre_topc(sK0,X6) = X6
        | ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,sK1)
        | ~ v4_pre_topc(X6,sK0) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f224])).

fof(f1101,plain,
    ( ~ spl3_6
    | spl3_82
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f1009,f228,f1099,f64])).

fof(f1099,plain,
    ( spl3_82
  <=> ! [X11,X10,X12] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X11,X10)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X11),X10))
        | ~ v4_pre_topc(X10,sK0)
        | ~ r1_tarski(X12,sK2)
        | ~ r1_tarski(X10,X12)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).

fof(f228,plain,
    ( spl3_26
  <=> ! [X9,X8] :
        ( ~ v4_pre_topc(X8,sK0)
        | ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,sK2)
        | k2_pre_topc(sK0,X8) = X8 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f1009,plain,
    ( ! [X12,X10,X11] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X11,X10)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X11),X10))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X10,X12)
        | ~ r1_tarski(X12,sK2)
        | ~ v4_pre_topc(X10,sK0) )
    | ~ spl3_26 ),
    inference(superposition,[],[f33,f229])).

fof(f229,plain,
    ( ! [X8,X9] :
        ( k2_pre_topc(sK0,X8) = X8
        | ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,sK2)
        | ~ v4_pre_topc(X8,sK0) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f228])).

fof(f1097,plain,
    ( ~ spl3_6
    | spl3_81
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f1008,f216,f1095,f64])).

fof(f1095,plain,
    ( spl3_81
  <=> ! [X9,X7,X8,X6] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X7,X6)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X7),X6))
        | ~ v4_pre_topc(X6,sK0)
        | ~ r1_tarski(X9,sK1)
        | ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X6,X8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).

fof(f216,plain,
    ( spl3_23
  <=> ! [X1,X0,X2] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X2,sK1)
        | k2_pre_topc(sK0,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f1008,plain,
    ( ! [X6,X8,X7,X9] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X7,X6)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X7),X6))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X6,X8)
        | ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,sK1)
        | ~ v4_pre_topc(X6,sK0) )
    | ~ spl3_23 ),
    inference(superposition,[],[f33,f217])).

fof(f217,plain,
    ( ! [X2,X0,X1] :
        ( k2_pre_topc(sK0,X0) = X0
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X2,sK1)
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f216])).

fof(f1093,plain,
    ( ~ spl3_6
    | spl3_80
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f1007,f220,f1091,f64])).

fof(f1091,plain,
    ( spl3_80
  <=> ! [X3,X5,X2,X4] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X3,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X3),X2))
        | ~ v4_pre_topc(X2,sK0)
        | ~ r1_tarski(X5,sK2)
        | ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X2,X4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).

fof(f220,plain,
    ( spl3_24
  <=> ! [X3,X5,X4] :
        ( ~ v4_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,X4)
        | ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,sK2)
        | k2_pre_topc(sK0,X3) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f1007,plain,
    ( ! [X4,X2,X5,X3] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X3,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X3),X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X2,X4)
        | ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,sK2)
        | ~ v4_pre_topc(X2,sK0) )
    | ~ spl3_24 ),
    inference(superposition,[],[f33,f221])).

fof(f221,plain,
    ( ! [X4,X5,X3] :
        ( k2_pre_topc(sK0,X3) = X3
        | ~ r1_tarski(X3,X4)
        | ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,sK2)
        | ~ v4_pre_topc(X3,sK0) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f220])).

fof(f1089,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | spl3_79
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f1006,f211,f1087,f59,f64])).

fof(f59,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f1087,plain,
    ( spl3_79
  <=> ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).

fof(f211,plain,
    ( spl3_22
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f1006,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_22 ),
    inference(superposition,[],[f33,f213])).

fof(f213,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f211])).

fof(f1085,plain,
    ( ~ spl3_6
    | ~ spl3_4
    | spl3_78
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f1005,f206,f1083,f54,f64])).

fof(f54,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1083,plain,
    ( spl3_78
  <=> ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f206,plain,
    ( spl3_21
  <=> sK2 = k2_pre_topc(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f1005,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_21 ),
    inference(superposition,[],[f33,f208])).

fof(f208,plain,
    ( sK2 = k2_pre_topc(sK0,sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f206])).

fof(f1081,plain,
    ( ~ spl3_6
    | spl3_77
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f1004,f232,f1079,f64])).

fof(f1079,plain,
    ( spl3_77
  <=> ! [X18,X19] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X18,X19)),k9_subset_1(u1_struct_0(sK0),X18,k2_pre_topc(sK0,X19)))
        | ~ v4_pre_topc(X18,sK0)
        | ~ r1_tarski(X18,sK1)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f1004,plain,
    ( ! [X19,X18] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X18,X19)),k9_subset_1(u1_struct_0(sK0),X18,k2_pre_topc(sK0,X19)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X18,sK1)
        | ~ v4_pre_topc(X18,sK0) )
    | ~ spl3_27 ),
    inference(superposition,[],[f33,f233])).

fof(f1077,plain,
    ( ~ spl3_6
    | spl3_76
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f1003,f236,f1075,f64])).

fof(f1075,plain,
    ( spl3_76
  <=> ! [X16,X17] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X16,X17)),k9_subset_1(u1_struct_0(sK0),X16,k2_pre_topc(sK0,X17)))
        | ~ v4_pre_topc(X16,sK0)
        | ~ r1_tarski(X16,sK2)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f1003,plain,
    ( ! [X17,X16] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X16,X17)),k9_subset_1(u1_struct_0(sK0),X16,k2_pre_topc(sK0,X17)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X16,sK2)
        | ~ v4_pre_topc(X16,sK0) )
    | ~ spl3_28 ),
    inference(superposition,[],[f33,f237])).

fof(f1073,plain,
    ( ~ spl3_6
    | spl3_75
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f1002,f224,f1071,f64])).

fof(f1071,plain,
    ( spl3_75
  <=> ! [X13,X15,X14] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X13,X14)),k9_subset_1(u1_struct_0(sK0),X13,k2_pre_topc(sK0,X14)))
        | ~ v4_pre_topc(X13,sK0)
        | ~ r1_tarski(X15,sK1)
        | ~ r1_tarski(X13,X15)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f1002,plain,
    ( ! [X14,X15,X13] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X13,X14)),k9_subset_1(u1_struct_0(sK0),X13,k2_pre_topc(sK0,X14)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X13,X15)
        | ~ r1_tarski(X15,sK1)
        | ~ v4_pre_topc(X13,sK0) )
    | ~ spl3_25 ),
    inference(superposition,[],[f33,f225])).

fof(f1069,plain,
    ( ~ spl3_6
    | spl3_74
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f1001,f228,f1067,f64])).

fof(f1067,plain,
    ( spl3_74
  <=> ! [X11,X10,X12] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X10,X11)),k9_subset_1(u1_struct_0(sK0),X10,k2_pre_topc(sK0,X11)))
        | ~ v4_pre_topc(X10,sK0)
        | ~ r1_tarski(X12,sK2)
        | ~ r1_tarski(X10,X12)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f1001,plain,
    ( ! [X12,X10,X11] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X10,X11)),k9_subset_1(u1_struct_0(sK0),X10,k2_pre_topc(sK0,X11)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X10,X12)
        | ~ r1_tarski(X12,sK2)
        | ~ v4_pre_topc(X10,sK0) )
    | ~ spl3_26 ),
    inference(superposition,[],[f33,f229])).

fof(f1065,plain,
    ( ~ spl3_6
    | spl3_73
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f1000,f216,f1063,f64])).

fof(f1063,plain,
    ( spl3_73
  <=> ! [X9,X7,X8,X6] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X6,X7)),k9_subset_1(u1_struct_0(sK0),X6,k2_pre_topc(sK0,X7)))
        | ~ v4_pre_topc(X6,sK0)
        | ~ r1_tarski(X9,sK1)
        | ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X6,X8)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f1000,plain,
    ( ! [X6,X8,X7,X9] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X6,X7)),k9_subset_1(u1_struct_0(sK0),X6,k2_pre_topc(sK0,X7)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X6,X8)
        | ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,sK1)
        | ~ v4_pre_topc(X6,sK0) )
    | ~ spl3_23 ),
    inference(superposition,[],[f33,f217])).

fof(f1061,plain,
    ( ~ spl3_6
    | spl3_72
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f999,f220,f1059,f64])).

fof(f1059,plain,
    ( spl3_72
  <=> ! [X3,X5,X2,X4] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X3)),k9_subset_1(u1_struct_0(sK0),X2,k2_pre_topc(sK0,X3)))
        | ~ v4_pre_topc(X2,sK0)
        | ~ r1_tarski(X5,sK2)
        | ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X2,X4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f999,plain,
    ( ! [X4,X2,X5,X3] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X3)),k9_subset_1(u1_struct_0(sK0),X2,k2_pre_topc(sK0,X3)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X2,X4)
        | ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,sK2)
        | ~ v4_pre_topc(X2,sK0) )
    | ~ spl3_24 ),
    inference(superposition,[],[f33,f221])).

fof(f1057,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | spl3_71
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f998,f211,f1055,f59,f64])).

fof(f1055,plain,
    ( spl3_71
  <=> ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X1)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f998,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X1)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_22 ),
    inference(superposition,[],[f33,f213])).

fof(f1053,plain,
    ( ~ spl3_6
    | ~ spl3_4
    | spl3_70
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f997,f206,f1051,f54,f64])).

fof(f1051,plain,
    ( spl3_70
  <=> ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)),k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f997,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)),k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_21 ),
    inference(superposition,[],[f33,f208])).

fof(f1049,plain,
    ( ~ spl3_6
    | spl3_69
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f996,f232,f1047,f64])).

fof(f1047,plain,
    ( spl3_69
  <=> ! [X16,X17] :
        ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X16,X17),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X16),k2_pre_topc(sK0,X17)))
        | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X16,X17),sK0)
        | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X16,X17),sK1)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f996,plain,
    ( ! [X17,X16] :
        ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X16,X17),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X16),k2_pre_topc(sK0,X17)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X16,X17),sK1)
        | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X16,X17),sK0) )
    | ~ spl3_27 ),
    inference(superposition,[],[f33,f233])).

fof(f1045,plain,
    ( ~ spl3_6
    | spl3_68
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f995,f236,f1043,f64])).

fof(f1043,plain,
    ( spl3_68
  <=> ! [X15,X14] :
        ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X14,X15),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X14),k2_pre_topc(sK0,X15)))
        | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X14,X15),sK0)
        | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X14,X15),sK2)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f995,plain,
    ( ! [X14,X15] :
        ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X14,X15),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X14),k2_pre_topc(sK0,X15)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X14,X15),sK2)
        | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X14,X15),sK0) )
    | ~ spl3_28 ),
    inference(superposition,[],[f33,f237])).

fof(f1041,plain,
    ( ~ spl3_6
    | spl3_67
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f994,f224,f1039,f64])).

fof(f1039,plain,
    ( spl3_67
  <=> ! [X11,X13,X12] :
        ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X11,X12),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X11),k2_pre_topc(sK0,X12)))
        | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X11,X12),sK0)
        | ~ r1_tarski(X13,sK1)
        | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X11,X12),X13)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f994,plain,
    ( ! [X12,X13,X11] :
        ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X11,X12),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X11),k2_pre_topc(sK0,X12)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X11,X12),X13)
        | ~ r1_tarski(X13,sK1)
        | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X11,X12),sK0) )
    | ~ spl3_25 ),
    inference(superposition,[],[f33,f225])).

fof(f1037,plain,
    ( ~ spl3_6
    | spl3_66
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f993,f228,f1035,f64])).

fof(f1035,plain,
    ( spl3_66
  <=> ! [X9,X8,X10] :
        ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X8,X9),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X8),k2_pre_topc(sK0,X9)))
        | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X8,X9),sK0)
        | ~ r1_tarski(X10,sK2)
        | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X8,X9),X10)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f993,plain,
    ( ! [X10,X8,X9] :
        ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X8,X9),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X8),k2_pre_topc(sK0,X9)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X8,X9),X10)
        | ~ r1_tarski(X10,sK2)
        | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X8,X9),sK0) )
    | ~ spl3_26 ),
    inference(superposition,[],[f33,f229])).

fof(f1033,plain,
    ( ~ spl3_6
    | spl3_65
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f992,f216,f1031,f64])).

fof(f1031,plain,
    ( spl3_65
  <=> ! [X5,X7,X4,X6] :
        ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X4,X5),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X4),k2_pre_topc(sK0,X5)))
        | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X4,X5),sK0)
        | ~ r1_tarski(X7,sK1)
        | ~ r1_tarski(X6,X7)
        | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X4,X5),X6)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f992,plain,
    ( ! [X6,X4,X7,X5] :
        ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X4,X5),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X4),k2_pre_topc(sK0,X5)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X4,X5),X6)
        | ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,sK1)
        | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X4,X5),sK0) )
    | ~ spl3_23 ),
    inference(superposition,[],[f33,f217])).

fof(f1029,plain,
    ( ~ spl3_6
    | spl3_64
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f991,f220,f1027,f64])).

fof(f1027,plain,
    ( spl3_64
  <=> ! [X1,X3,X0,X2] :
        ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,X1),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)))
        | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X0,X1),sK0)
        | ~ r1_tarski(X3,sK2)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,X1),X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f991,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,X1),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,X1),X2)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X3,sK2)
        | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X0,X1),sK0) )
    | ~ spl3_24 ),
    inference(superposition,[],[f33,f221])).

fof(f1025,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | ~ spl3_4
    | spl3_62
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_49
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f1024,f388,f375,f211,f206,f886,f54,f59,f64])).

fof(f388,plain,
    ( spl3_52
  <=> k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f1024,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_49
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f1023,f376])).

fof(f1023,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f1022,f389])).

fof(f389,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_xboole_0(sK2,sK1)
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f388])).

fof(f1022,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f1021,f213])).

fof(f1021,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_21
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f986,f208])).

fof(f986,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_52 ),
    inference(superposition,[],[f33,f389])).

fof(f919,plain,
    ( ~ spl3_63
    | ~ spl3_62
    | spl3_54
    | ~ spl3_5
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f907,f433,f59,f421,f886,f916])).

fof(f916,plain,
    ( spl3_63
  <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f907,plain,
    ( k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | ~ spl3_5
    | ~ spl3_55 ),
    inference(resolution,[],[f827,f435])).

fof(f827,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X3,X2)
        | X2 = X3
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X2,sK1) )
    | ~ spl3_5 ),
    inference(resolution,[],[f802,f86])).

fof(f86,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,sK1) )
    | ~ spl3_5 ),
    inference(resolution,[],[f84,f61])).

fof(f61,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f889,plain,
    ( ~ spl3_61
    | ~ spl3_62
    | spl3_54
    | ~ spl3_4
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f873,f433,f54,f421,f886,f882])).

fof(f882,plain,
    ( spl3_61
  <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f873,plain,
    ( k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),sK2)
    | ~ spl3_4
    | ~ spl3_55 ),
    inference(resolution,[],[f826,f435])).

fof(f826,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | X0 = X1
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X0,sK2) )
    | ~ spl3_4 ),
    inference(resolution,[],[f802,f85])).

fof(f85,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK2) )
    | ~ spl3_4 ),
    inference(resolution,[],[f84,f56])).

fof(f56,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f648,plain,
    ( ~ spl3_6
    | spl3_60
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f639,f59,f646,f64])).

fof(f639,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r1_tarski(X4,sK1)
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X4)
        | ~ r1_tarski(X7,X5)
        | r1_tarski(X7,k2_pre_topc(sK0,X7))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_5 ),
    inference(resolution,[],[f120,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f120,plain,
    ( ! [X6,X4,X5,X3] :
        ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X4,sK1)
        | ~ r1_tarski(X5,X3)
        | ~ r1_tarski(X3,X4)
        | ~ r1_tarski(X6,X5) )
    | ~ spl3_5 ),
    inference(resolution,[],[f108,f84])).

fof(f108,plain,
    ( ! [X4,X2,X3] :
        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,X2)
        | ~ r1_tarski(X2,sK1)
        | ~ r1_tarski(X4,X3) )
    | ~ spl3_5 ),
    inference(resolution,[],[f96,f84])).

fof(f96,plain,
    ( ! [X2,X1] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,sK1)
        | ~ r1_tarski(X2,X1) )
    | ~ spl3_5 ),
    inference(resolution,[],[f86,f84])).

fof(f644,plain,
    ( ~ spl3_6
    | spl3_59
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f638,f59,f642,f64])).

fof(f642,plain,
    ( spl3_59
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X0,sK1)
        | k2_pre_topc(sK0,X3) = X3
        | ~ v4_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,X1)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f638,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X2,X0)
        | ~ r1_tarski(X3,X1)
        | ~ v4_pre_topc(X3,sK0)
        | k2_pre_topc(sK0,X3) = X3
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_5 ),
    inference(resolution,[],[f120,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f637,plain,
    ( ~ spl3_6
    | spl3_58
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f628,f54,f635,f64])).

fof(f628,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r1_tarski(X4,sK2)
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X4)
        | ~ r1_tarski(X7,X5)
        | r1_tarski(X7,k2_pre_topc(sK0,X7))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f114,f30])).

fof(f114,plain,
    ( ! [X6,X4,X5,X3] :
        ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X4,sK2)
        | ~ r1_tarski(X5,X3)
        | ~ r1_tarski(X3,X4)
        | ~ r1_tarski(X6,X5) )
    | ~ spl3_4 ),
    inference(resolution,[],[f102,f84])).

fof(f102,plain,
    ( ! [X4,X2,X3] :
        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,X2)
        | ~ r1_tarski(X2,sK2)
        | ~ r1_tarski(X4,X3) )
    | ~ spl3_4 ),
    inference(resolution,[],[f90,f84])).

fof(f90,plain,
    ( ! [X2,X1] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,sK2)
        | ~ r1_tarski(X2,X1) )
    | ~ spl3_4 ),
    inference(resolution,[],[f85,f84])).

fof(f633,plain,
    ( ~ spl3_6
    | spl3_57
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f627,f54,f631,f64])).

fof(f631,plain,
    ( spl3_57
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X0,sK2)
        | k2_pre_topc(sK0,X3) = X3
        | ~ v4_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,X1)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f627,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X2,X0)
        | ~ r1_tarski(X3,X1)
        | ~ v4_pre_topc(X3,sK0)
        | k2_pre_topc(sK0,X3) = X3
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f114,f31])).

fof(f442,plain,
    ( spl3_56
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f429,f409,f375,f439])).

fof(f439,plain,
    ( spl3_56
  <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f429,plain,
    ( m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(superposition,[],[f411,f376])).

fof(f436,plain,
    ( ~ spl3_6
    | spl3_55
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f431,f409,f375,f433,f64])).

fof(f431,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_49
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f427,f376])).

fof(f427,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK1),k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_53 ),
    inference(resolution,[],[f411,f30])).

fof(f424,plain,
    ( ~ spl3_54
    | spl3_43
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f415,f375,f327,f421])).

fof(f327,plain,
    ( spl3_43
  <=> k3_xboole_0(sK2,sK1) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f415,plain,
    ( k3_xboole_0(sK1,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | spl3_43
    | ~ spl3_49 ),
    inference(superposition,[],[f329,f376])).

fof(f329,plain,
    ( k3_xboole_0(sK2,sK1) != k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))
    | spl3_43 ),
    inference(avatar_component_clause,[],[f327])).

fof(f419,plain,
    ( ~ spl3_47
    | spl3_45
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f414,f375,f358,f367])).

fof(f367,plain,
    ( spl3_47
  <=> v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f358,plain,
    ( spl3_45
  <=> v4_pre_topc(k3_xboole_0(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f414,plain,
    ( ~ v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | spl3_45
    | ~ spl3_49 ),
    inference(superposition,[],[f360,f376])).

fof(f360,plain,
    ( ~ v4_pre_topc(k3_xboole_0(sK2,sK1),sK0)
    | spl3_45 ),
    inference(avatar_component_clause,[],[f358])).

fof(f412,plain,
    ( ~ spl3_4
    | spl3_53
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f405,f388,f409,f54])).

fof(f405,plain,
    ( m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_52 ),
    inference(superposition,[],[f35,f389])).

fof(f407,plain,
    ( ~ spl3_4
    | spl3_49
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f404,f388,f375,f54])).

fof(f404,plain,
    ( k3_xboole_0(sK2,sK1) = k3_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_52 ),
    inference(superposition,[],[f36,f389])).

fof(f406,plain,
    ( ~ spl3_4
    | spl3_49
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f401,f388,f375,f54])).

fof(f401,plain,
    ( k3_xboole_0(sK2,sK1) = k3_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_52 ),
    inference(superposition,[],[f389,f36])).

fof(f399,plain,
    ( ~ spl3_4
    | ~ spl3_49
    | spl3_52 ),
    inference(avatar_split_clause,[],[f396,f388,f375,f54])).

fof(f396,plain,
    ( k3_xboole_0(sK2,sK1) != k3_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_52 ),
    inference(superposition,[],[f390,f36])).

fof(f390,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_xboole_0(sK2,sK1)
    | spl3_52 ),
    inference(avatar_component_clause,[],[f388])).

fof(f398,plain,
    ( ~ spl3_5
    | spl3_52 ),
    inference(avatar_split_clause,[],[f397,f388,f59])).

fof(f397,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_52 ),
    inference(trivial_inequality_removal,[],[f395])).

fof(f395,plain,
    ( k3_xboole_0(sK2,sK1) != k3_xboole_0(sK2,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_52 ),
    inference(superposition,[],[f390,f133])).

fof(f391,plain,
    ( ~ spl3_50
    | ~ spl3_51
    | ~ spl3_52
    | ~ spl3_27
    | spl3_29 ),
    inference(avatar_split_clause,[],[f349,f242,f232,f388,f384,f380])).

fof(f380,plain,
    ( spl3_50
  <=> v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f384,plain,
    ( spl3_51
  <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f242,plain,
    ( spl3_29
  <=> k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f349,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_xboole_0(sK2,sK1)
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl3_27
    | spl3_29 ),
    inference(superposition,[],[f244,f233])).

fof(f244,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_xboole_0(sK2,sK1)
    | spl3_29 ),
    inference(avatar_component_clause,[],[f242])).

fof(f378,plain,
    ( ~ spl3_47
    | ~ spl3_48
    | ~ spl3_49
    | ~ spl3_27
    | spl3_44 ),
    inference(avatar_split_clause,[],[f348,f332,f232,f375,f371,f367])).

fof(f371,plain,
    ( spl3_48
  <=> r1_tarski(k3_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f332,plain,
    ( spl3_44
  <=> k3_xboole_0(sK2,sK1) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f348,plain,
    ( k3_xboole_0(sK2,sK1) != k3_xboole_0(sK1,sK2)
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_27
    | spl3_44 ),
    inference(superposition,[],[f334,f233])).

fof(f334,plain,
    ( k3_xboole_0(sK2,sK1) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | spl3_44 ),
    inference(avatar_component_clause,[],[f332])).

fof(f365,plain,
    ( ~ spl3_45
    | ~ spl3_46
    | ~ spl3_27
    | spl3_43 ),
    inference(avatar_split_clause,[],[f355,f327,f232,f362,f358])).

fof(f362,plain,
    ( spl3_46
  <=> r1_tarski(k3_xboole_0(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f355,plain,
    ( ~ r1_tarski(k3_xboole_0(sK2,sK1),sK1)
    | ~ v4_pre_topc(k3_xboole_0(sK2,sK1),sK0)
    | ~ spl3_27
    | spl3_43 ),
    inference(trivial_inequality_removal,[],[f347])).

fof(f347,plain,
    ( k3_xboole_0(sK2,sK1) != k3_xboole_0(sK2,sK1)
    | ~ r1_tarski(k3_xboole_0(sK2,sK1),sK1)
    | ~ v4_pre_topc(k3_xboole_0(sK2,sK1),sK0)
    | ~ spl3_27
    | spl3_43 ),
    inference(superposition,[],[f329,f233])).

fof(f339,plain,
    ( ~ spl3_36
    | ~ spl3_21
    | spl3_43 ),
    inference(avatar_split_clause,[],[f338,f327,f206,f283])).

fof(f283,plain,
    ( spl3_36
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f338,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl3_21
    | spl3_43 ),
    inference(trivial_inequality_removal,[],[f337])).

fof(f337,plain,
    ( sK2 != sK2
    | ~ r1_tarski(sK2,sK1)
    | ~ spl3_21
    | spl3_43 ),
    inference(forward_demodulation,[],[f336,f208])).

fof(f336,plain,
    ( sK2 != k2_pre_topc(sK0,sK2)
    | ~ r1_tarski(sK2,sK1)
    | spl3_43 ),
    inference(superposition,[],[f329,f34])).

fof(f335,plain,
    ( ~ spl3_4
    | ~ spl3_44
    | spl3_29 ),
    inference(avatar_split_clause,[],[f325,f242,f332,f54])).

fof(f325,plain,
    ( k3_xboole_0(sK2,sK1) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_29 ),
    inference(superposition,[],[f244,f36])).

fof(f330,plain,
    ( ~ spl3_5
    | ~ spl3_43
    | spl3_29 ),
    inference(avatar_split_clause,[],[f324,f242,f327,f59])).

fof(f324,plain,
    ( k3_xboole_0(sK2,sK1) != k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_29 ),
    inference(superposition,[],[f244,f133])).

fof(f323,plain,
    ( ~ spl3_37
    | spl3_38
    | ~ spl3_9
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f295,f211,f92,f303,f297])).

fof(f297,plain,
    ( spl3_37
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f303,plain,
    ( spl3_38
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f295,plain,
    ( r1_tarski(sK1,sK1)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl3_9
    | ~ spl3_22 ),
    inference(superposition,[],[f93,f213])).

fof(f322,plain,
    ( spl3_42
    | spl3_38
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f293,f211,f104,f303,f320])).

fof(f320,plain,
    ( spl3_42
  <=> ! [X5] :
        ( ~ r1_tarski(X5,sK2)
        | ~ r1_tarski(sK1,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f293,plain,
    ( ! [X5] :
        ( r1_tarski(sK1,sK1)
        | ~ r1_tarski(X5,sK2)
        | ~ r1_tarski(sK1,X5) )
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(superposition,[],[f105,f213])).

fof(f318,plain,
    ( spl3_41
    | spl3_38
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f292,f211,f110,f303,f316])).

fof(f316,plain,
    ( spl3_41
  <=> ! [X4] :
        ( ~ r1_tarski(X4,sK1)
        | ~ r1_tarski(sK1,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f292,plain,
    ( ! [X4] :
        ( r1_tarski(sK1,sK1)
        | ~ r1_tarski(X4,sK1)
        | ~ r1_tarski(sK1,X4) )
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(superposition,[],[f111,f213])).

fof(f314,plain,
    ( spl3_40
    | spl3_38
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f291,f211,f116,f303,f312])).

fof(f312,plain,
    ( spl3_40
  <=> ! [X3,X2] :
        ( ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X3,sK2)
        | ~ r1_tarski(sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f291,plain,
    ( ! [X2,X3] :
        ( r1_tarski(sK1,sK1)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(sK1,X2)
        | ~ r1_tarski(X3,sK2) )
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(superposition,[],[f117,f213])).

fof(f310,plain,
    ( spl3_39
    | spl3_38
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f290,f211,f122,f303,f308])).

fof(f308,plain,
    ( spl3_39
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,sK1)
        | ~ r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f290,plain,
    ( ! [X0,X1] :
        ( r1_tarski(sK1,sK1)
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(sK1,X0)
        | ~ r1_tarski(X1,sK1) )
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(superposition,[],[f123,f213])).

fof(f306,plain,
    ( spl3_38
    | ~ spl3_8
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f289,f211,f77,f303])).

fof(f77,plain,
    ( spl3_8
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f289,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl3_8
    | ~ spl3_22 ),
    inference(superposition,[],[f79,f213])).

fof(f79,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f300,plain,
    ( ~ spl3_37
    | spl3_20
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f287,f211,f184,f297])).

fof(f184,plain,
    ( spl3_20
  <=> r1_tarski(k2_pre_topc(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f287,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_20
    | ~ spl3_22 ),
    inference(superposition,[],[f186,f213])).

fof(f186,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK2)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f184])).

fof(f286,plain,
    ( ~ spl3_36
    | spl3_31
    | ~ spl3_10
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f253,f206,f98,f262,f283])).

fof(f262,plain,
    ( spl3_31
  <=> r1_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f98,plain,
    ( spl3_10
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | r1_tarski(X0,k2_pre_topc(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f253,plain,
    ( r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,sK1)
    | ~ spl3_10
    | ~ spl3_21 ),
    inference(superposition,[],[f99,f208])).

fof(f99,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_pre_topc(sK0,X0))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f98])).

fof(f281,plain,
    ( spl3_35
    | spl3_31
    | ~ spl3_11
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f252,f206,f104,f262,f279])).

fof(f279,plain,
    ( spl3_35
  <=> ! [X5] :
        ( ~ r1_tarski(X5,sK2)
        | ~ r1_tarski(sK2,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f252,plain,
    ( ! [X5] :
        ( r1_tarski(sK2,sK2)
        | ~ r1_tarski(X5,sK2)
        | ~ r1_tarski(sK2,X5) )
    | ~ spl3_11
    | ~ spl3_21 ),
    inference(superposition,[],[f105,f208])).

fof(f277,plain,
    ( spl3_34
    | spl3_31
    | ~ spl3_12
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f251,f206,f110,f262,f275])).

fof(f275,plain,
    ( spl3_34
  <=> ! [X4] :
        ( ~ r1_tarski(X4,sK1)
        | ~ r1_tarski(sK2,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f251,plain,
    ( ! [X4] :
        ( r1_tarski(sK2,sK2)
        | ~ r1_tarski(X4,sK1)
        | ~ r1_tarski(sK2,X4) )
    | ~ spl3_12
    | ~ spl3_21 ),
    inference(superposition,[],[f111,f208])).

fof(f273,plain,
    ( spl3_33
    | spl3_31
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f250,f206,f116,f262,f271])).

fof(f271,plain,
    ( spl3_33
  <=> ! [X3,X2] :
        ( ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X3,sK2)
        | ~ r1_tarski(sK2,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f250,plain,
    ( ! [X2,X3] :
        ( r1_tarski(sK2,sK2)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(sK2,X2)
        | ~ r1_tarski(X3,sK2) )
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(superposition,[],[f117,f208])).

fof(f269,plain,
    ( spl3_32
    | spl3_31
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f249,f206,f122,f262,f267])).

fof(f267,plain,
    ( spl3_32
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,sK1)
        | ~ r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( r1_tarski(sK2,sK2)
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(sK2,X0)
        | ~ r1_tarski(X1,sK1) )
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(superposition,[],[f123,f208])).

fof(f265,plain,
    ( spl3_31
    | ~ spl3_7
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f248,f206,f72,f262])).

fof(f72,plain,
    ( spl3_7
  <=> r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f248,plain,
    ( r1_tarski(sK2,sK2)
    | ~ spl3_7
    | ~ spl3_21 ),
    inference(superposition,[],[f74,f208])).

fof(f74,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f260,plain,
    ( ~ spl3_30
    | spl3_1
    | ~ spl3_21
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f255,f211,f206,f39,f257])).

fof(f257,plain,
    ( spl3_30
  <=> k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f39,plain,
    ( spl3_1
  <=> k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f255,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | spl3_1
    | ~ spl3_21
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f247,f213])).

fof(f247,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK2)
    | spl3_1
    | ~ spl3_21 ),
    inference(superposition,[],[f41,f208])).

fof(f41,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f245,plain,
    ( ~ spl3_29
    | spl3_16
    | ~ spl3_21
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f240,f211,f206,f159,f242])).

fof(f159,plain,
    ( spl3_16
  <=> k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = k3_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f240,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_xboole_0(sK2,sK1)
    | spl3_16
    | ~ spl3_21
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f239,f208])).

fof(f239,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_xboole_0(k2_pre_topc(sK0,sK2),sK1)
    | spl3_16
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f161,f213])).

fof(f161,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f159])).

fof(f238,plain,
    ( ~ spl3_6
    | spl3_28
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f201,f54,f236,f64])).

fof(f201,plain,
    ( ! [X11] :
        ( ~ v4_pre_topc(X11,sK0)
        | k2_pre_topc(sK0,X11) = X11
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X11,sK2) )
    | ~ spl3_4 ),
    inference(resolution,[],[f31,f85])).

fof(f234,plain,
    ( ~ spl3_6
    | spl3_27
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f200,f59,f232,f64])).

fof(f200,plain,
    ( ! [X10] :
        ( ~ v4_pre_topc(X10,sK0)
        | k2_pre_topc(sK0,X10) = X10
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X10,sK1) )
    | ~ spl3_5 ),
    inference(resolution,[],[f31,f86])).

fof(f230,plain,
    ( ~ spl3_6
    | spl3_26
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f199,f54,f228,f64])).

fof(f199,plain,
    ( ! [X8,X9] :
        ( ~ v4_pre_topc(X8,sK0)
        | k2_pre_topc(sK0,X8) = X8
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X9,sK2)
        | ~ r1_tarski(X8,X9) )
    | ~ spl3_4 ),
    inference(resolution,[],[f31,f90])).

fof(f226,plain,
    ( ~ spl3_6
    | spl3_25
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f198,f59,f224,f64])).

fof(f198,plain,
    ( ! [X6,X7] :
        ( ~ v4_pre_topc(X6,sK0)
        | k2_pre_topc(sK0,X6) = X6
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X7,sK1)
        | ~ r1_tarski(X6,X7) )
    | ~ spl3_5 ),
    inference(resolution,[],[f31,f96])).

fof(f222,plain,
    ( ~ spl3_6
    | spl3_24
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f197,f54,f220,f64])).

fof(f197,plain,
    ( ! [X4,X5,X3] :
        ( ~ v4_pre_topc(X3,sK0)
        | k2_pre_topc(sK0,X3) = X3
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,sK2)
        | ~ r1_tarski(X3,X4) )
    | ~ spl3_4 ),
    inference(resolution,[],[f31,f102])).

fof(f218,plain,
    ( ~ spl3_6
    | spl3_23
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f196,f59,f216,f64])).

fof(f196,plain,
    ( ! [X2,X0,X1] :
        ( ~ v4_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,X0) = X0
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X2,sK1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_5 ),
    inference(resolution,[],[f31,f108])).

fof(f214,plain,
    ( ~ spl3_6
    | spl3_22
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f195,f59,f49,f211,f64])).

fof(f49,plain,
    ( spl3_3
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f195,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f31,f61])).

fof(f209,plain,
    ( ~ spl3_6
    | spl3_21
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f194,f54,f44,f206,f64])).

fof(f44,plain,
    ( spl3_2
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f194,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | sK2 = k2_pre_topc(sK0,sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f31,f56])).

fof(f187,plain,
    ( ~ spl3_20
    | ~ spl3_4
    | spl3_15 ),
    inference(avatar_split_clause,[],[f177,f155,f54,f184])).

fof(f155,plain,
    ( spl3_15
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f177,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK2)
    | ~ spl3_4
    | spl3_15 ),
    inference(resolution,[],[f157,f85])).

fof(f157,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f155])).

fof(f182,plain,
    ( ~ spl3_19
    | ~ spl3_5
    | spl3_15 ),
    inference(avatar_split_clause,[],[f176,f155,f59,f179])).

fof(f179,plain,
    ( spl3_19
  <=> r1_tarski(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f176,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_5
    | spl3_15 ),
    inference(resolution,[],[f157,f86])).

fof(f171,plain,
    ( ~ spl3_17
    | ~ spl3_18
    | spl3_1 ),
    inference(avatar_split_clause,[],[f153,f39,f168,f164])).

fof(f164,plain,
    ( spl3_17
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f168,plain,
    ( spl3_18
  <=> k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f153,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1 ),
    inference(superposition,[],[f41,f36])).

fof(f162,plain,
    ( ~ spl3_15
    | ~ spl3_16
    | spl3_1 ),
    inference(avatar_split_clause,[],[f152,f39,f159,f155])).

fof(f152,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1 ),
    inference(superposition,[],[f41,f133])).

fof(f124,plain,
    ( ~ spl3_6
    | spl3_14
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f119,f59,f122,f64])).

fof(f119,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,sK1)
        | ~ r1_tarski(X2,X0)
        | r1_tarski(X2,k2_pre_topc(sK0,X2))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_5 ),
    inference(resolution,[],[f108,f30])).

fof(f118,plain,
    ( ~ spl3_6
    | spl3_13
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f113,f54,f116,f64])).

fof(f113,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,sK2)
        | ~ r1_tarski(X2,X0)
        | r1_tarski(X2,k2_pre_topc(sK0,X2))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f102,f30])).

fof(f112,plain,
    ( ~ spl3_6
    | spl3_12
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f107,f59,f110,f64])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X1,X0)
        | r1_tarski(X1,k2_pre_topc(sK0,X1))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_5 ),
    inference(resolution,[],[f96,f30])).

fof(f106,plain,
    ( ~ spl3_6
    | spl3_11
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f101,f54,f104,f64])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(X1,X0)
        | r1_tarski(X1,k2_pre_topc(sK0,X1))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f90,f30])).

fof(f100,plain,
    ( ~ spl3_6
    | spl3_10
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f95,f59,f98,f64])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | r1_tarski(X0,k2_pre_topc(sK0,X0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_5 ),
    inference(resolution,[],[f86,f30])).

fof(f94,plain,
    ( ~ spl3_6
    | spl3_9
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f89,f54,f92,f64])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | r1_tarski(X0,k2_pre_topc(sK0,X0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f85,f30])).

fof(f80,plain,
    ( ~ spl3_6
    | spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f69,f59,f77,f64])).

fof(f69,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f30,f61])).

fof(f75,plain,
    ( ~ spl3_6
    | spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f68,f54,f72,f64])).

fof(f68,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f30,f56])).

fof(f67,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f24,f64])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    & v4_pre_topc(sK2,sK0)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
                & v4_pre_topc(X2,X0)
                & v4_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))
              & v4_pre_topc(X2,sK0)
              & v4_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))
            & v4_pre_topc(X2,sK0)
            & v4_pre_topc(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))
          & v4_pre_topc(X2,sK0)
          & v4_pre_topc(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))
        & v4_pre_topc(X2,sK0)
        & v4_pre_topc(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
      & v4_pre_topc(sK2,sK0)
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
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
               => ( ( v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_1)).

fof(f62,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f27,f49])).

fof(f27,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f28,f44])).

fof(f28,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f29,f39])).

fof(f29,plain,(
    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 09:44:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.47  % (31348)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.48  % (31339)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.50  % (31332)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.50  % (31340)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.12/0.51  % (31334)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.12/0.52  % (31341)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.12/0.52  % (31342)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.12/0.52  % (31331)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.12/0.52  % (31349)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.12/0.52  % (31352)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.12/0.52  % (31338)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.12/0.52  % (31344)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.12/0.52  % (31333)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.12/0.52  % (31335)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.12/0.52  % (31333)Refutation not found, incomplete strategy% (31333)------------------------------
% 1.12/0.52  % (31333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.52  % (31333)Termination reason: Refutation not found, incomplete strategy
% 1.12/0.52  
% 1.12/0.52  % (31333)Memory used [KB]: 10618
% 1.12/0.52  % (31333)Time elapsed: 0.103 s
% 1.12/0.52  % (31333)------------------------------
% 1.12/0.52  % (31333)------------------------------
% 1.12/0.53  % (31337)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.28/0.53  % (31330)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.28/0.53  % (31336)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.28/0.54  % (31347)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.28/0.54  % (31346)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.28/0.54  % (31353)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.28/0.54  % (31343)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.28/0.55  % (31350)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.28/0.55  % (31345)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.28/0.55  % (31351)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.28/0.56  % (31353)Refutation not found, incomplete strategy% (31353)------------------------------
% 1.28/0.56  % (31353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.56  % (31353)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.56  
% 1.28/0.56  % (31353)Memory used [KB]: 10618
% 1.28/0.56  % (31353)Time elapsed: 0.150 s
% 1.28/0.56  % (31353)------------------------------
% 1.28/0.56  % (31353)------------------------------
% 2.04/0.63  % (31352)Refutation not found, incomplete strategy% (31352)------------------------------
% 2.04/0.63  % (31352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.63  % (31352)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.63  
% 2.04/0.63  % (31352)Memory used [KB]: 1663
% 2.04/0.63  % (31352)Time elapsed: 0.159 s
% 2.04/0.63  % (31352)------------------------------
% 2.04/0.63  % (31352)------------------------------
% 2.58/0.70  % (31334)Refutation found. Thanks to Tanya!
% 2.58/0.70  % SZS status Theorem for theBenchmark
% 2.58/0.70  % SZS output start Proof for theBenchmark
% 2.58/0.70  fof(f1144,plain,(
% 2.58/0.70    $false),
% 2.58/0.70    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f62,f67,f75,f80,f94,f100,f106,f112,f118,f124,f162,f171,f182,f187,f209,f214,f218,f222,f226,f230,f234,f238,f245,f260,f265,f269,f273,f277,f281,f286,f300,f306,f310,f314,f318,f322,f323,f330,f335,f339,f365,f378,f391,f398,f399,f406,f407,f412,f419,f424,f436,f442,f633,f637,f644,f648,f889,f919,f1025,f1029,f1033,f1037,f1041,f1045,f1049,f1053,f1057,f1061,f1065,f1069,f1073,f1077,f1081,f1085,f1089,f1093,f1097,f1101,f1105,f1109,f1113,f1117,f1121,f1125,f1129,f1133,f1137,f1142,f1143])).
% 2.58/0.70  fof(f1143,plain,(
% 2.58/0.70    spl3_54 | ~spl3_62 | ~spl3_49 | ~spl3_53 | ~spl3_55),
% 2.58/0.70    inference(avatar_split_clause,[],[f930,f433,f409,f375,f886,f421])).
% 2.58/0.70  fof(f421,plain,(
% 2.58/0.70    spl3_54 <=> k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 2.58/0.70  fof(f886,plain,(
% 2.58/0.70    spl3_62 <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 2.58/0.70  fof(f375,plain,(
% 2.58/0.70    spl3_49 <=> k3_xboole_0(sK2,sK1) = k3_xboole_0(sK1,sK2)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 2.58/0.70  fof(f409,plain,(
% 2.58/0.70    spl3_53 <=> m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 2.58/0.70  fof(f433,plain,(
% 2.58/0.70    spl3_55 <=> r1_tarski(k3_xboole_0(sK1,sK2),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 2.58/0.70  fof(f930,plain,(
% 2.58/0.70    ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | (~spl3_49 | ~spl3_53 | ~spl3_55)),
% 2.58/0.70    inference(resolution,[],[f844,f435])).
% 2.58/0.70  fof(f435,plain,(
% 2.58/0.70    r1_tarski(k3_xboole_0(sK1,sK2),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) | ~spl3_55),
% 2.58/0.70    inference(avatar_component_clause,[],[f433])).
% 2.58/0.70  fof(f844,plain,(
% 2.58/0.70    ( ! [X28] : (~r1_tarski(k3_xboole_0(sK1,sK2),X28) | ~r1_tarski(X28,k3_xboole_0(sK1,sK2)) | k3_xboole_0(sK1,sK2) = X28) ) | (~spl3_49 | ~spl3_53)),
% 2.58/0.70    inference(forward_demodulation,[],[f843,f376])).
% 2.58/0.70  fof(f376,plain,(
% 2.58/0.70    k3_xboole_0(sK2,sK1) = k3_xboole_0(sK1,sK2) | ~spl3_49),
% 2.58/0.70    inference(avatar_component_clause,[],[f375])).
% 2.58/0.70  fof(f843,plain,(
% 2.58/0.70    ( ! [X28] : (~r1_tarski(X28,k3_xboole_0(sK1,sK2)) | k3_xboole_0(sK1,sK2) = X28 | ~r1_tarski(k3_xboole_0(sK2,sK1),X28)) ) | (~spl3_49 | ~spl3_53)),
% 2.58/0.70    inference(forward_demodulation,[],[f842,f376])).
% 2.58/0.70  fof(f842,plain,(
% 2.58/0.70    ( ! [X28] : (k3_xboole_0(sK1,sK2) = X28 | ~r1_tarski(X28,k3_xboole_0(sK2,sK1)) | ~r1_tarski(k3_xboole_0(sK2,sK1),X28)) ) | (~spl3_49 | ~spl3_53)),
% 2.58/0.70    inference(forward_demodulation,[],[f834,f376])).
% 2.58/0.70  fof(f834,plain,(
% 2.58/0.70    ( ! [X28] : (k3_xboole_0(sK2,sK1) = X28 | ~r1_tarski(X28,k3_xboole_0(sK2,sK1)) | ~r1_tarski(k3_xboole_0(sK2,sK1),X28)) ) | ~spl3_53),
% 2.58/0.70    inference(resolution,[],[f802,f411])).
% 2.58/0.70  fof(f411,plain,(
% 2.58/0.70    m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_53),
% 2.58/0.70    inference(avatar_component_clause,[],[f409])).
% 2.58/0.70  fof(f802,plain,(
% 2.58/0.70    ( ! [X12,X10,X11] : (~m1_subset_1(X10,k1_zfmisc_1(X12)) | X10 = X11 | ~r1_tarski(X11,X10) | ~r1_tarski(X10,X11)) )),
% 2.58/0.70    inference(superposition,[],[f799,f34])).
% 2.58/0.70  fof(f34,plain,(
% 2.58/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f16])).
% 2.58/0.70  fof(f16,plain,(
% 2.58/0.70    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.58/0.70    inference(ennf_transformation,[],[f1])).
% 2.58/0.70  fof(f1,axiom,(
% 2.58/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.58/0.70  fof(f799,plain,(
% 2.58/0.70    ( ! [X6,X4,X5] : (k3_xboole_0(X5,X4) = X4 | ~m1_subset_1(X5,k1_zfmisc_1(X6)) | ~r1_tarski(X4,X5)) )),
% 2.58/0.70    inference(global_subsumption,[],[f84,f785])).
% 2.58/0.70  fof(f785,plain,(
% 2.58/0.70    ( ! [X6,X4,X5] : (k3_xboole_0(X5,X4) = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X6)) | ~m1_subset_1(X5,k1_zfmisc_1(X6)) | ~r1_tarski(X4,X5)) )),
% 2.58/0.70    inference(superposition,[],[f142,f34])).
% 2.58/0.70  fof(f142,plain,(
% 2.58/0.70    ( ! [X10,X11,X9] : (k3_xboole_0(X10,X11) = k3_xboole_0(X11,X10) | ~m1_subset_1(X10,k1_zfmisc_1(X9)) | ~m1_subset_1(X11,k1_zfmisc_1(X9))) )),
% 2.58/0.70    inference(superposition,[],[f133,f36])).
% 2.58/0.70  fof(f36,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.58/0.70    inference(cnf_transformation,[],[f18])).
% 2.58/0.70  fof(f18,plain,(
% 2.58/0.70    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.58/0.70    inference(ennf_transformation,[],[f4])).
% 2.58/0.70  fof(f4,axiom,(
% 2.58/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.58/0.70  fof(f133,plain,(
% 2.58/0.70    ( ! [X6,X8,X7] : (k3_xboole_0(X7,X8) = k9_subset_1(X6,X8,X7) | ~m1_subset_1(X8,k1_zfmisc_1(X6))) )),
% 2.58/0.70    inference(duplicate_literal_removal,[],[f125])).
% 2.58/0.70  fof(f125,plain,(
% 2.58/0.70    ( ! [X6,X8,X7] : (k3_xboole_0(X7,X8) = k9_subset_1(X6,X8,X7) | ~m1_subset_1(X8,k1_zfmisc_1(X6)) | ~m1_subset_1(X8,k1_zfmisc_1(X6))) )),
% 2.58/0.70    inference(superposition,[],[f37,f36])).
% 2.58/0.70  fof(f37,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.58/0.70    inference(cnf_transformation,[],[f19])).
% 2.58/0.70  fof(f19,plain,(
% 2.58/0.70    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.58/0.70    inference(ennf_transformation,[],[f2])).
% 2.58/0.70  fof(f2,axiom,(
% 2.58/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 2.58/0.70  fof(f84,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,k1_zfmisc_1(X2)) | ~r1_tarski(X0,X1)) )),
% 2.58/0.70    inference(superposition,[],[f82,f34])).
% 2.58/0.70  fof(f82,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.58/0.70    inference(duplicate_literal_removal,[],[f81])).
% 2.58/0.70  fof(f81,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.58/0.70    inference(superposition,[],[f35,f36])).
% 2.58/0.70  fof(f35,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.58/0.70    inference(cnf_transformation,[],[f17])).
% 2.58/0.70  fof(f17,plain,(
% 2.58/0.70    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.58/0.70    inference(ennf_transformation,[],[f3])).
% 2.58/0.70  fof(f3,axiom,(
% 2.58/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 2.58/0.70  fof(f1142,plain,(
% 2.58/0.70    ~spl3_92 | spl3_54 | ~spl3_62 | ~spl3_9 | ~spl3_49 | ~spl3_53),
% 2.58/0.70    inference(avatar_split_clause,[],[f931,f409,f375,f92,f886,f421,f1139])).
% 2.58/0.70  fof(f1139,plain,(
% 2.58/0.70    spl3_92 <=> r1_tarski(k3_xboole_0(sK1,sK2),sK2)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).
% 2.58/0.70  fof(f92,plain,(
% 2.58/0.70    spl3_9 <=> ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(X0,k2_pre_topc(sK0,X0)))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.58/0.70  fof(f931,plain,(
% 2.58/0.70    ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | (~spl3_9 | ~spl3_49 | ~spl3_53)),
% 2.58/0.70    inference(resolution,[],[f844,f93])).
% 2.58/0.70  fof(f93,plain,(
% 2.58/0.70    ( ! [X0] : (r1_tarski(X0,k2_pre_topc(sK0,X0)) | ~r1_tarski(X0,sK2)) ) | ~spl3_9),
% 2.58/0.70    inference(avatar_component_clause,[],[f92])).
% 2.58/0.70  fof(f1137,plain,(
% 2.58/0.70    spl3_91 | spl3_54 | ~spl3_62 | ~spl3_11 | ~spl3_49 | ~spl3_53),
% 2.58/0.70    inference(avatar_split_clause,[],[f933,f409,f375,f104,f886,f421,f1135])).
% 2.58/0.70  fof(f1135,plain,(
% 2.58/0.70    spl3_91 <=> ! [X0] : (~r1_tarski(X0,sK2) | ~r1_tarski(k3_xboole_0(sK1,sK2),X0))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).
% 2.58/0.70  fof(f104,plain,(
% 2.58/0.70    spl3_11 <=> ! [X1,X0] : (~r1_tarski(X0,sK2) | r1_tarski(X1,k2_pre_topc(sK0,X1)) | ~r1_tarski(X1,X0))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.58/0.70  fof(f933,plain,(
% 2.58/0.70    ( ! [X0] : (~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(X0,sK2) | ~r1_tarski(k3_xboole_0(sK1,sK2),X0)) ) | (~spl3_11 | ~spl3_49 | ~spl3_53)),
% 2.58/0.70    inference(resolution,[],[f844,f105])).
% 2.58/0.70  fof(f105,plain,(
% 2.58/0.70    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(sK0,X1)) | ~r1_tarski(X0,sK2) | ~r1_tarski(X1,X0)) ) | ~spl3_11),
% 2.58/0.70    inference(avatar_component_clause,[],[f104])).
% 2.58/0.70  fof(f1133,plain,(
% 2.58/0.70    spl3_90 | spl3_54 | ~spl3_62 | ~spl3_12 | ~spl3_49 | ~spl3_53),
% 2.58/0.70    inference(avatar_split_clause,[],[f934,f409,f375,f110,f886,f421,f1131])).
% 2.58/0.70  fof(f1131,plain,(
% 2.58/0.70    spl3_90 <=> ! [X1] : (~r1_tarski(X1,sK1) | ~r1_tarski(k3_xboole_0(sK1,sK2),X1))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).
% 2.58/0.70  fof(f110,plain,(
% 2.58/0.70    spl3_12 <=> ! [X1,X0] : (~r1_tarski(X0,sK1) | r1_tarski(X1,k2_pre_topc(sK0,X1)) | ~r1_tarski(X1,X0))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.58/0.70  fof(f934,plain,(
% 2.58/0.70    ( ! [X1] : (~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(X1,sK1) | ~r1_tarski(k3_xboole_0(sK1,sK2),X1)) ) | (~spl3_12 | ~spl3_49 | ~spl3_53)),
% 2.58/0.70    inference(resolution,[],[f844,f111])).
% 2.58/0.70  fof(f111,plain,(
% 2.58/0.70    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(sK0,X1)) | ~r1_tarski(X0,sK1) | ~r1_tarski(X1,X0)) ) | ~spl3_12),
% 2.58/0.70    inference(avatar_component_clause,[],[f110])).
% 2.58/0.70  fof(f1129,plain,(
% 2.58/0.70    spl3_89 | spl3_54 | ~spl3_62 | ~spl3_13 | ~spl3_49 | ~spl3_53),
% 2.58/0.70    inference(avatar_split_clause,[],[f935,f409,f375,f116,f886,f421,f1127])).
% 2.58/0.70  fof(f1127,plain,(
% 2.58/0.70    spl3_89 <=> ! [X3,X2] : (~r1_tarski(X2,X3) | ~r1_tarski(X3,sK2) | ~r1_tarski(k3_xboole_0(sK1,sK2),X2))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).
% 2.58/0.70  fof(f116,plain,(
% 2.58/0.70    spl3_13 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | r1_tarski(X2,k2_pre_topc(sK0,X2)) | ~r1_tarski(X2,X0) | ~r1_tarski(X1,sK2))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.58/0.70  fof(f935,plain,(
% 2.58/0.70    ( ! [X2,X3] : (~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(X2,X3) | ~r1_tarski(k3_xboole_0(sK1,sK2),X2) | ~r1_tarski(X3,sK2)) ) | (~spl3_13 | ~spl3_49 | ~spl3_53)),
% 2.58/0.70    inference(resolution,[],[f844,f117])).
% 2.58/0.70  fof(f117,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (r1_tarski(X2,k2_pre_topc(sK0,X2)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X0) | ~r1_tarski(X1,sK2)) ) | ~spl3_13),
% 2.58/0.70    inference(avatar_component_clause,[],[f116])).
% 2.58/0.70  fof(f1125,plain,(
% 2.58/0.70    spl3_88 | spl3_54 | ~spl3_62 | ~spl3_14 | ~spl3_49 | ~spl3_53),
% 2.58/0.70    inference(avatar_split_clause,[],[f936,f409,f375,f122,f886,f421,f1123])).
% 2.58/0.70  fof(f1123,plain,(
% 2.58/0.70    spl3_88 <=> ! [X5,X4] : (~r1_tarski(X4,X5) | ~r1_tarski(X5,sK1) | ~r1_tarski(k3_xboole_0(sK1,sK2),X4))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).
% 2.58/0.70  fof(f122,plain,(
% 2.58/0.70    spl3_14 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | r1_tarski(X2,k2_pre_topc(sK0,X2)) | ~r1_tarski(X2,X0) | ~r1_tarski(X1,sK1))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.58/0.70  fof(f936,plain,(
% 2.58/0.70    ( ! [X4,X5] : (~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(X4,X5) | ~r1_tarski(k3_xboole_0(sK1,sK2),X4) | ~r1_tarski(X5,sK1)) ) | (~spl3_14 | ~spl3_49 | ~spl3_53)),
% 2.58/0.70    inference(resolution,[],[f844,f123])).
% 2.58/0.70  fof(f123,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (r1_tarski(X2,k2_pre_topc(sK0,X2)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X0) | ~r1_tarski(X1,sK1)) ) | ~spl3_14),
% 2.58/0.70    inference(avatar_component_clause,[],[f122])).
% 2.58/0.70  fof(f1121,plain,(
% 2.58/0.70    spl3_87 | spl3_54 | ~spl3_62 | ~spl3_49 | ~spl3_53 | ~spl3_58),
% 2.58/0.70    inference(avatar_split_clause,[],[f937,f635,f409,f375,f886,f421,f1119])).
% 2.58/0.70  fof(f1119,plain,(
% 2.58/0.70    spl3_87 <=> ! [X7,X8,X6] : (~r1_tarski(X6,sK2) | ~r1_tarski(k3_xboole_0(sK1,sK2),X7) | ~r1_tarski(X8,X6) | ~r1_tarski(X7,X8))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).
% 2.58/0.70  fof(f635,plain,(
% 2.58/0.70    spl3_58 <=> ! [X5,X7,X4,X6] : (~r1_tarski(X4,sK2) | r1_tarski(X7,k2_pre_topc(sK0,X7)) | ~r1_tarski(X7,X5) | ~r1_tarski(X5,X6) | ~r1_tarski(X6,X4))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 2.58/0.70  fof(f937,plain,(
% 2.58/0.70    ( ! [X6,X8,X7] : (~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(X6,sK2) | ~r1_tarski(k3_xboole_0(sK1,sK2),X7) | ~r1_tarski(X7,X8) | ~r1_tarski(X8,X6)) ) | (~spl3_49 | ~spl3_53 | ~spl3_58)),
% 2.58/0.70    inference(resolution,[],[f844,f636])).
% 2.58/0.70  fof(f636,plain,(
% 2.58/0.70    ( ! [X6,X4,X7,X5] : (r1_tarski(X7,k2_pre_topc(sK0,X7)) | ~r1_tarski(X4,sK2) | ~r1_tarski(X7,X5) | ~r1_tarski(X5,X6) | ~r1_tarski(X6,X4)) ) | ~spl3_58),
% 2.58/0.70    inference(avatar_component_clause,[],[f635])).
% 2.58/0.70  fof(f1117,plain,(
% 2.58/0.70    spl3_86 | spl3_54 | ~spl3_62 | ~spl3_49 | ~spl3_53 | ~spl3_60),
% 2.58/0.70    inference(avatar_split_clause,[],[f938,f646,f409,f375,f886,f421,f1115])).
% 2.58/0.70  fof(f1115,plain,(
% 2.58/0.70    spl3_86 <=> ! [X9,X11,X10] : (~r1_tarski(X9,sK1) | ~r1_tarski(k3_xboole_0(sK1,sK2),X10) | ~r1_tarski(X11,X9) | ~r1_tarski(X10,X11))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).
% 2.58/0.70  fof(f646,plain,(
% 2.58/0.70    spl3_60 <=> ! [X5,X7,X4,X6] : (~r1_tarski(X4,sK1) | r1_tarski(X7,k2_pre_topc(sK0,X7)) | ~r1_tarski(X7,X5) | ~r1_tarski(X5,X6) | ~r1_tarski(X6,X4))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 2.58/0.70  fof(f938,plain,(
% 2.58/0.70    ( ! [X10,X11,X9] : (~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) | k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(X9,sK1) | ~r1_tarski(k3_xboole_0(sK1,sK2),X10) | ~r1_tarski(X10,X11) | ~r1_tarski(X11,X9)) ) | (~spl3_49 | ~spl3_53 | ~spl3_60)),
% 2.58/0.70    inference(resolution,[],[f844,f647])).
% 2.58/0.70  fof(f647,plain,(
% 2.58/0.70    ( ! [X6,X4,X7,X5] : (r1_tarski(X7,k2_pre_topc(sK0,X7)) | ~r1_tarski(X4,sK1) | ~r1_tarski(X7,X5) | ~r1_tarski(X5,X6) | ~r1_tarski(X6,X4)) ) | ~spl3_60),
% 2.58/0.70    inference(avatar_component_clause,[],[f646])).
% 2.58/0.70  fof(f1113,plain,(
% 2.58/0.70    ~spl3_6 | spl3_85 | ~spl3_27),
% 2.58/0.70    inference(avatar_split_clause,[],[f1012,f232,f1111,f64])).
% 2.58/0.70  fof(f64,plain,(
% 2.58/0.70    spl3_6 <=> l1_pre_topc(sK0)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.58/0.70  fof(f1111,plain,(
% 2.58/0.70    spl3_85 <=> ! [X18,X19] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X19,X18)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X19),X18)) | ~v4_pre_topc(X18,sK0) | ~r1_tarski(X18,sK1) | ~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).
% 2.58/0.70  fof(f232,plain,(
% 2.58/0.70    spl3_27 <=> ! [X10] : (~v4_pre_topc(X10,sK0) | ~r1_tarski(X10,sK1) | k2_pre_topc(sK0,X10) = X10)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 2.58/0.70  fof(f1012,plain,(
% 2.58/0.70    ( ! [X19,X18] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X19,X18)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X19),X18)) | ~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X18,sK1) | ~v4_pre_topc(X18,sK0)) ) | ~spl3_27),
% 2.58/0.70    inference(superposition,[],[f33,f233])).
% 2.58/0.70  fof(f233,plain,(
% 2.58/0.70    ( ! [X10] : (k2_pre_topc(sK0,X10) = X10 | ~r1_tarski(X10,sK1) | ~v4_pre_topc(X10,sK0)) ) | ~spl3_27),
% 2.58/0.70    inference(avatar_component_clause,[],[f232])).
% 2.58/0.70  fof(f33,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.58/0.70    inference(cnf_transformation,[],[f15])).
% 2.58/0.70  fof(f15,plain,(
% 2.58/0.70    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.58/0.70    inference(ennf_transformation,[],[f6])).
% 2.58/0.70  fof(f6,axiom,(
% 2.58/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 2.58/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).
% 2.58/0.70  fof(f1109,plain,(
% 2.58/0.70    ~spl3_6 | spl3_84 | ~spl3_28),
% 2.58/0.70    inference(avatar_split_clause,[],[f1011,f236,f1107,f64])).
% 2.58/0.70  fof(f1107,plain,(
% 2.58/0.70    spl3_84 <=> ! [X16,X17] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X17,X16)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X17),X16)) | ~v4_pre_topc(X16,sK0) | ~r1_tarski(X16,sK2) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).
% 2.58/0.70  fof(f236,plain,(
% 2.58/0.70    spl3_28 <=> ! [X11] : (~v4_pre_topc(X11,sK0) | ~r1_tarski(X11,sK2) | k2_pre_topc(sK0,X11) = X11)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 2.58/0.70  fof(f1011,plain,(
% 2.58/0.70    ( ! [X17,X16] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X17,X16)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X17),X16)) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X16,sK2) | ~v4_pre_topc(X16,sK0)) ) | ~spl3_28),
% 2.58/0.70    inference(superposition,[],[f33,f237])).
% 2.58/0.70  fof(f237,plain,(
% 2.58/0.70    ( ! [X11] : (k2_pre_topc(sK0,X11) = X11 | ~r1_tarski(X11,sK2) | ~v4_pre_topc(X11,sK0)) ) | ~spl3_28),
% 2.58/0.70    inference(avatar_component_clause,[],[f236])).
% 2.58/0.70  fof(f1105,plain,(
% 2.58/0.70    ~spl3_6 | spl3_83 | ~spl3_25),
% 2.58/0.70    inference(avatar_split_clause,[],[f1010,f224,f1103,f64])).
% 2.58/0.70  fof(f1103,plain,(
% 2.58/0.70    spl3_83 <=> ! [X13,X15,X14] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X14,X13)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X14),X13)) | ~v4_pre_topc(X13,sK0) | ~r1_tarski(X15,sK1) | ~r1_tarski(X13,X15) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 2.58/0.70  fof(f224,plain,(
% 2.58/0.70    spl3_25 <=> ! [X7,X6] : (~v4_pre_topc(X6,sK0) | ~r1_tarski(X6,X7) | ~r1_tarski(X7,sK1) | k2_pre_topc(sK0,X6) = X6)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 2.58/0.70  fof(f1010,plain,(
% 2.58/0.70    ( ! [X14,X15,X13] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X14,X13)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X14),X13)) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X13,X15) | ~r1_tarski(X15,sK1) | ~v4_pre_topc(X13,sK0)) ) | ~spl3_25),
% 2.58/0.70    inference(superposition,[],[f33,f225])).
% 2.58/0.70  fof(f225,plain,(
% 2.58/0.70    ( ! [X6,X7] : (k2_pre_topc(sK0,X6) = X6 | ~r1_tarski(X6,X7) | ~r1_tarski(X7,sK1) | ~v4_pre_topc(X6,sK0)) ) | ~spl3_25),
% 2.58/0.70    inference(avatar_component_clause,[],[f224])).
% 2.58/0.70  fof(f1101,plain,(
% 2.58/0.70    ~spl3_6 | spl3_82 | ~spl3_26),
% 2.58/0.70    inference(avatar_split_clause,[],[f1009,f228,f1099,f64])).
% 2.58/0.70  fof(f1099,plain,(
% 2.58/0.70    spl3_82 <=> ! [X11,X10,X12] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X11,X10)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X11),X10)) | ~v4_pre_topc(X10,sK0) | ~r1_tarski(X12,sK2) | ~r1_tarski(X10,X12) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).
% 2.58/0.70  fof(f228,plain,(
% 2.58/0.70    spl3_26 <=> ! [X9,X8] : (~v4_pre_topc(X8,sK0) | ~r1_tarski(X8,X9) | ~r1_tarski(X9,sK2) | k2_pre_topc(sK0,X8) = X8)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 2.58/0.70  fof(f1009,plain,(
% 2.58/0.70    ( ! [X12,X10,X11] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X11,X10)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X11),X10)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X10,X12) | ~r1_tarski(X12,sK2) | ~v4_pre_topc(X10,sK0)) ) | ~spl3_26),
% 2.58/0.70    inference(superposition,[],[f33,f229])).
% 2.58/0.70  fof(f229,plain,(
% 2.58/0.70    ( ! [X8,X9] : (k2_pre_topc(sK0,X8) = X8 | ~r1_tarski(X8,X9) | ~r1_tarski(X9,sK2) | ~v4_pre_topc(X8,sK0)) ) | ~spl3_26),
% 2.58/0.70    inference(avatar_component_clause,[],[f228])).
% 2.58/0.70  fof(f1097,plain,(
% 2.58/0.70    ~spl3_6 | spl3_81 | ~spl3_23),
% 2.58/0.70    inference(avatar_split_clause,[],[f1008,f216,f1095,f64])).
% 2.58/0.70  fof(f1095,plain,(
% 2.58/0.70    spl3_81 <=> ! [X9,X7,X8,X6] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X7,X6)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X7),X6)) | ~v4_pre_topc(X6,sK0) | ~r1_tarski(X9,sK1) | ~r1_tarski(X8,X9) | ~r1_tarski(X6,X8) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).
% 2.58/0.70  fof(f216,plain,(
% 2.58/0.70    spl3_23 <=> ! [X1,X0,X2] : (~v4_pre_topc(X0,sK0) | ~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | ~r1_tarski(X2,sK1) | k2_pre_topc(sK0,X0) = X0)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 2.58/0.70  fof(f1008,plain,(
% 2.58/0.70    ( ! [X6,X8,X7,X9] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X7,X6)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X7),X6)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X6,X8) | ~r1_tarski(X8,X9) | ~r1_tarski(X9,sK1) | ~v4_pre_topc(X6,sK0)) ) | ~spl3_23),
% 2.58/0.70    inference(superposition,[],[f33,f217])).
% 2.58/0.70  fof(f217,plain,(
% 2.58/0.70    ( ! [X2,X0,X1] : (k2_pre_topc(sK0,X0) = X0 | ~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | ~r1_tarski(X2,sK1) | ~v4_pre_topc(X0,sK0)) ) | ~spl3_23),
% 2.58/0.70    inference(avatar_component_clause,[],[f216])).
% 2.58/0.70  fof(f1093,plain,(
% 2.58/0.70    ~spl3_6 | spl3_80 | ~spl3_24),
% 2.58/0.70    inference(avatar_split_clause,[],[f1007,f220,f1091,f64])).
% 2.58/0.70  fof(f1091,plain,(
% 2.58/0.70    spl3_80 <=> ! [X3,X5,X2,X4] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X3,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X3),X2)) | ~v4_pre_topc(X2,sK0) | ~r1_tarski(X5,sK2) | ~r1_tarski(X4,X5) | ~r1_tarski(X2,X4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).
% 2.58/0.70  fof(f220,plain,(
% 2.58/0.70    spl3_24 <=> ! [X3,X5,X4] : (~v4_pre_topc(X3,sK0) | ~r1_tarski(X3,X4) | ~r1_tarski(X4,X5) | ~r1_tarski(X5,sK2) | k2_pre_topc(sK0,X3) = X3)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.58/0.70  fof(f1007,plain,(
% 2.58/0.70    ( ! [X4,X2,X5,X3] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X3,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X3),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X2,X4) | ~r1_tarski(X4,X5) | ~r1_tarski(X5,sK2) | ~v4_pre_topc(X2,sK0)) ) | ~spl3_24),
% 2.58/0.70    inference(superposition,[],[f33,f221])).
% 2.58/0.70  fof(f221,plain,(
% 2.58/0.70    ( ! [X4,X5,X3] : (k2_pre_topc(sK0,X3) = X3 | ~r1_tarski(X3,X4) | ~r1_tarski(X4,X5) | ~r1_tarski(X5,sK2) | ~v4_pre_topc(X3,sK0)) ) | ~spl3_24),
% 2.58/0.70    inference(avatar_component_clause,[],[f220])).
% 2.58/0.70  fof(f1089,plain,(
% 2.58/0.70    ~spl3_6 | ~spl3_5 | spl3_79 | ~spl3_22),
% 2.58/0.70    inference(avatar_split_clause,[],[f1006,f211,f1087,f59,f64])).
% 2.58/0.70  fof(f59,plain,(
% 2.58/0.70    spl3_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.58/0.70  fof(f1087,plain,(
% 2.58/0.70    spl3_79 <=> ! [X1] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).
% 2.58/0.70  fof(f211,plain,(
% 2.58/0.70    spl3_22 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 2.58/0.70  fof(f1006,plain,(
% 2.58/0.70    ( ! [X1] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_22),
% 2.58/0.70    inference(superposition,[],[f33,f213])).
% 2.58/0.70  fof(f213,plain,(
% 2.58/0.70    sK1 = k2_pre_topc(sK0,sK1) | ~spl3_22),
% 2.58/0.70    inference(avatar_component_clause,[],[f211])).
% 2.58/0.70  fof(f1085,plain,(
% 2.58/0.70    ~spl3_6 | ~spl3_4 | spl3_78 | ~spl3_21),
% 2.58/0.70    inference(avatar_split_clause,[],[f1005,f206,f1083,f54,f64])).
% 2.58/0.70  fof(f54,plain,(
% 2.58/0.70    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.58/0.70  fof(f1083,plain,(
% 2.58/0.70    spl3_78 <=> ! [X0] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 2.58/0.70  fof(f206,plain,(
% 2.58/0.70    spl3_21 <=> sK2 = k2_pre_topc(sK0,sK2)),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 2.58/0.70  fof(f1005,plain,(
% 2.58/0.70    ( ! [X0] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_21),
% 2.58/0.70    inference(superposition,[],[f33,f208])).
% 2.58/0.70  fof(f208,plain,(
% 2.58/0.70    sK2 = k2_pre_topc(sK0,sK2) | ~spl3_21),
% 2.58/0.70    inference(avatar_component_clause,[],[f206])).
% 2.58/0.70  fof(f1081,plain,(
% 2.58/0.70    ~spl3_6 | spl3_77 | ~spl3_27),
% 2.58/0.70    inference(avatar_split_clause,[],[f1004,f232,f1079,f64])).
% 2.58/0.70  fof(f1079,plain,(
% 2.58/0.70    spl3_77 <=> ! [X18,X19] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X18,X19)),k9_subset_1(u1_struct_0(sK0),X18,k2_pre_topc(sK0,X19))) | ~v4_pre_topc(X18,sK0) | ~r1_tarski(X18,sK1) | ~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 2.58/0.70  fof(f1004,plain,(
% 2.58/0.70    ( ! [X19,X18] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X18,X19)),k9_subset_1(u1_struct_0(sK0),X18,k2_pre_topc(sK0,X19))) | ~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X18,sK1) | ~v4_pre_topc(X18,sK0)) ) | ~spl3_27),
% 2.58/0.70    inference(superposition,[],[f33,f233])).
% 2.58/0.70  fof(f1077,plain,(
% 2.58/0.70    ~spl3_6 | spl3_76 | ~spl3_28),
% 2.58/0.70    inference(avatar_split_clause,[],[f1003,f236,f1075,f64])).
% 2.58/0.70  fof(f1075,plain,(
% 2.58/0.70    spl3_76 <=> ! [X16,X17] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X16,X17)),k9_subset_1(u1_struct_0(sK0),X16,k2_pre_topc(sK0,X17))) | ~v4_pre_topc(X16,sK0) | ~r1_tarski(X16,sK2) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 2.58/0.70  fof(f1003,plain,(
% 2.58/0.70    ( ! [X17,X16] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X16,X17)),k9_subset_1(u1_struct_0(sK0),X16,k2_pre_topc(sK0,X17))) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X16,sK2) | ~v4_pre_topc(X16,sK0)) ) | ~spl3_28),
% 2.58/0.70    inference(superposition,[],[f33,f237])).
% 2.58/0.70  fof(f1073,plain,(
% 2.58/0.70    ~spl3_6 | spl3_75 | ~spl3_25),
% 2.58/0.70    inference(avatar_split_clause,[],[f1002,f224,f1071,f64])).
% 2.58/0.72  fof(f1071,plain,(
% 2.58/0.72    spl3_75 <=> ! [X13,X15,X14] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X13,X14)),k9_subset_1(u1_struct_0(sK0),X13,k2_pre_topc(sK0,X14))) | ~v4_pre_topc(X13,sK0) | ~r1_tarski(X15,sK1) | ~r1_tarski(X13,X15) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 2.58/0.72  fof(f1002,plain,(
% 2.58/0.72    ( ! [X14,X15,X13] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X13,X14)),k9_subset_1(u1_struct_0(sK0),X13,k2_pre_topc(sK0,X14))) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X13,X15) | ~r1_tarski(X15,sK1) | ~v4_pre_topc(X13,sK0)) ) | ~spl3_25),
% 2.58/0.72    inference(superposition,[],[f33,f225])).
% 2.58/0.72  fof(f1069,plain,(
% 2.58/0.72    ~spl3_6 | spl3_74 | ~spl3_26),
% 2.58/0.72    inference(avatar_split_clause,[],[f1001,f228,f1067,f64])).
% 2.58/0.72  fof(f1067,plain,(
% 2.58/0.72    spl3_74 <=> ! [X11,X10,X12] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X10,X11)),k9_subset_1(u1_struct_0(sK0),X10,k2_pre_topc(sK0,X11))) | ~v4_pre_topc(X10,sK0) | ~r1_tarski(X12,sK2) | ~r1_tarski(X10,X12) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 2.58/0.72  fof(f1001,plain,(
% 2.58/0.72    ( ! [X12,X10,X11] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X10,X11)),k9_subset_1(u1_struct_0(sK0),X10,k2_pre_topc(sK0,X11))) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X10,X12) | ~r1_tarski(X12,sK2) | ~v4_pre_topc(X10,sK0)) ) | ~spl3_26),
% 2.58/0.72    inference(superposition,[],[f33,f229])).
% 2.58/0.72  fof(f1065,plain,(
% 2.58/0.72    ~spl3_6 | spl3_73 | ~spl3_23),
% 2.58/0.72    inference(avatar_split_clause,[],[f1000,f216,f1063,f64])).
% 2.58/0.72  fof(f1063,plain,(
% 2.58/0.72    spl3_73 <=> ! [X9,X7,X8,X6] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X6,X7)),k9_subset_1(u1_struct_0(sK0),X6,k2_pre_topc(sK0,X7))) | ~v4_pre_topc(X6,sK0) | ~r1_tarski(X9,sK1) | ~r1_tarski(X8,X9) | ~r1_tarski(X6,X8) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 2.58/0.72  fof(f1000,plain,(
% 2.58/0.72    ( ! [X6,X8,X7,X9] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X6,X7)),k9_subset_1(u1_struct_0(sK0),X6,k2_pre_topc(sK0,X7))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X6,X8) | ~r1_tarski(X8,X9) | ~r1_tarski(X9,sK1) | ~v4_pre_topc(X6,sK0)) ) | ~spl3_23),
% 2.58/0.72    inference(superposition,[],[f33,f217])).
% 2.58/0.72  fof(f1061,plain,(
% 2.58/0.72    ~spl3_6 | spl3_72 | ~spl3_24),
% 2.58/0.72    inference(avatar_split_clause,[],[f999,f220,f1059,f64])).
% 2.58/0.72  fof(f1059,plain,(
% 2.58/0.72    spl3_72 <=> ! [X3,X5,X2,X4] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X3)),k9_subset_1(u1_struct_0(sK0),X2,k2_pre_topc(sK0,X3))) | ~v4_pre_topc(X2,sK0) | ~r1_tarski(X5,sK2) | ~r1_tarski(X4,X5) | ~r1_tarski(X2,X4) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 2.58/0.72  fof(f999,plain,(
% 2.58/0.72    ( ! [X4,X2,X5,X3] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X3)),k9_subset_1(u1_struct_0(sK0),X2,k2_pre_topc(sK0,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X2,X4) | ~r1_tarski(X4,X5) | ~r1_tarski(X5,sK2) | ~v4_pre_topc(X2,sK0)) ) | ~spl3_24),
% 2.58/0.72    inference(superposition,[],[f33,f221])).
% 2.58/0.72  fof(f1057,plain,(
% 2.58/0.72    ~spl3_6 | ~spl3_5 | spl3_71 | ~spl3_22),
% 2.58/0.72    inference(avatar_split_clause,[],[f998,f211,f1055,f59,f64])).
% 2.58/0.72  fof(f1055,plain,(
% 2.58/0.72    spl3_71 <=> ! [X1] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X1)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 2.58/0.72  fof(f998,plain,(
% 2.58/0.72    ( ! [X1] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X1)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_22),
% 2.58/0.72    inference(superposition,[],[f33,f213])).
% 2.58/0.72  fof(f1053,plain,(
% 2.58/0.72    ~spl3_6 | ~spl3_4 | spl3_70 | ~spl3_21),
% 2.58/0.72    inference(avatar_split_clause,[],[f997,f206,f1051,f54,f64])).
% 2.58/0.72  fof(f1051,plain,(
% 2.58/0.72    spl3_70 <=> ! [X0] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)),k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 2.58/0.72  fof(f997,plain,(
% 2.58/0.72    ( ! [X0] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)),k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_21),
% 2.58/0.72    inference(superposition,[],[f33,f208])).
% 2.58/0.72  fof(f1049,plain,(
% 2.58/0.72    ~spl3_6 | spl3_69 | ~spl3_27),
% 2.58/0.72    inference(avatar_split_clause,[],[f996,f232,f1047,f64])).
% 2.58/0.72  fof(f1047,plain,(
% 2.58/0.72    spl3_69 <=> ! [X16,X17] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),X16,X17),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X16),k2_pre_topc(sK0,X17))) | ~v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X16,X17),sK0) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),X16,X17),sK1) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 2.58/0.72  fof(f996,plain,(
% 2.58/0.72    ( ! [X17,X16] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),X16,X17),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X16),k2_pre_topc(sK0,X17))) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),X16,X17),sK1) | ~v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X16,X17),sK0)) ) | ~spl3_27),
% 2.58/0.72    inference(superposition,[],[f33,f233])).
% 2.58/0.72  fof(f1045,plain,(
% 2.58/0.72    ~spl3_6 | spl3_68 | ~spl3_28),
% 2.58/0.72    inference(avatar_split_clause,[],[f995,f236,f1043,f64])).
% 2.58/0.72  fof(f1043,plain,(
% 2.58/0.72    spl3_68 <=> ! [X15,X14] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),X14,X15),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X14),k2_pre_topc(sK0,X15))) | ~v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X14,X15),sK0) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),X14,X15),sK2) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 2.58/0.72  fof(f995,plain,(
% 2.58/0.72    ( ! [X14,X15] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),X14,X15),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X14),k2_pre_topc(sK0,X15))) | ~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),X14,X15),sK2) | ~v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X14,X15),sK0)) ) | ~spl3_28),
% 2.58/0.72    inference(superposition,[],[f33,f237])).
% 2.58/0.72  fof(f1041,plain,(
% 2.58/0.72    ~spl3_6 | spl3_67 | ~spl3_25),
% 2.58/0.72    inference(avatar_split_clause,[],[f994,f224,f1039,f64])).
% 2.58/0.72  fof(f1039,plain,(
% 2.58/0.72    spl3_67 <=> ! [X11,X13,X12] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),X11,X12),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X11),k2_pre_topc(sK0,X12))) | ~v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X11,X12),sK0) | ~r1_tarski(X13,sK1) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),X11,X12),X13) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 2.58/0.72  fof(f994,plain,(
% 2.58/0.72    ( ! [X12,X13,X11] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),X11,X12),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X11),k2_pre_topc(sK0,X12))) | ~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),X11,X12),X13) | ~r1_tarski(X13,sK1) | ~v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X11,X12),sK0)) ) | ~spl3_25),
% 2.58/0.72    inference(superposition,[],[f33,f225])).
% 2.58/0.72  fof(f1037,plain,(
% 2.58/0.72    ~spl3_6 | spl3_66 | ~spl3_26),
% 2.58/0.72    inference(avatar_split_clause,[],[f993,f228,f1035,f64])).
% 2.58/0.72  fof(f1035,plain,(
% 2.58/0.72    spl3_66 <=> ! [X9,X8,X10] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),X8,X9),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X8),k2_pre_topc(sK0,X9))) | ~v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X8,X9),sK0) | ~r1_tarski(X10,sK2) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),X8,X9),X10) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 2.58/0.72  fof(f993,plain,(
% 2.58/0.72    ( ! [X10,X8,X9] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),X8,X9),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X8),k2_pre_topc(sK0,X9))) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),X8,X9),X10) | ~r1_tarski(X10,sK2) | ~v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X8,X9),sK0)) ) | ~spl3_26),
% 2.58/0.72    inference(superposition,[],[f33,f229])).
% 2.58/0.72  fof(f1033,plain,(
% 2.58/0.72    ~spl3_6 | spl3_65 | ~spl3_23),
% 2.58/0.72    inference(avatar_split_clause,[],[f992,f216,f1031,f64])).
% 2.58/0.72  fof(f1031,plain,(
% 2.58/0.72    spl3_65 <=> ! [X5,X7,X4,X6] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),X4,X5),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X4),k2_pre_topc(sK0,X5))) | ~v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X4,X5),sK0) | ~r1_tarski(X7,sK1) | ~r1_tarski(X6,X7) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),X4,X5),X6) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 2.58/0.72  fof(f992,plain,(
% 2.58/0.72    ( ! [X6,X4,X7,X5] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),X4,X5),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X4),k2_pre_topc(sK0,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),X4,X5),X6) | ~r1_tarski(X6,X7) | ~r1_tarski(X7,sK1) | ~v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X4,X5),sK0)) ) | ~spl3_23),
% 2.58/0.72    inference(superposition,[],[f33,f217])).
% 2.58/0.72  fof(f1029,plain,(
% 2.58/0.72    ~spl3_6 | spl3_64 | ~spl3_24),
% 2.58/0.72    inference(avatar_split_clause,[],[f991,f220,f1027,f64])).
% 2.58/0.72  fof(f1027,plain,(
% 2.58/0.72    spl3_64 <=> ! [X1,X3,X0,X2] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,X1),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) | ~v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X0,X1),sK0) | ~r1_tarski(X3,sK2) | ~r1_tarski(X2,X3) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,X1),X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 2.58/0.72  fof(f991,plain,(
% 2.58/0.72    ( ! [X2,X0,X3,X1] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,X1),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,X1),X2) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,sK2) | ~v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X0,X1),sK0)) ) | ~spl3_24),
% 2.58/0.72    inference(superposition,[],[f33,f221])).
% 2.58/0.72  fof(f1025,plain,(
% 2.58/0.72    ~spl3_6 | ~spl3_5 | ~spl3_4 | spl3_62 | ~spl3_21 | ~spl3_22 | ~spl3_49 | ~spl3_52),
% 2.58/0.72    inference(avatar_split_clause,[],[f1024,f388,f375,f211,f206,f886,f54,f59,f64])).
% 2.58/0.72  fof(f388,plain,(
% 2.58/0.72    spl3_52 <=> k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_xboole_0(sK2,sK1)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 2.58/0.72  fof(f1024,plain,(
% 2.58/0.72    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_21 | ~spl3_22 | ~spl3_49 | ~spl3_52)),
% 2.58/0.72    inference(forward_demodulation,[],[f1023,f376])).
% 2.58/0.72  fof(f1023,plain,(
% 2.58/0.72    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_21 | ~spl3_22 | ~spl3_52)),
% 2.58/0.72    inference(forward_demodulation,[],[f1022,f389])).
% 2.58/0.72  fof(f389,plain,(
% 2.58/0.72    k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_xboole_0(sK2,sK1) | ~spl3_52),
% 2.58/0.72    inference(avatar_component_clause,[],[f388])).
% 2.58/0.72  fof(f1022,plain,(
% 2.58/0.72    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_21 | ~spl3_22 | ~spl3_52)),
% 2.58/0.72    inference(forward_demodulation,[],[f1021,f213])).
% 2.58/0.72  fof(f1021,plain,(
% 2.58/0.72    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_21 | ~spl3_52)),
% 2.58/0.72    inference(forward_demodulation,[],[f986,f208])).
% 2.58/0.72  fof(f986,plain,(
% 2.58/0.72    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_52),
% 2.58/0.72    inference(superposition,[],[f33,f389])).
% 2.58/0.72  fof(f919,plain,(
% 2.58/0.72    ~spl3_63 | ~spl3_62 | spl3_54 | ~spl3_5 | ~spl3_55),
% 2.58/0.72    inference(avatar_split_clause,[],[f907,f433,f59,f421,f886,f916])).
% 2.58/0.72  fof(f916,plain,(
% 2.58/0.72    spl3_63 <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),sK1)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 2.58/0.72  fof(f907,plain,(
% 2.58/0.72    k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) | ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),sK1) | (~spl3_5 | ~spl3_55)),
% 2.58/0.72    inference(resolution,[],[f827,f435])).
% 2.58/0.72  fof(f827,plain,(
% 2.58/0.72    ( ! [X2,X3] : (~r1_tarski(X3,X2) | X2 = X3 | ~r1_tarski(X2,X3) | ~r1_tarski(X2,sK1)) ) | ~spl3_5),
% 2.58/0.72    inference(resolution,[],[f802,f86])).
% 2.58/0.72  fof(f86,plain,(
% 2.58/0.72    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,sK1)) ) | ~spl3_5),
% 2.58/0.72    inference(resolution,[],[f84,f61])).
% 2.58/0.72  fof(f61,plain,(
% 2.58/0.72    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 2.58/0.72    inference(avatar_component_clause,[],[f59])).
% 2.58/0.72  fof(f889,plain,(
% 2.58/0.72    ~spl3_61 | ~spl3_62 | spl3_54 | ~spl3_4 | ~spl3_55),
% 2.58/0.72    inference(avatar_split_clause,[],[f873,f433,f54,f421,f886,f882])).
% 2.58/0.72  fof(f882,plain,(
% 2.58/0.72    spl3_61 <=> r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),sK2)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 2.58/0.72  fof(f873,plain,(
% 2.58/0.72    k3_xboole_0(sK1,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) | ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),sK2) | (~spl3_4 | ~spl3_55)),
% 2.58/0.72    inference(resolution,[],[f826,f435])).
% 2.58/0.72  fof(f826,plain,(
% 2.58/0.72    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1) | ~r1_tarski(X0,sK2)) ) | ~spl3_4),
% 2.58/0.72    inference(resolution,[],[f802,f85])).
% 2.58/0.72  fof(f85,plain,(
% 2.58/0.72    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK2)) ) | ~spl3_4),
% 2.58/0.72    inference(resolution,[],[f84,f56])).
% 2.58/0.72  fof(f56,plain,(
% 2.58/0.72    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 2.58/0.72    inference(avatar_component_clause,[],[f54])).
% 2.58/0.72  fof(f648,plain,(
% 2.58/0.72    ~spl3_6 | spl3_60 | ~spl3_5),
% 2.58/0.72    inference(avatar_split_clause,[],[f639,f59,f646,f64])).
% 2.58/0.72  fof(f639,plain,(
% 2.58/0.72    ( ! [X6,X4,X7,X5] : (~r1_tarski(X4,sK1) | ~r1_tarski(X5,X6) | ~r1_tarski(X6,X4) | ~r1_tarski(X7,X5) | r1_tarski(X7,k2_pre_topc(sK0,X7)) | ~l1_pre_topc(sK0)) ) | ~spl3_5),
% 2.58/0.72    inference(resolution,[],[f120,f30])).
% 2.58/0.72  fof(f30,plain,(
% 2.58/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.58/0.72    inference(cnf_transformation,[],[f12])).
% 2.58/0.72  fof(f12,plain,(
% 2.58/0.72    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.58/0.72    inference(ennf_transformation,[],[f5])).
% 2.58/0.72  fof(f5,axiom,(
% 2.58/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 2.58/0.72  fof(f120,plain,(
% 2.58/0.72    ( ! [X6,X4,X5,X3] : (m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X4,sK1) | ~r1_tarski(X5,X3) | ~r1_tarski(X3,X4) | ~r1_tarski(X6,X5)) ) | ~spl3_5),
% 2.58/0.72    inference(resolution,[],[f108,f84])).
% 2.58/0.72  fof(f108,plain,(
% 2.58/0.72    ( ! [X4,X2,X3] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,X2) | ~r1_tarski(X2,sK1) | ~r1_tarski(X4,X3)) ) | ~spl3_5),
% 2.58/0.72    inference(resolution,[],[f96,f84])).
% 2.58/0.72  fof(f96,plain,(
% 2.58/0.72    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,sK1) | ~r1_tarski(X2,X1)) ) | ~spl3_5),
% 2.58/0.72    inference(resolution,[],[f86,f84])).
% 2.58/0.72  fof(f644,plain,(
% 2.58/0.72    ~spl3_6 | spl3_59 | ~spl3_5),
% 2.58/0.72    inference(avatar_split_clause,[],[f638,f59,f642,f64])).
% 2.58/0.72  fof(f642,plain,(
% 2.58/0.72    spl3_59 <=> ! [X1,X3,X0,X2] : (~r1_tarski(X0,sK1) | k2_pre_topc(sK0,X3) = X3 | ~v4_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~r1_tarski(X1,X2) | ~r1_tarski(X2,X0))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 2.58/0.72  fof(f638,plain,(
% 2.58/0.72    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,sK1) | ~r1_tarski(X1,X2) | ~r1_tarski(X2,X0) | ~r1_tarski(X3,X1) | ~v4_pre_topc(X3,sK0) | k2_pre_topc(sK0,X3) = X3 | ~l1_pre_topc(sK0)) ) | ~spl3_5),
% 2.58/0.72    inference(resolution,[],[f120,f31])).
% 2.58/0.72  fof(f31,plain,(
% 2.58/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 2.58/0.72    inference(cnf_transformation,[],[f14])).
% 2.58/0.72  fof(f14,plain,(
% 2.58/0.72    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.58/0.72    inference(flattening,[],[f13])).
% 2.58/0.72  fof(f13,plain,(
% 2.58/0.72    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.58/0.72    inference(ennf_transformation,[],[f7])).
% 2.58/0.72  fof(f7,axiom,(
% 2.58/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.58/0.72  fof(f637,plain,(
% 2.58/0.72    ~spl3_6 | spl3_58 | ~spl3_4),
% 2.58/0.72    inference(avatar_split_clause,[],[f628,f54,f635,f64])).
% 2.58/0.72  fof(f628,plain,(
% 2.58/0.72    ( ! [X6,X4,X7,X5] : (~r1_tarski(X4,sK2) | ~r1_tarski(X5,X6) | ~r1_tarski(X6,X4) | ~r1_tarski(X7,X5) | r1_tarski(X7,k2_pre_topc(sK0,X7)) | ~l1_pre_topc(sK0)) ) | ~spl3_4),
% 2.58/0.72    inference(resolution,[],[f114,f30])).
% 2.58/0.72  fof(f114,plain,(
% 2.58/0.72    ( ! [X6,X4,X5,X3] : (m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X4,sK2) | ~r1_tarski(X5,X3) | ~r1_tarski(X3,X4) | ~r1_tarski(X6,X5)) ) | ~spl3_4),
% 2.58/0.72    inference(resolution,[],[f102,f84])).
% 2.58/0.72  fof(f102,plain,(
% 2.58/0.72    ( ! [X4,X2,X3] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,X2) | ~r1_tarski(X2,sK2) | ~r1_tarski(X4,X3)) ) | ~spl3_4),
% 2.58/0.72    inference(resolution,[],[f90,f84])).
% 2.58/0.72  fof(f90,plain,(
% 2.58/0.72    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,sK2) | ~r1_tarski(X2,X1)) ) | ~spl3_4),
% 2.58/0.72    inference(resolution,[],[f85,f84])).
% 2.58/0.72  fof(f633,plain,(
% 2.58/0.72    ~spl3_6 | spl3_57 | ~spl3_4),
% 2.58/0.72    inference(avatar_split_clause,[],[f627,f54,f631,f64])).
% 2.58/0.72  fof(f631,plain,(
% 2.58/0.72    spl3_57 <=> ! [X1,X3,X0,X2] : (~r1_tarski(X0,sK2) | k2_pre_topc(sK0,X3) = X3 | ~v4_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~r1_tarski(X1,X2) | ~r1_tarski(X2,X0))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 2.58/0.72  fof(f627,plain,(
% 2.58/0.72    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,sK2) | ~r1_tarski(X1,X2) | ~r1_tarski(X2,X0) | ~r1_tarski(X3,X1) | ~v4_pre_topc(X3,sK0) | k2_pre_topc(sK0,X3) = X3 | ~l1_pre_topc(sK0)) ) | ~spl3_4),
% 2.58/0.72    inference(resolution,[],[f114,f31])).
% 2.58/0.72  fof(f442,plain,(
% 2.58/0.72    spl3_56 | ~spl3_49 | ~spl3_53),
% 2.58/0.72    inference(avatar_split_clause,[],[f429,f409,f375,f439])).
% 2.58/0.72  fof(f439,plain,(
% 2.58/0.72    spl3_56 <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 2.58/0.72  fof(f429,plain,(
% 2.58/0.72    m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_49 | ~spl3_53)),
% 2.58/0.72    inference(superposition,[],[f411,f376])).
% 2.58/0.72  fof(f436,plain,(
% 2.58/0.72    ~spl3_6 | spl3_55 | ~spl3_49 | ~spl3_53),
% 2.58/0.72    inference(avatar_split_clause,[],[f431,f409,f375,f433,f64])).
% 2.58/0.72  fof(f431,plain,(
% 2.58/0.72    r1_tarski(k3_xboole_0(sK1,sK2),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) | ~l1_pre_topc(sK0) | (~spl3_49 | ~spl3_53)),
% 2.58/0.72    inference(forward_demodulation,[],[f427,f376])).
% 2.58/0.72  fof(f427,plain,(
% 2.58/0.72    r1_tarski(k3_xboole_0(sK2,sK1),k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))) | ~l1_pre_topc(sK0) | ~spl3_53),
% 2.58/0.72    inference(resolution,[],[f411,f30])).
% 2.58/0.72  fof(f424,plain,(
% 2.58/0.72    ~spl3_54 | spl3_43 | ~spl3_49),
% 2.58/0.72    inference(avatar_split_clause,[],[f415,f375,f327,f421])).
% 2.58/0.72  fof(f327,plain,(
% 2.58/0.72    spl3_43 <=> k3_xboole_0(sK2,sK1) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 2.58/0.72  fof(f415,plain,(
% 2.58/0.72    k3_xboole_0(sK1,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | (spl3_43 | ~spl3_49)),
% 2.58/0.72    inference(superposition,[],[f329,f376])).
% 2.58/0.72  fof(f329,plain,(
% 2.58/0.72    k3_xboole_0(sK2,sK1) != k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) | spl3_43),
% 2.58/0.72    inference(avatar_component_clause,[],[f327])).
% 2.58/0.72  fof(f419,plain,(
% 2.58/0.72    ~spl3_47 | spl3_45 | ~spl3_49),
% 2.58/0.72    inference(avatar_split_clause,[],[f414,f375,f358,f367])).
% 2.58/0.72  fof(f367,plain,(
% 2.58/0.72    spl3_47 <=> v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 2.58/0.72  fof(f358,plain,(
% 2.58/0.72    spl3_45 <=> v4_pre_topc(k3_xboole_0(sK2,sK1),sK0)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 2.58/0.72  fof(f414,plain,(
% 2.58/0.72    ~v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) | (spl3_45 | ~spl3_49)),
% 2.58/0.72    inference(superposition,[],[f360,f376])).
% 2.58/0.72  fof(f360,plain,(
% 2.58/0.72    ~v4_pre_topc(k3_xboole_0(sK2,sK1),sK0) | spl3_45),
% 2.58/0.72    inference(avatar_component_clause,[],[f358])).
% 2.58/0.72  fof(f412,plain,(
% 2.58/0.72    ~spl3_4 | spl3_53 | ~spl3_52),
% 2.58/0.72    inference(avatar_split_clause,[],[f405,f388,f409,f54])).
% 2.58/0.72  fof(f405,plain,(
% 2.58/0.72    m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_52),
% 2.58/0.72    inference(superposition,[],[f35,f389])).
% 2.58/0.72  fof(f407,plain,(
% 2.58/0.72    ~spl3_4 | spl3_49 | ~spl3_52),
% 2.58/0.72    inference(avatar_split_clause,[],[f404,f388,f375,f54])).
% 2.58/0.72  fof(f404,plain,(
% 2.58/0.72    k3_xboole_0(sK2,sK1) = k3_xboole_0(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_52),
% 2.58/0.72    inference(superposition,[],[f36,f389])).
% 2.58/0.72  fof(f406,plain,(
% 2.58/0.72    ~spl3_4 | spl3_49 | ~spl3_52),
% 2.58/0.72    inference(avatar_split_clause,[],[f401,f388,f375,f54])).
% 2.58/0.72  fof(f401,plain,(
% 2.58/0.72    k3_xboole_0(sK2,sK1) = k3_xboole_0(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_52),
% 2.58/0.72    inference(superposition,[],[f389,f36])).
% 2.58/0.72  fof(f399,plain,(
% 2.58/0.72    ~spl3_4 | ~spl3_49 | spl3_52),
% 2.58/0.72    inference(avatar_split_clause,[],[f396,f388,f375,f54])).
% 2.58/0.72  fof(f396,plain,(
% 2.58/0.72    k3_xboole_0(sK2,sK1) != k3_xboole_0(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_52),
% 2.58/0.72    inference(superposition,[],[f390,f36])).
% 2.58/0.72  fof(f390,plain,(
% 2.58/0.72    k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_xboole_0(sK2,sK1) | spl3_52),
% 2.58/0.72    inference(avatar_component_clause,[],[f388])).
% 2.58/0.72  fof(f398,plain,(
% 2.58/0.72    ~spl3_5 | spl3_52),
% 2.58/0.72    inference(avatar_split_clause,[],[f397,f388,f59])).
% 2.58/0.72  fof(f397,plain,(
% 2.58/0.72    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_52),
% 2.58/0.72    inference(trivial_inequality_removal,[],[f395])).
% 2.58/0.72  fof(f395,plain,(
% 2.58/0.72    k3_xboole_0(sK2,sK1) != k3_xboole_0(sK2,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_52),
% 2.58/0.72    inference(superposition,[],[f390,f133])).
% 2.58/0.72  fof(f391,plain,(
% 2.58/0.72    ~spl3_50 | ~spl3_51 | ~spl3_52 | ~spl3_27 | spl3_29),
% 2.58/0.72    inference(avatar_split_clause,[],[f349,f242,f232,f388,f384,f380])).
% 2.58/0.72  fof(f380,plain,(
% 2.58/0.72    spl3_50 <=> v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 2.58/0.72  fof(f384,plain,(
% 2.58/0.72    spl3_51 <=> r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 2.58/0.72  fof(f242,plain,(
% 2.58/0.72    spl3_29 <=> k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = k3_xboole_0(sK2,sK1)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 2.58/0.72  fof(f349,plain,(
% 2.58/0.72    k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_xboole_0(sK2,sK1) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | ~v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | (~spl3_27 | spl3_29)),
% 2.58/0.72    inference(superposition,[],[f244,f233])).
% 2.58/0.72  fof(f244,plain,(
% 2.58/0.72    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_xboole_0(sK2,sK1) | spl3_29),
% 2.58/0.72    inference(avatar_component_clause,[],[f242])).
% 2.58/0.72  fof(f378,plain,(
% 2.58/0.72    ~spl3_47 | ~spl3_48 | ~spl3_49 | ~spl3_27 | spl3_44),
% 2.58/0.72    inference(avatar_split_clause,[],[f348,f332,f232,f375,f371,f367])).
% 2.58/0.72  fof(f371,plain,(
% 2.58/0.72    spl3_48 <=> r1_tarski(k3_xboole_0(sK1,sK2),sK1)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 2.58/0.72  fof(f332,plain,(
% 2.58/0.72    spl3_44 <=> k3_xboole_0(sK2,sK1) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 2.58/0.72  fof(f348,plain,(
% 2.58/0.72    k3_xboole_0(sK2,sK1) != k3_xboole_0(sK1,sK2) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | ~v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) | (~spl3_27 | spl3_44)),
% 2.58/0.72    inference(superposition,[],[f334,f233])).
% 2.58/0.72  fof(f334,plain,(
% 2.58/0.72    k3_xboole_0(sK2,sK1) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | spl3_44),
% 2.58/0.72    inference(avatar_component_clause,[],[f332])).
% 2.58/0.72  fof(f365,plain,(
% 2.58/0.72    ~spl3_45 | ~spl3_46 | ~spl3_27 | spl3_43),
% 2.58/0.72    inference(avatar_split_clause,[],[f355,f327,f232,f362,f358])).
% 2.58/0.72  fof(f362,plain,(
% 2.58/0.72    spl3_46 <=> r1_tarski(k3_xboole_0(sK2,sK1),sK1)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 2.58/0.72  fof(f355,plain,(
% 2.58/0.72    ~r1_tarski(k3_xboole_0(sK2,sK1),sK1) | ~v4_pre_topc(k3_xboole_0(sK2,sK1),sK0) | (~spl3_27 | spl3_43)),
% 2.58/0.72    inference(trivial_inequality_removal,[],[f347])).
% 2.58/0.72  fof(f347,plain,(
% 2.58/0.72    k3_xboole_0(sK2,sK1) != k3_xboole_0(sK2,sK1) | ~r1_tarski(k3_xboole_0(sK2,sK1),sK1) | ~v4_pre_topc(k3_xboole_0(sK2,sK1),sK0) | (~spl3_27 | spl3_43)),
% 2.58/0.72    inference(superposition,[],[f329,f233])).
% 2.58/0.72  fof(f339,plain,(
% 2.58/0.72    ~spl3_36 | ~spl3_21 | spl3_43),
% 2.58/0.72    inference(avatar_split_clause,[],[f338,f327,f206,f283])).
% 2.58/0.72  fof(f283,plain,(
% 2.58/0.72    spl3_36 <=> r1_tarski(sK2,sK1)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 2.58/0.72  fof(f338,plain,(
% 2.58/0.72    ~r1_tarski(sK2,sK1) | (~spl3_21 | spl3_43)),
% 2.58/0.72    inference(trivial_inequality_removal,[],[f337])).
% 2.58/0.72  fof(f337,plain,(
% 2.58/0.72    sK2 != sK2 | ~r1_tarski(sK2,sK1) | (~spl3_21 | spl3_43)),
% 2.58/0.72    inference(forward_demodulation,[],[f336,f208])).
% 2.58/0.72  fof(f336,plain,(
% 2.58/0.72    sK2 != k2_pre_topc(sK0,sK2) | ~r1_tarski(sK2,sK1) | spl3_43),
% 2.58/0.72    inference(superposition,[],[f329,f34])).
% 2.58/0.72  fof(f335,plain,(
% 2.58/0.72    ~spl3_4 | ~spl3_44 | spl3_29),
% 2.58/0.72    inference(avatar_split_clause,[],[f325,f242,f332,f54])).
% 2.58/0.72  fof(f325,plain,(
% 2.58/0.72    k3_xboole_0(sK2,sK1) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_29),
% 2.58/0.72    inference(superposition,[],[f244,f36])).
% 2.58/0.72  fof(f330,plain,(
% 2.58/0.72    ~spl3_5 | ~spl3_43 | spl3_29),
% 2.58/0.72    inference(avatar_split_clause,[],[f324,f242,f327,f59])).
% 2.58/0.72  fof(f324,plain,(
% 2.58/0.72    k3_xboole_0(sK2,sK1) != k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_29),
% 2.58/0.72    inference(superposition,[],[f244,f133])).
% 2.58/0.72  fof(f323,plain,(
% 2.58/0.72    ~spl3_37 | spl3_38 | ~spl3_9 | ~spl3_22),
% 2.58/0.72    inference(avatar_split_clause,[],[f295,f211,f92,f303,f297])).
% 2.58/0.72  fof(f297,plain,(
% 2.58/0.72    spl3_37 <=> r1_tarski(sK1,sK2)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 2.58/0.72  fof(f303,plain,(
% 2.58/0.72    spl3_38 <=> r1_tarski(sK1,sK1)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 2.58/0.72  fof(f295,plain,(
% 2.58/0.72    r1_tarski(sK1,sK1) | ~r1_tarski(sK1,sK2) | (~spl3_9 | ~spl3_22)),
% 2.58/0.72    inference(superposition,[],[f93,f213])).
% 2.58/0.72  fof(f322,plain,(
% 2.58/0.72    spl3_42 | spl3_38 | ~spl3_11 | ~spl3_22),
% 2.58/0.72    inference(avatar_split_clause,[],[f293,f211,f104,f303,f320])).
% 2.58/0.72  fof(f320,plain,(
% 2.58/0.72    spl3_42 <=> ! [X5] : (~r1_tarski(X5,sK2) | ~r1_tarski(sK1,X5))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 2.58/0.72  fof(f293,plain,(
% 2.58/0.72    ( ! [X5] : (r1_tarski(sK1,sK1) | ~r1_tarski(X5,sK2) | ~r1_tarski(sK1,X5)) ) | (~spl3_11 | ~spl3_22)),
% 2.58/0.72    inference(superposition,[],[f105,f213])).
% 2.58/0.72  fof(f318,plain,(
% 2.58/0.72    spl3_41 | spl3_38 | ~spl3_12 | ~spl3_22),
% 2.58/0.72    inference(avatar_split_clause,[],[f292,f211,f110,f303,f316])).
% 2.58/0.72  fof(f316,plain,(
% 2.58/0.72    spl3_41 <=> ! [X4] : (~r1_tarski(X4,sK1) | ~r1_tarski(sK1,X4))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 2.58/0.72  fof(f292,plain,(
% 2.58/0.72    ( ! [X4] : (r1_tarski(sK1,sK1) | ~r1_tarski(X4,sK1) | ~r1_tarski(sK1,X4)) ) | (~spl3_12 | ~spl3_22)),
% 2.58/0.72    inference(superposition,[],[f111,f213])).
% 2.58/0.72  fof(f314,plain,(
% 2.58/0.72    spl3_40 | spl3_38 | ~spl3_13 | ~spl3_22),
% 2.58/0.72    inference(avatar_split_clause,[],[f291,f211,f116,f303,f312])).
% 2.58/0.72  fof(f312,plain,(
% 2.58/0.72    spl3_40 <=> ! [X3,X2] : (~r1_tarski(X2,X3) | ~r1_tarski(X3,sK2) | ~r1_tarski(sK1,X2))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 2.58/0.72  fof(f291,plain,(
% 2.58/0.72    ( ! [X2,X3] : (r1_tarski(sK1,sK1) | ~r1_tarski(X2,X3) | ~r1_tarski(sK1,X2) | ~r1_tarski(X3,sK2)) ) | (~spl3_13 | ~spl3_22)),
% 2.58/0.72    inference(superposition,[],[f117,f213])).
% 2.58/0.72  fof(f310,plain,(
% 2.58/0.72    spl3_39 | spl3_38 | ~spl3_14 | ~spl3_22),
% 2.58/0.72    inference(avatar_split_clause,[],[f290,f211,f122,f303,f308])).
% 2.58/0.72  fof(f308,plain,(
% 2.58/0.72    spl3_39 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,sK1) | ~r1_tarski(sK1,X0))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 2.58/0.72  fof(f290,plain,(
% 2.58/0.72    ( ! [X0,X1] : (r1_tarski(sK1,sK1) | ~r1_tarski(X0,X1) | ~r1_tarski(sK1,X0) | ~r1_tarski(X1,sK1)) ) | (~spl3_14 | ~spl3_22)),
% 2.58/0.72    inference(superposition,[],[f123,f213])).
% 2.58/0.72  fof(f306,plain,(
% 2.58/0.72    spl3_38 | ~spl3_8 | ~spl3_22),
% 2.58/0.72    inference(avatar_split_clause,[],[f289,f211,f77,f303])).
% 2.58/0.72  fof(f77,plain,(
% 2.58/0.72    spl3_8 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.58/0.72  fof(f289,plain,(
% 2.58/0.72    r1_tarski(sK1,sK1) | (~spl3_8 | ~spl3_22)),
% 2.58/0.72    inference(superposition,[],[f79,f213])).
% 2.58/0.72  fof(f79,plain,(
% 2.58/0.72    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl3_8),
% 2.58/0.72    inference(avatar_component_clause,[],[f77])).
% 2.58/0.72  fof(f300,plain,(
% 2.58/0.72    ~spl3_37 | spl3_20 | ~spl3_22),
% 2.58/0.72    inference(avatar_split_clause,[],[f287,f211,f184,f297])).
% 2.58/0.72  fof(f184,plain,(
% 2.58/0.72    spl3_20 <=> r1_tarski(k2_pre_topc(sK0,sK1),sK2)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 2.58/0.72  fof(f287,plain,(
% 2.58/0.72    ~r1_tarski(sK1,sK2) | (spl3_20 | ~spl3_22)),
% 2.58/0.72    inference(superposition,[],[f186,f213])).
% 2.58/0.72  fof(f186,plain,(
% 2.58/0.72    ~r1_tarski(k2_pre_topc(sK0,sK1),sK2) | spl3_20),
% 2.58/0.72    inference(avatar_component_clause,[],[f184])).
% 2.58/0.72  fof(f286,plain,(
% 2.58/0.72    ~spl3_36 | spl3_31 | ~spl3_10 | ~spl3_21),
% 2.58/0.72    inference(avatar_split_clause,[],[f253,f206,f98,f262,f283])).
% 2.58/0.72  fof(f262,plain,(
% 2.58/0.72    spl3_31 <=> r1_tarski(sK2,sK2)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 2.58/0.72  fof(f98,plain,(
% 2.58/0.72    spl3_10 <=> ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(X0,k2_pre_topc(sK0,X0)))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.58/0.72  fof(f253,plain,(
% 2.58/0.72    r1_tarski(sK2,sK2) | ~r1_tarski(sK2,sK1) | (~spl3_10 | ~spl3_21)),
% 2.58/0.72    inference(superposition,[],[f99,f208])).
% 2.58/0.72  fof(f99,plain,(
% 2.58/0.72    ( ! [X0] : (r1_tarski(X0,k2_pre_topc(sK0,X0)) | ~r1_tarski(X0,sK1)) ) | ~spl3_10),
% 2.58/0.72    inference(avatar_component_clause,[],[f98])).
% 2.58/0.72  fof(f281,plain,(
% 2.58/0.72    spl3_35 | spl3_31 | ~spl3_11 | ~spl3_21),
% 2.58/0.72    inference(avatar_split_clause,[],[f252,f206,f104,f262,f279])).
% 2.58/0.72  fof(f279,plain,(
% 2.58/0.72    spl3_35 <=> ! [X5] : (~r1_tarski(X5,sK2) | ~r1_tarski(sK2,X5))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 2.58/0.72  fof(f252,plain,(
% 2.58/0.72    ( ! [X5] : (r1_tarski(sK2,sK2) | ~r1_tarski(X5,sK2) | ~r1_tarski(sK2,X5)) ) | (~spl3_11 | ~spl3_21)),
% 2.58/0.72    inference(superposition,[],[f105,f208])).
% 2.58/0.72  fof(f277,plain,(
% 2.58/0.72    spl3_34 | spl3_31 | ~spl3_12 | ~spl3_21),
% 2.58/0.72    inference(avatar_split_clause,[],[f251,f206,f110,f262,f275])).
% 2.58/0.72  fof(f275,plain,(
% 2.58/0.72    spl3_34 <=> ! [X4] : (~r1_tarski(X4,sK1) | ~r1_tarski(sK2,X4))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 2.58/0.72  fof(f251,plain,(
% 2.58/0.72    ( ! [X4] : (r1_tarski(sK2,sK2) | ~r1_tarski(X4,sK1) | ~r1_tarski(sK2,X4)) ) | (~spl3_12 | ~spl3_21)),
% 2.58/0.72    inference(superposition,[],[f111,f208])).
% 2.58/0.72  fof(f273,plain,(
% 2.58/0.72    spl3_33 | spl3_31 | ~spl3_13 | ~spl3_21),
% 2.58/0.72    inference(avatar_split_clause,[],[f250,f206,f116,f262,f271])).
% 2.58/0.72  fof(f271,plain,(
% 2.58/0.72    spl3_33 <=> ! [X3,X2] : (~r1_tarski(X2,X3) | ~r1_tarski(X3,sK2) | ~r1_tarski(sK2,X2))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 2.58/0.72  fof(f250,plain,(
% 2.58/0.72    ( ! [X2,X3] : (r1_tarski(sK2,sK2) | ~r1_tarski(X2,X3) | ~r1_tarski(sK2,X2) | ~r1_tarski(X3,sK2)) ) | (~spl3_13 | ~spl3_21)),
% 2.58/0.72    inference(superposition,[],[f117,f208])).
% 2.58/0.72  fof(f269,plain,(
% 2.58/0.72    spl3_32 | spl3_31 | ~spl3_14 | ~spl3_21),
% 2.58/0.72    inference(avatar_split_clause,[],[f249,f206,f122,f262,f267])).
% 2.58/0.72  fof(f267,plain,(
% 2.58/0.72    spl3_32 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,sK1) | ~r1_tarski(sK2,X0))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 2.58/0.72  fof(f249,plain,(
% 2.58/0.72    ( ! [X0,X1] : (r1_tarski(sK2,sK2) | ~r1_tarski(X0,X1) | ~r1_tarski(sK2,X0) | ~r1_tarski(X1,sK1)) ) | (~spl3_14 | ~spl3_21)),
% 2.58/0.72    inference(superposition,[],[f123,f208])).
% 2.58/0.72  fof(f265,plain,(
% 2.58/0.72    spl3_31 | ~spl3_7 | ~spl3_21),
% 2.58/0.72    inference(avatar_split_clause,[],[f248,f206,f72,f262])).
% 2.58/0.72  fof(f72,plain,(
% 2.58/0.72    spl3_7 <=> r1_tarski(sK2,k2_pre_topc(sK0,sK2))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.58/0.72  fof(f248,plain,(
% 2.58/0.72    r1_tarski(sK2,sK2) | (~spl3_7 | ~spl3_21)),
% 2.58/0.72    inference(superposition,[],[f74,f208])).
% 2.58/0.72  fof(f74,plain,(
% 2.58/0.72    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | ~spl3_7),
% 2.58/0.72    inference(avatar_component_clause,[],[f72])).
% 2.58/0.72  fof(f260,plain,(
% 2.58/0.72    ~spl3_30 | spl3_1 | ~spl3_21 | ~spl3_22),
% 2.58/0.72    inference(avatar_split_clause,[],[f255,f211,f206,f39,f257])).
% 2.58/0.72  fof(f257,plain,(
% 2.58/0.72    spl3_30 <=> k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 2.58/0.72  fof(f39,plain,(
% 2.58/0.72    spl3_1 <=> k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.58/0.72  fof(f255,plain,(
% 2.58/0.72    k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) | (spl3_1 | ~spl3_21 | ~spl3_22)),
% 2.58/0.72    inference(forward_demodulation,[],[f247,f213])).
% 2.58/0.72  fof(f247,plain,(
% 2.58/0.72    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK2) | (spl3_1 | ~spl3_21)),
% 2.58/0.72    inference(superposition,[],[f41,f208])).
% 2.58/0.72  fof(f41,plain,(
% 2.58/0.72    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) | spl3_1),
% 2.58/0.72    inference(avatar_component_clause,[],[f39])).
% 2.58/0.72  fof(f245,plain,(
% 2.58/0.72    ~spl3_29 | spl3_16 | ~spl3_21 | ~spl3_22),
% 2.58/0.72    inference(avatar_split_clause,[],[f240,f211,f206,f159,f242])).
% 2.58/0.72  fof(f159,plain,(
% 2.58/0.72    spl3_16 <=> k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = k3_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 2.58/0.72  fof(f240,plain,(
% 2.58/0.72    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_xboole_0(sK2,sK1) | (spl3_16 | ~spl3_21 | ~spl3_22)),
% 2.58/0.72    inference(forward_demodulation,[],[f239,f208])).
% 2.58/0.72  fof(f239,plain,(
% 2.58/0.72    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_xboole_0(k2_pre_topc(sK0,sK2),sK1) | (spl3_16 | ~spl3_22)),
% 2.58/0.72    inference(forward_demodulation,[],[f161,f213])).
% 2.58/0.72  fof(f161,plain,(
% 2.58/0.72    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) | spl3_16),
% 2.58/0.72    inference(avatar_component_clause,[],[f159])).
% 2.58/0.72  fof(f238,plain,(
% 2.58/0.72    ~spl3_6 | spl3_28 | ~spl3_4),
% 2.58/0.72    inference(avatar_split_clause,[],[f201,f54,f236,f64])).
% 2.58/0.72  fof(f201,plain,(
% 2.58/0.72    ( ! [X11] : (~v4_pre_topc(X11,sK0) | k2_pre_topc(sK0,X11) = X11 | ~l1_pre_topc(sK0) | ~r1_tarski(X11,sK2)) ) | ~spl3_4),
% 2.58/0.72    inference(resolution,[],[f31,f85])).
% 2.58/0.72  fof(f234,plain,(
% 2.58/0.72    ~spl3_6 | spl3_27 | ~spl3_5),
% 2.58/0.72    inference(avatar_split_clause,[],[f200,f59,f232,f64])).
% 2.58/0.72  fof(f200,plain,(
% 2.58/0.72    ( ! [X10] : (~v4_pre_topc(X10,sK0) | k2_pre_topc(sK0,X10) = X10 | ~l1_pre_topc(sK0) | ~r1_tarski(X10,sK1)) ) | ~spl3_5),
% 2.58/0.72    inference(resolution,[],[f31,f86])).
% 2.58/0.72  fof(f230,plain,(
% 2.58/0.72    ~spl3_6 | spl3_26 | ~spl3_4),
% 2.58/0.72    inference(avatar_split_clause,[],[f199,f54,f228,f64])).
% 2.58/0.72  fof(f199,plain,(
% 2.58/0.72    ( ! [X8,X9] : (~v4_pre_topc(X8,sK0) | k2_pre_topc(sK0,X8) = X8 | ~l1_pre_topc(sK0) | ~r1_tarski(X9,sK2) | ~r1_tarski(X8,X9)) ) | ~spl3_4),
% 2.58/0.72    inference(resolution,[],[f31,f90])).
% 2.58/0.72  fof(f226,plain,(
% 2.58/0.72    ~spl3_6 | spl3_25 | ~spl3_5),
% 2.58/0.72    inference(avatar_split_clause,[],[f198,f59,f224,f64])).
% 2.58/0.72  fof(f198,plain,(
% 2.58/0.72    ( ! [X6,X7] : (~v4_pre_topc(X6,sK0) | k2_pre_topc(sK0,X6) = X6 | ~l1_pre_topc(sK0) | ~r1_tarski(X7,sK1) | ~r1_tarski(X6,X7)) ) | ~spl3_5),
% 2.58/0.72    inference(resolution,[],[f31,f96])).
% 2.58/0.72  fof(f222,plain,(
% 2.58/0.72    ~spl3_6 | spl3_24 | ~spl3_4),
% 2.58/0.72    inference(avatar_split_clause,[],[f197,f54,f220,f64])).
% 2.58/0.72  fof(f197,plain,(
% 2.58/0.72    ( ! [X4,X5,X3] : (~v4_pre_topc(X3,sK0) | k2_pre_topc(sK0,X3) = X3 | ~l1_pre_topc(sK0) | ~r1_tarski(X4,X5) | ~r1_tarski(X5,sK2) | ~r1_tarski(X3,X4)) ) | ~spl3_4),
% 2.58/0.72    inference(resolution,[],[f31,f102])).
% 2.58/0.72  fof(f218,plain,(
% 2.58/0.72    ~spl3_6 | spl3_23 | ~spl3_5),
% 2.58/0.72    inference(avatar_split_clause,[],[f196,f59,f216,f64])).
% 2.58/0.72  fof(f196,plain,(
% 2.58/0.72    ( ! [X2,X0,X1] : (~v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) = X0 | ~l1_pre_topc(sK0) | ~r1_tarski(X1,X2) | ~r1_tarski(X2,sK1) | ~r1_tarski(X0,X1)) ) | ~spl3_5),
% 2.58/0.72    inference(resolution,[],[f31,f108])).
% 2.58/0.72  fof(f214,plain,(
% 2.58/0.72    ~spl3_6 | spl3_22 | ~spl3_3 | ~spl3_5),
% 2.58/0.72    inference(avatar_split_clause,[],[f195,f59,f49,f211,f64])).
% 2.58/0.72  fof(f49,plain,(
% 2.58/0.72    spl3_3 <=> v4_pre_topc(sK1,sK0)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.58/0.72  fof(f195,plain,(
% 2.58/0.72    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | ~spl3_5),
% 2.58/0.72    inference(resolution,[],[f31,f61])).
% 2.58/0.72  fof(f209,plain,(
% 2.58/0.72    ~spl3_6 | spl3_21 | ~spl3_2 | ~spl3_4),
% 2.58/0.72    inference(avatar_split_clause,[],[f194,f54,f44,f206,f64])).
% 2.58/0.72  fof(f44,plain,(
% 2.58/0.72    spl3_2 <=> v4_pre_topc(sK2,sK0)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.58/0.72  fof(f194,plain,(
% 2.58/0.72    ~v4_pre_topc(sK2,sK0) | sK2 = k2_pre_topc(sK0,sK2) | ~l1_pre_topc(sK0) | ~spl3_4),
% 2.58/0.72    inference(resolution,[],[f31,f56])).
% 2.58/0.72  fof(f187,plain,(
% 2.58/0.72    ~spl3_20 | ~spl3_4 | spl3_15),
% 2.58/0.72    inference(avatar_split_clause,[],[f177,f155,f54,f184])).
% 2.58/0.72  fof(f155,plain,(
% 2.58/0.72    spl3_15 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 2.58/0.72  fof(f177,plain,(
% 2.58/0.72    ~r1_tarski(k2_pre_topc(sK0,sK1),sK2) | (~spl3_4 | spl3_15)),
% 2.58/0.72    inference(resolution,[],[f157,f85])).
% 2.58/0.72  fof(f157,plain,(
% 2.58/0.72    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_15),
% 2.58/0.72    inference(avatar_component_clause,[],[f155])).
% 2.58/0.72  fof(f182,plain,(
% 2.58/0.72    ~spl3_19 | ~spl3_5 | spl3_15),
% 2.58/0.72    inference(avatar_split_clause,[],[f176,f155,f59,f179])).
% 2.58/0.72  fof(f179,plain,(
% 2.58/0.72    spl3_19 <=> r1_tarski(k2_pre_topc(sK0,sK1),sK1)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 2.58/0.72  fof(f176,plain,(
% 2.58/0.72    ~r1_tarski(k2_pre_topc(sK0,sK1),sK1) | (~spl3_5 | spl3_15)),
% 2.58/0.72    inference(resolution,[],[f157,f86])).
% 2.58/0.72  fof(f171,plain,(
% 2.58/0.72    ~spl3_17 | ~spl3_18 | spl3_1),
% 2.58/0.72    inference(avatar_split_clause,[],[f153,f39,f168,f164])).
% 2.58/0.72  fof(f164,plain,(
% 2.58/0.72    spl3_17 <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 2.58/0.72  fof(f168,plain,(
% 2.58/0.72    spl3_18 <=> k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.58/0.72  fof(f153,plain,(
% 2.58/0.72    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) | ~m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_1),
% 2.58/0.72    inference(superposition,[],[f41,f36])).
% 2.58/0.72  fof(f162,plain,(
% 2.58/0.72    ~spl3_15 | ~spl3_16 | spl3_1),
% 2.58/0.72    inference(avatar_split_clause,[],[f152,f39,f159,f155])).
% 2.58/0.72  fof(f152,plain,(
% 2.58/0.72    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_1),
% 2.58/0.72    inference(superposition,[],[f41,f133])).
% 2.58/0.72  fof(f124,plain,(
% 2.58/0.72    ~spl3_6 | spl3_14 | ~spl3_5),
% 2.58/0.72    inference(avatar_split_clause,[],[f119,f59,f122,f64])).
% 2.58/0.72  fof(f119,plain,(
% 2.58/0.72    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,sK1) | ~r1_tarski(X2,X0) | r1_tarski(X2,k2_pre_topc(sK0,X2)) | ~l1_pre_topc(sK0)) ) | ~spl3_5),
% 2.58/0.72    inference(resolution,[],[f108,f30])).
% 2.58/0.72  fof(f118,plain,(
% 2.58/0.72    ~spl3_6 | spl3_13 | ~spl3_4),
% 2.58/0.72    inference(avatar_split_clause,[],[f113,f54,f116,f64])).
% 2.58/0.72  fof(f113,plain,(
% 2.58/0.72    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,sK2) | ~r1_tarski(X2,X0) | r1_tarski(X2,k2_pre_topc(sK0,X2)) | ~l1_pre_topc(sK0)) ) | ~spl3_4),
% 2.58/0.72    inference(resolution,[],[f102,f30])).
% 2.58/0.72  fof(f112,plain,(
% 2.58/0.72    ~spl3_6 | spl3_12 | ~spl3_5),
% 2.58/0.72    inference(avatar_split_clause,[],[f107,f59,f110,f64])).
% 2.58/0.72  fof(f107,plain,(
% 2.58/0.72    ( ! [X0,X1] : (~r1_tarski(X0,sK1) | ~r1_tarski(X1,X0) | r1_tarski(X1,k2_pre_topc(sK0,X1)) | ~l1_pre_topc(sK0)) ) | ~spl3_5),
% 2.58/0.72    inference(resolution,[],[f96,f30])).
% 2.58/0.72  fof(f106,plain,(
% 2.58/0.72    ~spl3_6 | spl3_11 | ~spl3_4),
% 2.58/0.72    inference(avatar_split_clause,[],[f101,f54,f104,f64])).
% 2.58/0.72  fof(f101,plain,(
% 2.58/0.72    ( ! [X0,X1] : (~r1_tarski(X0,sK2) | ~r1_tarski(X1,X0) | r1_tarski(X1,k2_pre_topc(sK0,X1)) | ~l1_pre_topc(sK0)) ) | ~spl3_4),
% 2.58/0.72    inference(resolution,[],[f90,f30])).
% 2.58/0.72  fof(f100,plain,(
% 2.58/0.72    ~spl3_6 | spl3_10 | ~spl3_5),
% 2.58/0.72    inference(avatar_split_clause,[],[f95,f59,f98,f64])).
% 2.58/0.72  fof(f95,plain,(
% 2.58/0.72    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(X0,k2_pre_topc(sK0,X0)) | ~l1_pre_topc(sK0)) ) | ~spl3_5),
% 2.58/0.72    inference(resolution,[],[f86,f30])).
% 2.58/0.72  fof(f94,plain,(
% 2.58/0.72    ~spl3_6 | spl3_9 | ~spl3_4),
% 2.58/0.72    inference(avatar_split_clause,[],[f89,f54,f92,f64])).
% 2.58/0.72  fof(f89,plain,(
% 2.58/0.72    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(X0,k2_pre_topc(sK0,X0)) | ~l1_pre_topc(sK0)) ) | ~spl3_4),
% 2.58/0.72    inference(resolution,[],[f85,f30])).
% 2.58/0.72  fof(f80,plain,(
% 2.58/0.72    ~spl3_6 | spl3_8 | ~spl3_5),
% 2.58/0.72    inference(avatar_split_clause,[],[f69,f59,f77,f64])).
% 2.58/0.72  fof(f69,plain,(
% 2.58/0.72    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl3_5),
% 2.58/0.72    inference(resolution,[],[f30,f61])).
% 2.58/0.72  fof(f75,plain,(
% 2.58/0.72    ~spl3_6 | spl3_7 | ~spl3_4),
% 2.58/0.72    inference(avatar_split_clause,[],[f68,f54,f72,f64])).
% 2.58/0.72  fof(f68,plain,(
% 2.58/0.72    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0) | ~spl3_4),
% 2.58/0.72    inference(resolution,[],[f30,f56])).
% 2.58/0.72  fof(f67,plain,(
% 2.58/0.72    spl3_6),
% 2.58/0.72    inference(avatar_split_clause,[],[f24,f64])).
% 2.58/0.72  fof(f24,plain,(
% 2.58/0.72    l1_pre_topc(sK0)),
% 2.58/0.72    inference(cnf_transformation,[],[f23])).
% 2.58/0.72  fof(f23,plain,(
% 2.58/0.72    ((k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) & v4_pre_topc(sK2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.58/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f22,f21,f20])).
% 2.58/0.72  fof(f20,plain,(
% 2.58/0.72    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)) & v4_pre_topc(X2,sK0) & v4_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.58/0.72    introduced(choice_axiom,[])).
% 2.58/0.72  fof(f21,plain,(
% 2.58/0.72    ? [X1] : (? [X2] : (k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)) & v4_pre_topc(X2,sK0) & v4_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)) & v4_pre_topc(X2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.72    introduced(choice_axiom,[])).
% 2.58/0.72  fof(f22,plain,(
% 2.58/0.72    ? [X2] : (k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)) & v4_pre_topc(X2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) & v4_pre_topc(sK2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.58/0.72    introduced(choice_axiom,[])).
% 2.58/0.72  fof(f11,plain,(
% 2.58/0.72    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.58/0.72    inference(flattening,[],[f10])).
% 2.58/0.72  fof(f10,plain,(
% 2.58/0.72    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & (v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.58/0.72    inference(ennf_transformation,[],[f9])).
% 2.58/0.72  fof(f9,negated_conjecture,(
% 2.58/0.72    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 2.58/0.72    inference(negated_conjecture,[],[f8])).
% 2.58/0.72  fof(f8,conjecture,(
% 2.58/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_1)).
% 2.58/0.72  fof(f62,plain,(
% 2.58/0.72    spl3_5),
% 2.58/0.72    inference(avatar_split_clause,[],[f25,f59])).
% 2.58/0.72  fof(f25,plain,(
% 2.58/0.72    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.58/0.72    inference(cnf_transformation,[],[f23])).
% 2.58/0.72  fof(f57,plain,(
% 2.58/0.72    spl3_4),
% 2.58/0.72    inference(avatar_split_clause,[],[f26,f54])).
% 2.58/0.72  fof(f26,plain,(
% 2.58/0.72    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.58/0.72    inference(cnf_transformation,[],[f23])).
% 2.58/0.72  fof(f52,plain,(
% 2.58/0.72    spl3_3),
% 2.58/0.72    inference(avatar_split_clause,[],[f27,f49])).
% 2.58/0.72  fof(f27,plain,(
% 2.58/0.72    v4_pre_topc(sK1,sK0)),
% 2.58/0.72    inference(cnf_transformation,[],[f23])).
% 2.58/0.72  fof(f47,plain,(
% 2.58/0.72    spl3_2),
% 2.58/0.72    inference(avatar_split_clause,[],[f28,f44])).
% 2.58/0.72  fof(f28,plain,(
% 2.58/0.72    v4_pre_topc(sK2,sK0)),
% 2.58/0.72    inference(cnf_transformation,[],[f23])).
% 2.58/0.72  fof(f42,plain,(
% 2.58/0.72    ~spl3_1),
% 2.58/0.72    inference(avatar_split_clause,[],[f29,f39])).
% 2.58/0.72  fof(f29,plain,(
% 2.58/0.72    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),
% 2.58/0.72    inference(cnf_transformation,[],[f23])).
% 2.58/0.72  % SZS output end Proof for theBenchmark
% 2.58/0.72  % (31334)------------------------------
% 2.58/0.72  % (31334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.58/0.72  % (31334)Termination reason: Refutation
% 2.58/0.72  
% 2.58/0.72  % (31334)Memory used [KB]: 6652
% 2.58/0.72  % (31334)Time elapsed: 0.268 s
% 2.58/0.72  % (31334)------------------------------
% 2.58/0.72  % (31334)------------------------------
% 2.58/0.73  % (31329)Success in time 0.353 s
%------------------------------------------------------------------------------
