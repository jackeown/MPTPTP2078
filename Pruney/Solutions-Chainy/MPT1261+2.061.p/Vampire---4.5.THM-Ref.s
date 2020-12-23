%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 371 expanded)
%              Number of leaves         :   55 ( 174 expanded)
%              Depth                    :   10
%              Number of atoms          :  586 (1169 expanded)
%              Number of equality atoms :  142 ( 304 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f732,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f83,f92,f94,f98,f102,f106,f110,f115,f119,f123,f127,f131,f135,f156,f167,f175,f184,f191,f196,f211,f221,f238,f256,f268,f273,f276,f293,f300,f334,f402,f530,f572,f656,f696,f728])).

fof(f728,plain,
    ( ~ spl2_7
    | ~ spl2_14
    | spl2_29
    | ~ spl2_54
    | ~ spl2_71
    | ~ spl2_74 ),
    inference(avatar_contradiction_clause,[],[f727])).

fof(f727,plain,
    ( $false
    | ~ spl2_7
    | ~ spl2_14
    | spl2_29
    | ~ spl2_54
    | ~ spl2_71
    | ~ spl2_74 ),
    inference(subsumption_resolution,[],[f237,f726])).

fof(f726,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_7
    | ~ spl2_14
    | ~ spl2_54
    | ~ spl2_71
    | ~ spl2_74 ),
    inference(forward_demodulation,[],[f722,f712])).

fof(f712,plain,
    ( ! [X4] : k5_xboole_0(X4,k1_xboole_0) = X4
    | ~ spl2_7
    | ~ spl2_14
    | ~ spl2_74 ),
    inference(forward_demodulation,[],[f706,f97])).

fof(f97,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl2_7
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f706,plain,
    ( ! [X4] : k2_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0)
    | ~ spl2_14
    | ~ spl2_74 ),
    inference(superposition,[],[f126,f695])).

fof(f695,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_74 ),
    inference(avatar_component_clause,[],[f694])).

fof(f694,plain,
    ( spl2_74
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).

fof(f126,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl2_14
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f722,plain,
    ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_54
    | ~ spl2_71 ),
    inference(superposition,[],[f655,f529])).

fof(f529,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f527])).

fof(f527,plain,
    ( spl2_54
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f655,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_71 ),
    inference(avatar_component_clause,[],[f653])).

fof(f653,plain,
    ( spl2_71
  <=> k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f237,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_29 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl2_29
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f696,plain,
    ( spl2_74
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f303,f298,f133,f129,f104,f100,f694])).

fof(f100,plain,
    ( spl2_8
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f104,plain,
    ( spl2_9
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f129,plain,
    ( spl2_15
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f133,plain,
    ( spl2_16
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f298,plain,
    ( spl2_35
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f303,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_35 ),
    inference(forward_demodulation,[],[f302,f105])).

fof(f105,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f302,plain,
    ( ! [X0] : k3_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_35 ),
    inference(forward_demodulation,[],[f301,f151])).

fof(f151,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0)
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f149,f145])).

fof(f145,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(superposition,[],[f130,f101])).

fof(f101,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f130,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f149,plain,
    ( ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)
    | ~ spl2_9
    | ~ spl2_16 ),
    inference(superposition,[],[f134,f105])).

fof(f134,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f133])).

fof(f301,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_16
    | ~ spl2_35 ),
    inference(superposition,[],[f134,f299])).

fof(f299,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f298])).

fof(f656,plain,
    ( spl2_71
    | ~ spl2_14
    | ~ spl2_61 ),
    inference(avatar_split_clause,[],[f613,f569,f125,f653])).

fof(f569,plain,
    ( spl2_61
  <=> k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).

fof(f613,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_14
    | ~ spl2_61 ),
    inference(superposition,[],[f126,f571])).

fof(f571,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_61 ),
    inference(avatar_component_clause,[],[f569])).

fof(f572,plain,
    ( spl2_61
    | ~ spl2_12
    | ~ spl2_34
    | ~ spl2_35
    | ~ spl2_39
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f422,f400,f332,f298,f290,f117,f569])).

fof(f117,plain,
    ( spl2_12
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f290,plain,
    ( spl2_34
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f332,plain,
    ( spl2_39
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f400,plain,
    ( spl2_45
  <=> ! [X1,X2] :
        ( k4_xboole_0(X1,X2) = k3_xboole_0(X1,k1_xboole_0)
        | ~ r1_tarski(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f422,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_12
    | ~ spl2_34
    | ~ spl2_35
    | ~ spl2_39
    | ~ spl2_45 ),
    inference(forward_demodulation,[],[f421,f299])).

fof(f421,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k3_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1))
    | ~ spl2_12
    | ~ spl2_34
    | ~ spl2_39
    | ~ spl2_45 ),
    inference(forward_demodulation,[],[f407,f337])).

fof(f337,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl2_12
    | ~ spl2_39 ),
    inference(superposition,[],[f333,f118])).

fof(f118,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f333,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f332])).

fof(f407,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0)
    | ~ spl2_34
    | ~ spl2_45 ),
    inference(unit_resulting_resolution,[],[f292,f401])).

fof(f401,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = k3_xboole_0(X1,k1_xboole_0)
        | ~ r1_tarski(X1,X2) )
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f400])).

fof(f292,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f290])).

fof(f530,plain,
    ( spl2_54
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_23
    | ~ spl2_25
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f233,f218,f194,f182,f76,f71,f527])).

fof(f71,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f76,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f182,plain,
    ( spl2_23
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f194,plain,
    ( spl2_25
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f218,plain,
    ( spl2_28
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f233,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_23
    | ~ spl2_25
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f228,f203])).

fof(f203,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_25 ),
    inference(unit_resulting_resolution,[],[f73,f78,f195])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f194])).

fof(f78,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f73,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f228,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_23
    | ~ spl2_28 ),
    inference(unit_resulting_resolution,[],[f78,f220,f183])).

fof(f183,plain,
    ( ! [X2,X0,X1] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f182])).

fof(f220,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f218])).

fof(f402,plain,
    ( spl2_45
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f152,f133,f129,f121,f104,f100,f400])).

fof(f121,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f152,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = k3_xboole_0(X1,k1_xboole_0)
        | ~ r1_tarski(X1,X2) )
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f150,f151])).

fof(f150,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1)
        | ~ r1_tarski(X1,X2) )
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(superposition,[],[f134,f122])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f334,plain,
    ( spl2_39
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f136,f117,f113,f332])).

fof(f113,plain,
    ( spl2_11
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f136,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(superposition,[],[f118,f114])).

fof(f114,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f300,plain,
    ( spl2_35
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f142,f121,f81,f298])).

fof(f81,plain,
    ( spl2_4
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f142,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(unit_resulting_resolution,[],[f82,f122])).

fof(f82,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f293,plain,
    ( spl2_34
    | ~ spl2_10
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f288,f253,f108,f290])).

fof(f108,plain,
    ( spl2_10
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f253,plain,
    ( spl2_32
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f288,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_10
    | ~ spl2_32 ),
    inference(superposition,[],[f109,f255])).

fof(f255,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f253])).

fof(f109,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f276,plain,
    ( spl2_6
    | ~ spl2_29
    | ~ spl2_33 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | spl2_6
    | ~ spl2_29
    | ~ spl2_33 ),
    inference(subsumption_resolution,[],[f90,f274])).

fof(f274,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_29
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f272,f236])).

fof(f236,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f235])).

fof(f272,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl2_33
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f90,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f273,plain,
    ( spl2_33
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f212,f209,f76,f71,f270])).

fof(f209,plain,
    ( spl2_27
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f212,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_27 ),
    inference(unit_resulting_resolution,[],[f73,f78,f210])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f209])).

fof(f268,plain,
    ( ~ spl2_2
    | spl2_29
    | ~ spl2_5
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f185,f173,f76,f85,f235,f71])).

fof(f85,plain,
    ( spl2_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f173,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = X1
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f185,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(resolution,[],[f174,f78])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) = X1
        | ~ l1_pre_topc(X0) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f173])).

fof(f256,plain,
    ( ~ spl2_3
    | spl2_32
    | ~ spl2_6
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f158,f154,f89,f253,f76])).

fof(f154,plain,
    ( spl2_18
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f158,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6
    | ~ spl2_18 ),
    inference(superposition,[],[f155,f91])).

fof(f91,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f155,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f154])).

fof(f238,plain,
    ( ~ spl2_29
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_5
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f202,f189,f85,f76,f71,f66,f235])).

fof(f66,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f189,plain,
    ( spl2_24
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) != X1
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f202,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_5
    | ~ spl2_24 ),
    inference(unit_resulting_resolution,[],[f73,f68,f86,f78,f190])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) != X1
        | v4_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f189])).

fof(f86,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f68,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f221,plain,
    ( spl2_28
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f178,f165,f76,f71,f218])).

fof(f165,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f178,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(unit_resulting_resolution,[],[f73,f78,f166])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f165])).

fof(f211,plain,(
    spl2_27 ),
    inference(avatar_split_clause,[],[f50,f209])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f196,plain,(
    spl2_25 ),
    inference(avatar_split_clause,[],[f49,f194])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f191,plain,(
    spl2_24 ),
    inference(avatar_split_clause,[],[f52,f189])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f184,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f64,f182])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f175,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f51,f173])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f167,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f62,f165])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f156,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f63,f154])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f135,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f59,f133])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f131,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f58,f129])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f127,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f57,f125])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f123,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f60,f121])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f119,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f56,f117])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f115,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f55,f113])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f110,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f54,f108])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f106,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f53,f104])).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f102,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f48,f100])).

fof(f48,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f98,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f47,f96])).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f94,plain,
    ( ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f93,f89,f85])).

fof(f93,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f45,f91])).

fof(f45,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).

fof(f38,plain,
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

fof(f39,plain,
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

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f92,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f44,f89,f85])).

fof(f44,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f83,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f46,f81])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f79,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f43,f76])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f42,f71])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f41,f66])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:45:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (11287)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (11283)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (11289)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (11290)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (11295)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (11284)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (11292)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (11291)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (11298)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (11301)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (11299)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (11289)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f732,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f69,f74,f79,f83,f92,f94,f98,f102,f106,f110,f115,f119,f123,f127,f131,f135,f156,f167,f175,f184,f191,f196,f211,f221,f238,f256,f268,f273,f276,f293,f300,f334,f402,f530,f572,f656,f696,f728])).
% 0.21/0.49  fof(f728,plain,(
% 0.21/0.49    ~spl2_7 | ~spl2_14 | spl2_29 | ~spl2_54 | ~spl2_71 | ~spl2_74),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f727])).
% 0.21/0.49  fof(f727,plain,(
% 0.21/0.49    $false | (~spl2_7 | ~spl2_14 | spl2_29 | ~spl2_54 | ~spl2_71 | ~spl2_74)),
% 0.21/0.49    inference(subsumption_resolution,[],[f237,f726])).
% 0.21/0.49  fof(f726,plain,(
% 0.21/0.49    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_7 | ~spl2_14 | ~spl2_54 | ~spl2_71 | ~spl2_74)),
% 0.21/0.49    inference(forward_demodulation,[],[f722,f712])).
% 0.21/0.49  fof(f712,plain,(
% 0.21/0.49    ( ! [X4] : (k5_xboole_0(X4,k1_xboole_0) = X4) ) | (~spl2_7 | ~spl2_14 | ~spl2_74)),
% 0.21/0.49    inference(forward_demodulation,[],[f706,f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl2_7 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.49  fof(f706,plain,(
% 0.21/0.49    ( ! [X4] : (k2_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0)) ) | (~spl2_14 | ~spl2_74)),
% 0.21/0.49    inference(superposition,[],[f126,f695])).
% 0.21/0.49  fof(f695,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl2_74),
% 0.21/0.49    inference(avatar_component_clause,[],[f694])).
% 0.21/0.49  fof(f694,plain,(
% 0.21/0.49    spl2_74 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl2_14 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.49  fof(f722,plain,(
% 0.21/0.49    k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0) | (~spl2_54 | ~spl2_71)),
% 0.21/0.49    inference(superposition,[],[f655,f529])).
% 0.21/0.49  fof(f529,plain,(
% 0.21/0.49    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_54),
% 0.21/0.49    inference(avatar_component_clause,[],[f527])).
% 0.21/0.49  fof(f527,plain,(
% 0.21/0.49    spl2_54 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 0.21/0.49  fof(f655,plain,(
% 0.21/0.49    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0) | ~spl2_71),
% 0.21/0.49    inference(avatar_component_clause,[],[f653])).
% 0.21/0.49  fof(f653,plain,(
% 0.21/0.49    spl2_71 <=> k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    sK1 != k2_pre_topc(sK0,sK1) | spl2_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f235])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    spl2_29 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.49  fof(f696,plain,(
% 0.21/0.49    spl2_74 | ~spl2_8 | ~spl2_9 | ~spl2_15 | ~spl2_16 | ~spl2_35),
% 0.21/0.49    inference(avatar_split_clause,[],[f303,f298,f133,f129,f104,f100,f694])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl2_8 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl2_9 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    spl2_15 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    spl2_16 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    spl2_35 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.21/0.49  fof(f303,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl2_8 | ~spl2_9 | ~spl2_15 | ~spl2_16 | ~spl2_35)),
% 0.21/0.49    inference(forward_demodulation,[],[f302,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl2_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f104])).
% 0.21/0.49  fof(f302,plain,(
% 0.21/0.49    ( ! [X0] : (k3_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl2_8 | ~spl2_9 | ~spl2_15 | ~spl2_16 | ~spl2_35)),
% 0.21/0.49    inference(forward_demodulation,[],[f301,f151])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0)) ) | (~spl2_8 | ~spl2_9 | ~spl2_15 | ~spl2_16)),
% 0.21/0.49    inference(forward_demodulation,[],[f149,f145])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) ) | (~spl2_8 | ~spl2_15)),
% 0.21/0.49    inference(superposition,[],[f130,f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f100])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f129])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) ) | (~spl2_9 | ~spl2_16)),
% 0.21/0.49    inference(superposition,[],[f134,f105])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f133])).
% 0.21/0.49  fof(f301,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) ) | (~spl2_16 | ~spl2_35)),
% 0.21/0.49    inference(superposition,[],[f134,f299])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl2_35),
% 0.21/0.49    inference(avatar_component_clause,[],[f298])).
% 0.21/0.49  fof(f656,plain,(
% 0.21/0.49    spl2_71 | ~spl2_14 | ~spl2_61),
% 0.21/0.49    inference(avatar_split_clause,[],[f613,f569,f125,f653])).
% 0.21/0.49  fof(f569,plain,(
% 0.21/0.49    spl2_61 <=> k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).
% 0.21/0.49  fof(f613,plain,(
% 0.21/0.49    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0) | (~spl2_14 | ~spl2_61)),
% 0.21/0.49    inference(superposition,[],[f126,f571])).
% 0.21/0.49  fof(f571,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_61),
% 0.21/0.49    inference(avatar_component_clause,[],[f569])).
% 0.21/0.49  fof(f572,plain,(
% 0.21/0.49    spl2_61 | ~spl2_12 | ~spl2_34 | ~spl2_35 | ~spl2_39 | ~spl2_45),
% 0.21/0.49    inference(avatar_split_clause,[],[f422,f400,f332,f298,f290,f117,f569])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl2_12 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    spl2_34 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.49  fof(f332,plain,(
% 0.21/0.49    spl2_39 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.21/0.49  fof(f400,plain,(
% 0.21/0.49    spl2_45 <=> ! [X1,X2] : (k4_xboole_0(X1,X2) = k3_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X1,X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.21/0.49  fof(f422,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | (~spl2_12 | ~spl2_34 | ~spl2_35 | ~spl2_39 | ~spl2_45)),
% 0.21/0.49    inference(forward_demodulation,[],[f421,f299])).
% 0.21/0.49  fof(f421,plain,(
% 0.21/0.49    k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k3_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1)) | (~spl2_12 | ~spl2_34 | ~spl2_39 | ~spl2_45)),
% 0.21/0.49    inference(forward_demodulation,[],[f407,f337])).
% 0.21/0.49  fof(f337,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | (~spl2_12 | ~spl2_39)),
% 0.21/0.49    inference(superposition,[],[f333,f118])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) ) | ~spl2_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f117])).
% 0.21/0.49  fof(f333,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | ~spl2_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f332])).
% 0.21/0.49  fof(f407,plain,(
% 0.21/0.49    k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0) | (~spl2_34 | ~spl2_45)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f292,f401])).
% 0.21/0.49  fof(f401,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X1,X2)) ) | ~spl2_45),
% 0.21/0.49    inference(avatar_component_clause,[],[f400])).
% 0.21/0.49  fof(f292,plain,(
% 0.21/0.49    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f290])).
% 0.21/0.49  fof(f530,plain,(
% 0.21/0.49    spl2_54 | ~spl2_2 | ~spl2_3 | ~spl2_23 | ~spl2_25 | ~spl2_28),
% 0.21/0.49    inference(avatar_split_clause,[],[f233,f218,f194,f182,f76,f71,f527])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl2_2 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    spl2_23 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    spl2_25 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    spl2_28 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_23 | ~spl2_25 | ~spl2_28)),
% 0.21/0.49    inference(forward_demodulation,[],[f228,f203])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_25)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f73,f78,f195])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f194])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f76])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_23 | ~spl2_28)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f78,f220,f183])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f182])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_28),
% 0.21/0.49    inference(avatar_component_clause,[],[f218])).
% 0.21/0.49  fof(f402,plain,(
% 0.21/0.49    spl2_45 | ~spl2_8 | ~spl2_9 | ~spl2_13 | ~spl2_15 | ~spl2_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f152,f133,f129,f121,f104,f100,f400])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    spl2_13 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X1,X2)) ) | (~spl2_8 | ~spl2_9 | ~spl2_13 | ~spl2_15 | ~spl2_16)),
% 0.21/0.49    inference(forward_demodulation,[],[f150,f151])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1) | ~r1_tarski(X1,X2)) ) | (~spl2_13 | ~spl2_16)),
% 0.21/0.49    inference(superposition,[],[f134,f122])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f121])).
% 0.21/0.49  fof(f334,plain,(
% 0.21/0.49    spl2_39 | ~spl2_11 | ~spl2_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f136,f117,f113,f332])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    spl2_11 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | (~spl2_11 | ~spl2_12)),
% 0.21/0.49    inference(superposition,[],[f118,f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f113])).
% 0.21/0.49  fof(f300,plain,(
% 0.21/0.49    spl2_35 | ~spl2_4 | ~spl2_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f142,f121,f81,f298])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl2_4 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl2_4 | ~spl2_13)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f82,f122])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl2_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f81])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    spl2_34 | ~spl2_10 | ~spl2_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f288,f253,f108,f290])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl2_10 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    spl2_32 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_10 | ~spl2_32)),
% 0.21/0.49    inference(superposition,[],[f109,f255])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f253])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f108])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    spl2_6 | ~spl2_29 | ~spl2_33),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f275])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    $false | (spl2_6 | ~spl2_29 | ~spl2_33)),
% 0.21/0.49    inference(subsumption_resolution,[],[f90,f274])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_29 | ~spl2_33)),
% 0.21/0.49    inference(forward_demodulation,[],[f272,f236])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f235])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_33),
% 0.21/0.49    inference(avatar_component_clause,[],[f270])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    spl2_33 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl2_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    spl2_33 | ~spl2_2 | ~spl2_3 | ~spl2_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f212,f209,f76,f71,f270])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    spl2_27 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_27)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f73,f78,f210])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f209])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    ~spl2_2 | spl2_29 | ~spl2_5 | ~spl2_3 | ~spl2_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f185,f173,f76,f85,f235,f71])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl2_5 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    spl2_22 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_22)),
% 0.21/0.49    inference(resolution,[],[f174,f78])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) ) | ~spl2_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f173])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    ~spl2_3 | spl2_32 | ~spl2_6 | ~spl2_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f158,f154,f89,f253,f76])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    spl2_18 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_6 | ~spl2_18)),
% 0.21/0.49    inference(superposition,[],[f155,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f89])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f154])).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    ~spl2_29 | ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_5 | ~spl2_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f202,f189,f85,f76,f71,f66,f235])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl2_1 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    spl2_24 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    sK1 != k2_pre_topc(sK0,sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_5 | ~spl2_24)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f73,f68,f86,f78,f190])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f189])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ~v4_pre_topc(sK1,sK0) | spl2_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f85])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    v2_pre_topc(sK0) | ~spl2_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    spl2_28 | ~spl2_2 | ~spl2_3 | ~spl2_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f178,f165,f76,f71,f218])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    spl2_20 <=> ! [X1,X0] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3 | ~spl2_20)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f73,f78,f166])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f165])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    spl2_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f50,f209])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    spl2_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f49,f194])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    spl2_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f189])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    spl2_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f64,f182])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(flattening,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    spl2_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f51,f173])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    spl2_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f62,f165])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    spl2_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f63,f154])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    spl2_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f59,f133])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    spl2_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f58,f129])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    spl2_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f57,f125])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl2_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f60,f121])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    spl2_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f56,f117])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    spl2_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f55,f113])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl2_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f54,f108])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl2_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f53,f104])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.49    inference(rectify,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl2_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f100])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    spl2_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f47,f96])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ~spl2_5 | ~spl2_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f93,f89,f85])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ~v4_pre_topc(sK1,sK0) | ~spl2_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f45,f91])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f19])).
% 0.21/0.49  fof(f19,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl2_5 | spl2_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f44,f89,f85])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl2_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f81])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f43,f76])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f71])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f41,f66])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (11289)------------------------------
% 0.21/0.49  % (11289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11289)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (11289)Memory used [KB]: 6524
% 0.21/0.49  % (11289)Time elapsed: 0.061 s
% 0.21/0.49  % (11289)------------------------------
% 0.21/0.49  % (11289)------------------------------
% 0.21/0.49  % (11296)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (11285)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (11280)Success in time 0.136 s
%------------------------------------------------------------------------------
