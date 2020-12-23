%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:49 EST 2020

% Result     : Theorem 2.30s
% Output     : Refutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 308 expanded)
%              Number of leaves         :   37 ( 141 expanded)
%              Depth                    :    9
%              Number of atoms          :  382 ( 679 expanded)
%              Number of equality atoms :   72 ( 169 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2380,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f83,f84,f90,f97,f109,f120,f149,f162,f171,f318,f775,f829,f852,f858,f873,f883,f1131,f1184,f1319,f2370,f2371,f2379])).

fof(f2379,plain,
    ( spl3_37
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f2378,f849,f94,f80,f875])).

fof(f875,plain,
    ( spl3_37
  <=> v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f80,plain,
    ( spl3_4
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f94,plain,
    ( spl3_6
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f849,plain,
    ( spl3_33
  <=> k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f2378,plain,
    ( v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f2377,f851])).

fof(f851,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f849])).

fof(f2377,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f81,f96])).

fof(f96,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f81,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f2371,plain,
    ( ~ spl3_8
    | spl3_3
    | ~ spl3_37
    | ~ spl3_13
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f2238,f1314,f160,f875,f76,f106])).

fof(f106,plain,
    ( spl3_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f76,plain,
    ( spl3_3
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f160,plain,
    ( spl3_13
  <=> ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f1314,plain,
    ( spl3_60
  <=> k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f2238,plain,
    ( ~ v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_13
    | ~ spl3_60 ),
    inference(superposition,[],[f161,f1316])).

fof(f1316,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f1314])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f2370,plain,
    ( ~ spl3_3
    | spl3_37
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f2369,f1314,f169,f106,f875,f76])).

fof(f169,plain,
    ( spl3_14
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f2369,plain,
    ( v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_60 ),
    inference(forward_demodulation,[],[f2357,f1316])).

fof(f2357,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(resolution,[],[f170,f108])).

fof(f108,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f1319,plain,
    ( spl3_60
    | ~ spl3_36
    | ~ spl3_46
    | ~ spl3_50 ),
    inference(avatar_split_clause,[],[f1318,f1181,f1128,f870,f1314])).

fof(f870,plain,
    ( spl3_36
  <=> m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f1128,plain,
    ( spl3_46
  <=> k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f1181,plain,
    ( spl3_50
  <=> k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f1318,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl3_36
    | ~ spl3_46
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f1311,f1130])).

fof(f1130,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f1128])).

fof(f1311,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl3_36
    | ~ spl3_50 ),
    inference(superposition,[],[f888,f1183])).

fof(f1183,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f1181])).

fof(f888,plain,
    ( ! [X1] : k9_subset_1(k2_struct_0(sK0),X1,k5_xboole_0(k2_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X1,k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl3_36 ),
    inference(resolution,[],[f872,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f45,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f872,plain,
    ( m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f870])).

fof(f1184,plain,
    ( spl3_50
    | ~ spl3_21
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f1179,f849,f315,f1181])).

fof(f315,plain,
    ( spl3_21
  <=> k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f1179,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl3_21
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f317,f851])).

fof(f317,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f315])).

fof(f1131,plain,
    ( spl3_46
    | ~ spl3_32
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f1126,f855,f772,f1128])).

fof(f772,plain,
    ( spl3_32
  <=> sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f855,plain,
    ( spl3_34
  <=> sK1 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f1126,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl3_32
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f1125,f774])).

fof(f774,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f772])).

fof(f1125,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f1124,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1124,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl3_34 ),
    inference(superposition,[],[f53,f857])).

fof(f857,plain,
    ( sK1 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f855])).

fof(f53,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f40,f38,f52,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f883,plain,
    ( ~ spl3_37
    | spl3_4
    | ~ spl3_6
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f882,f849,f94,f80,f875])).

fof(f882,plain,
    ( ~ v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | spl3_4
    | ~ spl3_6
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f881,f851])).

fof(f881,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f82,f96])).

fof(f82,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f873,plain,
    ( spl3_36
    | ~ spl3_9
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f862,f849,f117,f870])).

fof(f117,plain,
    ( spl3_9
  <=> m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f862,plain,
    ( m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_9
    | ~ spl3_33 ),
    inference(backward_demodulation,[],[f119,f851])).

fof(f119,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f858,plain,
    ( spl3_34
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f834,f772,f855])).

fof(f834,plain,
    ( sK1 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))))
    | ~ spl3_32 ),
    inference(superposition,[],[f155,f774])).

fof(f155,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X1,X0)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))))) ),
    inference(superposition,[],[f53,f37])).

fof(f852,plain,
    ( spl3_33
    | ~ spl3_11
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f830,f772,f146,f849])).

fof(f146,plain,
    ( spl3_11
  <=> k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f830,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl3_11
    | ~ spl3_32 ),
    inference(backward_demodulation,[],[f148,f774])).

fof(f148,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f829,plain,
    ( spl3_32
    | spl3_31 ),
    inference(avatar_split_clause,[],[f828,f768,f772])).

fof(f768,plain,
    ( spl3_31
  <=> r2_hidden(sK2(k2_struct_0(sK0),sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f828,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))
    | spl3_31 ),
    inference(forward_demodulation,[],[f824,f37])).

fof(f824,plain,
    ( sK1 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))
    | spl3_31 ),
    inference(resolution,[],[f770,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X1),X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X1 ) ),
    inference(factoring,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f48,f38])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f770,plain,
    ( ~ r2_hidden(sK2(k2_struct_0(sK0),sK1,sK1),sK1)
    | spl3_31 ),
    inference(avatar_component_clause,[],[f768])).

fof(f775,plain,
    ( ~ spl3_31
    | spl3_32
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f766,f106,f772,f768])).

fof(f766,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))
    | ~ r2_hidden(sK2(k2_struct_0(sK0),sK1,sK1),sK1)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f765,f37])).

fof(f765,plain,
    ( sK1 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))
    | ~ r2_hidden(sK2(k2_struct_0(sK0),sK1,sK1),sK1)
    | ~ spl3_8 ),
    inference(duplicate_literal_removal,[],[f757])).

fof(f757,plain,
    ( sK1 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))
    | ~ r2_hidden(sK2(k2_struct_0(sK0),sK1,sK1),sK1)
    | ~ r2_hidden(sK2(k2_struct_0(sK0),sK1,sK1),sK1)
    | sK1 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))
    | ~ spl3_8 ),
    inference(resolution,[],[f227,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f46,f38])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f227,plain,
    ( ! [X14] :
        ( r2_hidden(sK2(X14,sK1,sK1),k2_struct_0(sK0))
        | sK1 = k1_setfam_1(k2_tarski(X14,sK1)) )
    | ~ spl3_8 ),
    inference(resolution,[],[f186,f123])).

fof(f123,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | r2_hidden(X2,k2_struct_0(sK0)) )
    | ~ spl3_8 ),
    inference(resolution,[],[f43,f108])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f318,plain,
    ( spl3_21
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f302,f106,f315])).

fof(f302,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl3_8 ),
    inference(resolution,[],[f228,f108])).

fof(f228,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k7_subset_1(X1,X1,X0) = k9_subset_1(X1,X1,k3_subset_1(X1,X0)) ) ),
    inference(resolution,[],[f44,f91])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f32,f31])).

fof(f31,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f171,plain,
    ( ~ spl3_1
    | spl3_14
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f167,f94,f169,f66])).

fof(f66,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl3_6 ),
    inference(superposition,[],[f36,f96])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f162,plain,
    ( ~ spl3_1
    | spl3_13
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f158,f94,f160,f66])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v4_pre_topc(X0,sK0) )
    | ~ spl3_6 ),
    inference(superposition,[],[f35,f96])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f149,plain,
    ( spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f144,f106,f146])).

fof(f144,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f140,f37])).

fof(f140,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1)))
    | ~ spl3_8 ),
    inference(resolution,[],[f54,f108])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f120,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f115,f106,f117])).

fof(f115,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(resolution,[],[f41,f108])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f109,plain,
    ( spl3_8
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f99,f94,f71,f106])).

fof(f71,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f99,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f73,f96])).

fof(f73,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f97,plain,
    ( spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f92,f87,f94])).

fof(f87,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f92,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f33,f89])).

fof(f89,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f90,plain,
    ( spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f85,f66,f87])).

fof(f85,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f34,f68])).

fof(f68,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f84,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f27,f80,f76])).

fof(f27,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f83,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f28,f80,f76])).

fof(f28,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f30,f66])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:54:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (3588)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.49  % (3585)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.49  % (3589)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (3596)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (3602)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (3595)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (3614)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.48/0.56  % (3598)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.48/0.57  % (3597)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.57  % (3615)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.48/0.57  % (3607)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.68/0.58  % (3593)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.68/0.58  % (3607)Refutation not found, incomplete strategy% (3607)------------------------------
% 1.68/0.58  % (3607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (3607)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.58  
% 1.68/0.58  % (3607)Memory used [KB]: 1791
% 1.68/0.58  % (3607)Time elapsed: 0.100 s
% 1.68/0.58  % (3607)------------------------------
% 1.68/0.58  % (3607)------------------------------
% 1.68/0.58  % (3591)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.68/0.58  % (3587)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.68/0.58  % (3590)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.68/0.58  % (3609)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.68/0.59  % (3600)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.68/0.59  % (3605)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.68/0.59  % (3586)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.68/0.60  % (3613)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.68/0.60  % (3604)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.68/0.60  % (3606)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.68/0.60  % (3611)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.68/0.60  % (3599)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.68/0.60  % (3606)Refutation not found, incomplete strategy% (3606)------------------------------
% 1.68/0.60  % (3606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.60  % (3606)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.60  
% 1.68/0.60  % (3606)Memory used [KB]: 10746
% 1.68/0.60  % (3606)Time elapsed: 0.188 s
% 1.68/0.60  % (3606)------------------------------
% 1.68/0.60  % (3606)------------------------------
% 1.68/0.60  % (3608)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.68/0.61  % (3608)Refutation not found, incomplete strategy% (3608)------------------------------
% 1.68/0.61  % (3608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.61  % (3608)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.61  
% 1.68/0.61  % (3608)Memory used [KB]: 10746
% 1.68/0.61  % (3608)Time elapsed: 0.197 s
% 1.68/0.61  % (3608)------------------------------
% 1.68/0.61  % (3608)------------------------------
% 1.68/0.61  % (3610)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.68/0.61  % (3603)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.68/0.61  % (3603)Refutation not found, incomplete strategy% (3603)------------------------------
% 1.68/0.61  % (3603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.61  % (3603)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.61  
% 1.68/0.61  % (3603)Memory used [KB]: 10618
% 1.68/0.61  % (3603)Time elapsed: 0.211 s
% 1.68/0.61  % (3603)------------------------------
% 1.68/0.61  % (3603)------------------------------
% 1.68/0.61  % (3594)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.68/0.61  % (3612)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.68/0.62  % (3592)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 2.30/0.67  % (3602)Refutation found. Thanks to Tanya!
% 2.30/0.67  % SZS status Theorem for theBenchmark
% 2.30/0.67  % SZS output start Proof for theBenchmark
% 2.30/0.67  fof(f2380,plain,(
% 2.30/0.67    $false),
% 2.30/0.67    inference(avatar_sat_refutation,[],[f69,f74,f83,f84,f90,f97,f109,f120,f149,f162,f171,f318,f775,f829,f852,f858,f873,f883,f1131,f1184,f1319,f2370,f2371,f2379])).
% 2.30/0.67  fof(f2379,plain,(
% 2.30/0.67    spl3_37 | ~spl3_4 | ~spl3_6 | ~spl3_33),
% 2.30/0.67    inference(avatar_split_clause,[],[f2378,f849,f94,f80,f875])).
% 2.30/0.68  fof(f875,plain,(
% 2.30/0.68    spl3_37 <=> v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 2.30/0.68  fof(f80,plain,(
% 2.30/0.68    spl3_4 <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.30/0.68  fof(f94,plain,(
% 2.30/0.68    spl3_6 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.30/0.68  fof(f849,plain,(
% 2.30/0.68    spl3_33 <=> k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 2.30/0.68  fof(f2378,plain,(
% 2.30/0.68    v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | (~spl3_4 | ~spl3_6 | ~spl3_33)),
% 2.30/0.68    inference(forward_demodulation,[],[f2377,f851])).
% 2.30/0.68  fof(f851,plain,(
% 2.30/0.68    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) | ~spl3_33),
% 2.30/0.68    inference(avatar_component_clause,[],[f849])).
% 2.30/0.68  fof(f2377,plain,(
% 2.30/0.68    v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | (~spl3_4 | ~spl3_6)),
% 2.30/0.68    inference(forward_demodulation,[],[f81,f96])).
% 2.30/0.68  fof(f96,plain,(
% 2.30/0.68    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_6),
% 2.30/0.68    inference(avatar_component_clause,[],[f94])).
% 2.30/0.68  fof(f81,plain,(
% 2.30/0.68    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl3_4),
% 2.30/0.68    inference(avatar_component_clause,[],[f80])).
% 2.30/0.68  fof(f2371,plain,(
% 2.30/0.68    ~spl3_8 | spl3_3 | ~spl3_37 | ~spl3_13 | ~spl3_60),
% 2.30/0.68    inference(avatar_split_clause,[],[f2238,f1314,f160,f875,f76,f106])).
% 2.30/0.68  fof(f106,plain,(
% 2.30/0.68    spl3_8 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.30/0.68  fof(f76,plain,(
% 2.30/0.68    spl3_3 <=> v4_pre_topc(sK1,sK0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.30/0.68  fof(f160,plain,(
% 2.30/0.68    spl3_13 <=> ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.30/0.68  fof(f1314,plain,(
% 2.30/0.68    spl3_60 <=> k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 2.30/0.68  fof(f2238,plain,(
% 2.30/0.68    ~v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_13 | ~spl3_60)),
% 2.30/0.68    inference(superposition,[],[f161,f1316])).
% 2.30/0.68  fof(f1316,plain,(
% 2.30/0.68    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) | ~spl3_60),
% 2.30/0.68    inference(avatar_component_clause,[],[f1314])).
% 2.30/0.68  fof(f161,plain,(
% 2.30/0.68    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_13),
% 2.30/0.68    inference(avatar_component_clause,[],[f160])).
% 2.30/0.68  fof(f2370,plain,(
% 2.30/0.68    ~spl3_3 | spl3_37 | ~spl3_8 | ~spl3_14 | ~spl3_60),
% 2.30/0.68    inference(avatar_split_clause,[],[f2369,f1314,f169,f106,f875,f76])).
% 2.30/0.68  fof(f169,plain,(
% 2.30/0.68    spl3_14 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0))),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.30/0.68  fof(f2369,plain,(
% 2.30/0.68    v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0) | (~spl3_8 | ~spl3_14 | ~spl3_60)),
% 2.30/0.68    inference(forward_demodulation,[],[f2357,f1316])).
% 2.30/0.68  fof(f2357,plain,(
% 2.30/0.68    ~v4_pre_topc(sK1,sK0) | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | (~spl3_8 | ~spl3_14)),
% 2.30/0.68    inference(resolution,[],[f170,f108])).
% 2.30/0.68  fof(f108,plain,(
% 2.30/0.68    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_8),
% 2.30/0.68    inference(avatar_component_clause,[],[f106])).
% 2.30/0.68  fof(f170,plain,(
% 2.30/0.68    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)) ) | ~spl3_14),
% 2.30/0.68    inference(avatar_component_clause,[],[f169])).
% 2.30/0.68  fof(f1319,plain,(
% 2.30/0.68    spl3_60 | ~spl3_36 | ~spl3_46 | ~spl3_50),
% 2.30/0.68    inference(avatar_split_clause,[],[f1318,f1181,f1128,f870,f1314])).
% 2.30/0.68  fof(f870,plain,(
% 2.30/0.68    spl3_36 <=> m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 2.30/0.68  fof(f1128,plain,(
% 2.30/0.68    spl3_46 <=> k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 2.30/0.68  fof(f1181,plain,(
% 2.30/0.68    spl3_50 <=> k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 2.30/0.68  fof(f1318,plain,(
% 2.30/0.68    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) | (~spl3_36 | ~spl3_46 | ~spl3_50)),
% 2.30/0.68    inference(forward_demodulation,[],[f1311,f1130])).
% 2.30/0.68  fof(f1130,plain,(
% 2.30/0.68    k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) | ~spl3_46),
% 2.30/0.68    inference(avatar_component_clause,[],[f1128])).
% 2.30/0.68  fof(f1311,plain,(
% 2.30/0.68    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) | (~spl3_36 | ~spl3_50)),
% 2.30/0.68    inference(superposition,[],[f888,f1183])).
% 2.30/0.68  fof(f1183,plain,(
% 2.30/0.68    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)) | ~spl3_50),
% 2.30/0.68    inference(avatar_component_clause,[],[f1181])).
% 2.30/0.68  fof(f888,plain,(
% 2.30/0.68    ( ! [X1] : (k9_subset_1(k2_struct_0(sK0),X1,k5_xboole_0(k2_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X1,k5_xboole_0(k2_struct_0(sK0),sK1)))) ) | ~spl3_36),
% 2.30/0.68    inference(resolution,[],[f872,f55])).
% 2.30/0.68  fof(f55,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 2.30/0.68    inference(definition_unfolding,[],[f45,f38])).
% 2.30/0.68  fof(f38,plain,(
% 2.30/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.30/0.68    inference(cnf_transformation,[],[f12])).
% 2.30/0.68  fof(f12,axiom,(
% 2.30/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.30/0.68  fof(f45,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f26])).
% 2.30/0.68  fof(f26,plain,(
% 2.30/0.68    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.30/0.68    inference(ennf_transformation,[],[f10])).
% 2.30/0.68  fof(f10,axiom,(
% 2.30/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.30/0.68  fof(f872,plain,(
% 2.30/0.68    m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_36),
% 2.30/0.68    inference(avatar_component_clause,[],[f870])).
% 2.30/0.68  fof(f1184,plain,(
% 2.30/0.68    spl3_50 | ~spl3_21 | ~spl3_33),
% 2.30/0.68    inference(avatar_split_clause,[],[f1179,f849,f315,f1181])).
% 2.30/0.68  fof(f315,plain,(
% 2.30/0.68    spl3_21 <=> k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 2.30/0.68  fof(f1179,plain,(
% 2.30/0.68    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)) | (~spl3_21 | ~spl3_33)),
% 2.30/0.68    inference(forward_demodulation,[],[f317,f851])).
% 2.30/0.68  fof(f317,plain,(
% 2.30/0.68    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) | ~spl3_21),
% 2.30/0.68    inference(avatar_component_clause,[],[f315])).
% 2.30/0.68  fof(f1131,plain,(
% 2.30/0.68    spl3_46 | ~spl3_32 | ~spl3_34),
% 2.30/0.68    inference(avatar_split_clause,[],[f1126,f855,f772,f1128])).
% 2.30/0.68  fof(f772,plain,(
% 2.30/0.68    spl3_32 <=> sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 2.30/0.68  fof(f855,plain,(
% 2.30/0.68    spl3_34 <=> sK1 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))))),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 2.30/0.68  fof(f1126,plain,(
% 2.30/0.68    k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) | (~spl3_32 | ~spl3_34)),
% 2.30/0.68    inference(forward_demodulation,[],[f1125,f774])).
% 2.30/0.68  fof(f774,plain,(
% 2.30/0.68    sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) | ~spl3_32),
% 2.30/0.68    inference(avatar_component_clause,[],[f772])).
% 2.30/0.68  fof(f1125,plain,(
% 2.30/0.68    k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) | ~spl3_34),
% 2.30/0.68    inference(forward_demodulation,[],[f1124,f37])).
% 2.30/0.68  fof(f37,plain,(
% 2.30/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f4])).
% 2.30/0.68  fof(f4,axiom,(
% 2.30/0.68    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.30/0.68  fof(f1124,plain,(
% 2.30/0.68    k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) | ~spl3_34),
% 2.30/0.68    inference(superposition,[],[f53,f857])).
% 2.30/0.68  fof(f857,plain,(
% 2.30/0.68    sK1 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))) | ~spl3_34),
% 2.30/0.68    inference(avatar_component_clause,[],[f855])).
% 2.30/0.68  fof(f53,plain,(
% 2.30/0.68    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 2.30/0.68    inference(definition_unfolding,[],[f40,f38,f52,f52])).
% 2.30/0.68  fof(f52,plain,(
% 2.30/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.30/0.68    inference(definition_unfolding,[],[f39,f38])).
% 2.30/0.68  fof(f39,plain,(
% 2.30/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.30/0.68    inference(cnf_transformation,[],[f2])).
% 2.30/0.68  fof(f2,axiom,(
% 2.30/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.30/0.68  fof(f40,plain,(
% 2.30/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.30/0.68    inference(cnf_transformation,[],[f3])).
% 2.30/0.68  fof(f3,axiom,(
% 2.30/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.30/0.68  fof(f883,plain,(
% 2.30/0.68    ~spl3_37 | spl3_4 | ~spl3_6 | ~spl3_33),
% 2.30/0.68    inference(avatar_split_clause,[],[f882,f849,f94,f80,f875])).
% 2.30/0.68  fof(f882,plain,(
% 2.30/0.68    ~v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | (spl3_4 | ~spl3_6 | ~spl3_33)),
% 2.30/0.68    inference(forward_demodulation,[],[f881,f851])).
% 2.30/0.68  fof(f881,plain,(
% 2.30/0.68    ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | (spl3_4 | ~spl3_6)),
% 2.30/0.68    inference(forward_demodulation,[],[f82,f96])).
% 2.30/0.68  fof(f82,plain,(
% 2.30/0.68    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl3_4),
% 2.30/0.68    inference(avatar_component_clause,[],[f80])).
% 2.30/0.68  fof(f873,plain,(
% 2.30/0.68    spl3_36 | ~spl3_9 | ~spl3_33),
% 2.30/0.68    inference(avatar_split_clause,[],[f862,f849,f117,f870])).
% 2.30/0.68  fof(f117,plain,(
% 2.30/0.68    spl3_9 <=> m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.30/0.68  fof(f862,plain,(
% 2.30/0.68    m1_subset_1(k5_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_9 | ~spl3_33)),
% 2.30/0.68    inference(backward_demodulation,[],[f119,f851])).
% 2.30/0.68  fof(f119,plain,(
% 2.30/0.68    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_9),
% 2.30/0.68    inference(avatar_component_clause,[],[f117])).
% 2.30/0.68  fof(f858,plain,(
% 2.30/0.68    spl3_34 | ~spl3_32),
% 2.30/0.68    inference(avatar_split_clause,[],[f834,f772,f855])).
% 2.30/0.68  fof(f834,plain,(
% 2.30/0.68    sK1 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))) | ~spl3_32),
% 2.30/0.68    inference(superposition,[],[f155,f774])).
% 2.30/0.68  fof(f155,plain,(
% 2.30/0.68    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X1,X0)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))))))) )),
% 2.30/0.68    inference(superposition,[],[f53,f37])).
% 2.30/0.68  fof(f852,plain,(
% 2.30/0.68    spl3_33 | ~spl3_11 | ~spl3_32),
% 2.30/0.68    inference(avatar_split_clause,[],[f830,f772,f146,f849])).
% 2.30/0.68  fof(f146,plain,(
% 2.30/0.68    spl3_11 <=> k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))))),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.30/0.68  fof(f830,plain,(
% 2.30/0.68    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) | (~spl3_11 | ~spl3_32)),
% 2.30/0.68    inference(backward_demodulation,[],[f148,f774])).
% 2.30/0.68  fof(f148,plain,(
% 2.30/0.68    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))) | ~spl3_11),
% 2.30/0.68    inference(avatar_component_clause,[],[f146])).
% 2.30/0.68  fof(f829,plain,(
% 2.30/0.68    spl3_32 | spl3_31),
% 2.30/0.68    inference(avatar_split_clause,[],[f828,f768,f772])).
% 2.30/0.68  fof(f768,plain,(
% 2.30/0.68    spl3_31 <=> r2_hidden(sK2(k2_struct_0(sK0),sK1,sK1),sK1)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 2.30/0.68  fof(f828,plain,(
% 2.30/0.68    sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) | spl3_31),
% 2.30/0.68    inference(forward_demodulation,[],[f824,f37])).
% 2.30/0.68  fof(f824,plain,(
% 2.30/0.68    sK1 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1)) | spl3_31),
% 2.30/0.68    inference(resolution,[],[f770,f186])).
% 2.30/0.68  fof(f186,plain,(
% 2.30/0.68    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X1),X1) | k1_setfam_1(k2_tarski(X0,X1)) = X1) )),
% 2.30/0.68    inference(factoring,[],[f59])).
% 2.30/0.68  fof(f59,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 2.30/0.68    inference(definition_unfolding,[],[f48,f38])).
% 2.30/0.68  fof(f48,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.30/0.68    inference(cnf_transformation,[],[f1])).
% 2.30/0.68  fof(f1,axiom,(
% 2.30/0.68    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.30/0.68  fof(f770,plain,(
% 2.30/0.68    ~r2_hidden(sK2(k2_struct_0(sK0),sK1,sK1),sK1) | spl3_31),
% 2.30/0.68    inference(avatar_component_clause,[],[f768])).
% 2.30/0.68  fof(f775,plain,(
% 2.30/0.68    ~spl3_31 | spl3_32 | ~spl3_8),
% 2.30/0.68    inference(avatar_split_clause,[],[f766,f106,f772,f768])).
% 2.30/0.68  fof(f766,plain,(
% 2.30/0.68    sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) | ~r2_hidden(sK2(k2_struct_0(sK0),sK1,sK1),sK1) | ~spl3_8),
% 2.30/0.68    inference(forward_demodulation,[],[f765,f37])).
% 2.30/0.68  fof(f765,plain,(
% 2.30/0.68    sK1 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1)) | ~r2_hidden(sK2(k2_struct_0(sK0),sK1,sK1),sK1) | ~spl3_8),
% 2.30/0.68    inference(duplicate_literal_removal,[],[f757])).
% 2.30/0.68  fof(f757,plain,(
% 2.30/0.68    sK1 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1)) | ~r2_hidden(sK2(k2_struct_0(sK0),sK1,sK1),sK1) | ~r2_hidden(sK2(k2_struct_0(sK0),sK1,sK1),sK1) | sK1 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1)) | ~spl3_8),
% 2.30/0.68    inference(resolution,[],[f227,f61])).
% 2.30/0.68  fof(f61,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 2.30/0.68    inference(definition_unfolding,[],[f46,f38])).
% 2.30/0.68  fof(f46,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.30/0.68    inference(cnf_transformation,[],[f1])).
% 2.30/0.68  fof(f227,plain,(
% 2.30/0.68    ( ! [X14] : (r2_hidden(sK2(X14,sK1,sK1),k2_struct_0(sK0)) | sK1 = k1_setfam_1(k2_tarski(X14,sK1))) ) | ~spl3_8),
% 2.30/0.68    inference(resolution,[],[f186,f123])).
% 2.30/0.68  fof(f123,plain,(
% 2.30/0.68    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(X2,k2_struct_0(sK0))) ) | ~spl3_8),
% 2.30/0.68    inference(resolution,[],[f43,f108])).
% 2.30/0.68  fof(f43,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f24])).
% 2.30/0.68  fof(f24,plain,(
% 2.30/0.68    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.30/0.68    inference(ennf_transformation,[],[f9])).
% 2.30/0.68  fof(f9,axiom,(
% 2.30/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 2.30/0.68  fof(f318,plain,(
% 2.30/0.68    spl3_21 | ~spl3_8),
% 2.30/0.68    inference(avatar_split_clause,[],[f302,f106,f315])).
% 2.30/0.68  fof(f302,plain,(
% 2.30/0.68    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) | ~spl3_8),
% 2.30/0.68    inference(resolution,[],[f228,f108])).
% 2.30/0.68  fof(f228,plain,(
% 2.30/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k7_subset_1(X1,X1,X0) = k9_subset_1(X1,X1,k3_subset_1(X1,X0))) )),
% 2.30/0.68    inference(resolution,[],[f44,f91])).
% 2.30/0.68  fof(f91,plain,(
% 2.30/0.68    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.30/0.68    inference(forward_demodulation,[],[f32,f31])).
% 2.30/0.68  fof(f31,plain,(
% 2.30/0.68    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.30/0.68    inference(cnf_transformation,[],[f5])).
% 2.30/0.68  fof(f5,axiom,(
% 2.30/0.68    ! [X0] : k2_subset_1(X0) = X0),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 2.30/0.68  fof(f32,plain,(
% 2.30/0.68    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.30/0.68    inference(cnf_transformation,[],[f7])).
% 2.30/0.68  fof(f7,axiom,(
% 2.30/0.68    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.30/0.68  fof(f44,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))) )),
% 2.30/0.68    inference(cnf_transformation,[],[f25])).
% 2.30/0.68  fof(f25,plain,(
% 2.30/0.68    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.30/0.68    inference(ennf_transformation,[],[f11])).
% 2.30/0.68  fof(f11,axiom,(
% 2.30/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 2.30/0.68  fof(f171,plain,(
% 2.30/0.68    ~spl3_1 | spl3_14 | ~spl3_6),
% 2.30/0.68    inference(avatar_split_clause,[],[f167,f94,f169,f66])).
% 2.30/0.68  fof(f66,plain,(
% 2.30/0.68    spl3_1 <=> l1_pre_topc(sK0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.30/0.68  fof(f167,plain,(
% 2.30/0.68    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~v4_pre_topc(X0,sK0)) ) | ~spl3_6),
% 2.30/0.68    inference(superposition,[],[f36,f96])).
% 2.30/0.68  fof(f36,plain,(
% 2.30/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f21])).
% 2.30/0.68  fof(f21,plain,(
% 2.30/0.68    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.30/0.68    inference(ennf_transformation,[],[f14])).
% 2.30/0.68  fof(f14,axiom,(
% 2.30/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).
% 2.30/0.68  fof(f162,plain,(
% 2.30/0.68    ~spl3_1 | spl3_13 | ~spl3_6),
% 2.30/0.68    inference(avatar_split_clause,[],[f158,f94,f160,f66])).
% 2.30/0.68  fof(f158,plain,(
% 2.30/0.68    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v4_pre_topc(X0,sK0)) ) | ~spl3_6),
% 2.30/0.68    inference(superposition,[],[f35,f96])).
% 2.30/0.68  fof(f35,plain,(
% 2.30/0.68    ( ! [X0,X1] : (~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f21])).
% 2.30/0.68  fof(f149,plain,(
% 2.30/0.68    spl3_11 | ~spl3_8),
% 2.30/0.68    inference(avatar_split_clause,[],[f144,f106,f146])).
% 2.30/0.68  fof(f144,plain,(
% 2.30/0.68    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))) | ~spl3_8),
% 2.30/0.68    inference(forward_demodulation,[],[f140,f37])).
% 2.30/0.68  fof(f140,plain,(
% 2.30/0.68    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))) | ~spl3_8),
% 2.30/0.68    inference(resolution,[],[f54,f108])).
% 2.30/0.68  fof(f54,plain,(
% 2.30/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.30/0.68    inference(definition_unfolding,[],[f42,f52])).
% 2.30/0.68  fof(f42,plain,(
% 2.30/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f23])).
% 2.30/0.68  fof(f23,plain,(
% 2.30/0.68    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.30/0.68    inference(ennf_transformation,[],[f6])).
% 2.30/0.68  fof(f6,axiom,(
% 2.30/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.30/0.68  fof(f120,plain,(
% 2.30/0.68    spl3_9 | ~spl3_8),
% 2.30/0.68    inference(avatar_split_clause,[],[f115,f106,f117])).
% 2.30/0.68  fof(f115,plain,(
% 2.30/0.68    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_8),
% 2.30/0.68    inference(resolution,[],[f41,f108])).
% 2.30/0.68  fof(f41,plain,(
% 2.30/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.30/0.68    inference(cnf_transformation,[],[f22])).
% 2.30/0.68  fof(f22,plain,(
% 2.30/0.68    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.30/0.68    inference(ennf_transformation,[],[f8])).
% 2.30/0.68  fof(f8,axiom,(
% 2.30/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.30/0.68  fof(f109,plain,(
% 2.30/0.68    spl3_8 | ~spl3_2 | ~spl3_6),
% 2.30/0.68    inference(avatar_split_clause,[],[f99,f94,f71,f106])).
% 2.30/0.68  fof(f71,plain,(
% 2.30/0.68    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.30/0.68  fof(f99,plain,(
% 2.30/0.68    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_2 | ~spl3_6)),
% 2.30/0.68    inference(backward_demodulation,[],[f73,f96])).
% 2.30/0.68  fof(f73,plain,(
% 2.30/0.68    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 2.30/0.68    inference(avatar_component_clause,[],[f71])).
% 2.30/0.68  fof(f97,plain,(
% 2.30/0.68    spl3_6 | ~spl3_5),
% 2.30/0.68    inference(avatar_split_clause,[],[f92,f87,f94])).
% 2.30/0.68  fof(f87,plain,(
% 2.30/0.68    spl3_5 <=> l1_struct_0(sK0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.30/0.68  fof(f92,plain,(
% 2.30/0.68    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 2.30/0.68    inference(resolution,[],[f33,f89])).
% 2.30/0.68  fof(f89,plain,(
% 2.30/0.68    l1_struct_0(sK0) | ~spl3_5),
% 2.30/0.68    inference(avatar_component_clause,[],[f87])).
% 2.30/0.68  fof(f33,plain,(
% 2.30/0.68    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f19])).
% 2.30/0.68  fof(f19,plain,(
% 2.30/0.68    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.30/0.68    inference(ennf_transformation,[],[f13])).
% 2.30/0.68  fof(f13,axiom,(
% 2.30/0.68    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 2.30/0.68  fof(f90,plain,(
% 2.30/0.68    spl3_5 | ~spl3_1),
% 2.30/0.68    inference(avatar_split_clause,[],[f85,f66,f87])).
% 2.30/0.68  fof(f85,plain,(
% 2.30/0.68    l1_struct_0(sK0) | ~spl3_1),
% 2.30/0.68    inference(resolution,[],[f34,f68])).
% 2.30/0.68  fof(f68,plain,(
% 2.30/0.68    l1_pre_topc(sK0) | ~spl3_1),
% 2.30/0.68    inference(avatar_component_clause,[],[f66])).
% 2.30/0.68  fof(f34,plain,(
% 2.30/0.68    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f20])).
% 2.30/0.68  fof(f20,plain,(
% 2.30/0.68    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.30/0.68    inference(ennf_transformation,[],[f15])).
% 2.30/0.68  fof(f15,axiom,(
% 2.30/0.68    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.30/0.68  fof(f84,plain,(
% 2.30/0.68    spl3_3 | spl3_4),
% 2.30/0.68    inference(avatar_split_clause,[],[f27,f80,f76])).
% 2.30/0.68  fof(f27,plain,(
% 2.30/0.68    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 2.30/0.68    inference(cnf_transformation,[],[f18])).
% 2.30/0.68  fof(f18,plain,(
% 2.30/0.68    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.30/0.68    inference(ennf_transformation,[],[f17])).
% 2.30/0.68  fof(f17,negated_conjecture,(
% 2.30/0.68    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.30/0.68    inference(negated_conjecture,[],[f16])).
% 2.30/0.69  fof(f16,conjecture,(
% 2.30/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.30/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 2.30/0.69  fof(f83,plain,(
% 2.30/0.69    ~spl3_3 | ~spl3_4),
% 2.30/0.69    inference(avatar_split_clause,[],[f28,f80,f76])).
% 2.30/0.69  fof(f28,plain,(
% 2.30/0.69    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 2.30/0.69    inference(cnf_transformation,[],[f18])).
% 2.30/0.69  fof(f74,plain,(
% 2.30/0.69    spl3_2),
% 2.30/0.69    inference(avatar_split_clause,[],[f29,f71])).
% 2.30/0.69  fof(f29,plain,(
% 2.30/0.69    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.30/0.69    inference(cnf_transformation,[],[f18])).
% 2.30/0.69  fof(f69,plain,(
% 2.30/0.69    spl3_1),
% 2.30/0.69    inference(avatar_split_clause,[],[f30,f66])).
% 2.30/0.69  fof(f30,plain,(
% 2.30/0.69    l1_pre_topc(sK0)),
% 2.30/0.69    inference(cnf_transformation,[],[f18])).
% 2.30/0.69  % SZS output end Proof for theBenchmark
% 2.30/0.69  % (3602)------------------------------
% 2.30/0.69  % (3602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.69  % (3602)Termination reason: Refutation
% 2.30/0.69  
% 2.30/0.69  % (3602)Memory used [KB]: 12665
% 2.30/0.69  % (3602)Time elapsed: 0.238 s
% 2.30/0.69  % (3602)------------------------------
% 2.30/0.69  % (3602)------------------------------
% 2.30/0.69  % (3583)Success in time 0.328 s
%------------------------------------------------------------------------------
