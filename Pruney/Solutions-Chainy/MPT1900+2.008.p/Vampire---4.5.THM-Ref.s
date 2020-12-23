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
% DateTime   : Thu Dec  3 13:22:25 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  238 ( 572 expanded)
%              Number of leaves         :   46 ( 211 expanded)
%              Depth                    :   21
%              Number of atoms          :  925 (1897 expanded)
%              Number of equality atoms :   60 ( 186 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f855,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f137,f142,f147,f152,f157,f182,f187,f201,f223,f231,f243,f248,f265,f268,f275,f299,f304,f309,f444,f459,f469,f524,f641,f787,f812,f837,f846,f854])).

fof(f854,plain,(
    spl10_61 ),
    inference(avatar_contradiction_clause,[],[f853])).

fof(f853,plain,
    ( $false
    | spl10_61 ),
    inference(subsumption_resolution,[],[f852,f71])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f852,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))))
    | spl10_61 ),
    inference(resolution,[],[f845,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f845,plain,
    ( ~ r1_tarski(k1_xboole_0,k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | spl10_61 ),
    inference(avatar_component_clause,[],[f843])).

fof(f843,plain,
    ( spl10_61
  <=> r1_tarski(k1_xboole_0,k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f846,plain,
    ( ~ spl10_61
    | ~ spl10_45
    | spl10_60 ),
    inference(avatar_split_clause,[],[f841,f834,f638,f843])).

fof(f638,plain,
    ( spl10_45
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f834,plain,
    ( spl10_60
  <=> r1_tarski(k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).

fof(f841,plain,
    ( ~ r1_tarski(k1_xboole_0,k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ spl10_45
    | spl10_60 ),
    inference(forward_demodulation,[],[f840,f640])).

fof(f640,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f638])).

fof(f840,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | spl10_60 ),
    inference(subsumption_resolution,[],[f839,f71])).

fof(f839,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | spl10_60 ),
    inference(superposition,[],[f836,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f836,plain,
    ( ~ r1_tarski(k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | spl10_60 ),
    inference(avatar_component_clause,[],[f834])).

fof(f837,plain,
    ( ~ spl10_60
    | spl10_58 ),
    inference(avatar_split_clause,[],[f820,f809,f834])).

fof(f809,plain,
    ( spl10_58
  <=> r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f820,plain,
    ( ~ r1_tarski(k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | spl10_58 ),
    inference(subsumption_resolution,[],[f819,f71])).

fof(f819,plain,
    ( ~ r1_tarski(k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | spl10_58 ),
    inference(superposition,[],[f811,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f811,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | spl10_58 ),
    inference(avatar_component_clause,[],[f809])).

fof(f812,plain,
    ( ~ spl10_58
    | ~ spl10_18
    | spl10_36
    | ~ spl10_39 ),
    inference(avatar_split_clause,[],[f793,f545,f521,f272,f809])).

fof(f272,plain,
    ( spl10_18
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f521,plain,
    ( spl10_36
  <=> r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK7(sK0,sK1,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK7(sK0,sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f545,plain,
    ( spl10_39
  <=> r1_tarski(sK7(sK0,sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f793,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ spl10_18
    | spl10_36
    | ~ spl10_39 ),
    inference(backward_demodulation,[],[f523,f790])).

fof(f790,plain,
    ( k1_xboole_0 = sK7(sK0,sK1,k1_xboole_0)
    | ~ spl10_18
    | ~ spl10_39 ),
    inference(resolution,[],[f546,f400])).

fof(f400,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl10_18 ),
    inference(resolution,[],[f342,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f342,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X3 )
    | ~ spl10_18 ),
    inference(resolution,[],[f294,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f294,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl10_18 ),
    inference(forward_demodulation,[],[f288,f126])).

fof(f126,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f288,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | v1_xboole_0(X0) )
    | ~ spl10_18 ),
    inference(backward_demodulation,[],[f276,f277])).

fof(f277,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl10_18 ),
    inference(resolution,[],[f274,f87])).

fof(f274,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f272])).

fof(f276,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
        | v1_xboole_0(X0) )
    | ~ spl10_18 ),
    inference(resolution,[],[f274,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f546,plain,
    ( r1_tarski(sK7(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f545])).

fof(f523,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK7(sK0,sK1,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK7(sK0,sK1,k1_xboole_0))))
    | spl10_36 ),
    inference(avatar_component_clause,[],[f521])).

fof(f787,plain,
    ( ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_21
    | ~ spl10_26
    | spl10_28
    | ~ spl10_30
    | spl10_39 ),
    inference(avatar_contradiction_clause,[],[f786])).

fof(f786,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_21
    | ~ spl10_26
    | spl10_28
    | ~ spl10_30
    | spl10_39 ),
    inference(subsumption_resolution,[],[f552,f785])).

fof(f785,plain,
    ( m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_21
    | ~ spl10_26
    | spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f784,f458])).

fof(f458,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl10_28 ),
    inference(avatar_component_clause,[],[f456])).

fof(f456,plain,
    ( spl10_28
  <=> v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f784,plain,
    ( m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_21
    | ~ spl10_26
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f779,f146])).

fof(f146,plain,
    ( v2_pre_topc(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl10_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f779,plain,
    ( m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_21
    | ~ spl10_26
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f777,f156])).

fof(f156,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl10_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f777,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_21
    | ~ spl10_26
    | ~ spl10_30 ),
    inference(resolution,[],[f636,f468])).

fof(f468,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f466])).

fof(f466,plain,
    ( spl10_30
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f636,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ l1_pre_topc(X0)
        | m1_subset_1(sK7(X0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(k1_xboole_0,X0,sK1) )
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_21
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f635,f71])).

fof(f635,plain,
    ( ! [X0] :
        ( m1_subset_1(sK7(X0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(k1_xboole_0,X0,sK1) )
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_21
    | ~ spl10_26 ),
    inference(resolution,[],[f328,f443])).

fof(f443,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f441])).

fof(f441,plain,
    ( spl10_26
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f328,plain,
    ( ! [X8,X9] :
        ( ~ v1_funct_1(X9)
        | m1_subset_1(sK7(X8,sK1,X9),k1_zfmisc_1(k1_xboole_0))
        | ~ l1_pre_topc(X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X9,u1_struct_0(X8),k1_xboole_0)
        | ~ v2_pre_topc(X8)
        | v5_pre_topc(X9,X8,sK1) )
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_21 ),
    inference(forward_demodulation,[],[f327,f126])).

fof(f327,plain,
    ( ! [X8,X9] :
        ( m1_subset_1(sK7(X8,sK1,X9),k1_zfmisc_1(k1_xboole_0))
        | ~ l1_pre_topc(X8)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X8),k1_xboole_0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),k1_xboole_0)))
        | ~ v2_pre_topc(X8)
        | v5_pre_topc(X9,X8,sK1) )
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f326,f141])).

fof(f141,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl10_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f326,plain,
    ( ! [X8,X9] :
        ( m1_subset_1(sK7(X8,sK1,X9),k1_zfmisc_1(k1_xboole_0))
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X8),k1_xboole_0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),k1_xboole_0)))
        | ~ v2_pre_topc(X8)
        | v5_pre_topc(X9,X8,sK1) )
    | ~ spl10_2
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f315,f136])).

fof(f136,plain,
    ( v2_pre_topc(sK1)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl10_2
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f315,plain,
    ( ! [X8,X9] :
        ( m1_subset_1(sK7(X8,sK1,X9),k1_zfmisc_1(k1_xboole_0))
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X8),k1_xboole_0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),k1_xboole_0)))
        | ~ v2_pre_topc(X8)
        | v5_pre_topc(X9,X8,sK1) )
    | ~ spl10_21 ),
    inference(superposition,[],[f97,f308])).

fof(f308,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl10_21
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_2)).

fof(f552,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl10_39 ),
    inference(resolution,[],[f547,f114])).

fof(f547,plain,
    ( ~ r1_tarski(sK7(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | spl10_39 ),
    inference(avatar_component_clause,[],[f545])).

fof(f641,plain,
    ( spl10_45
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f634,f272,f638])).

fof(f634,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f632,f71])).

fof(f632,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl10_18 ),
    inference(superposition,[],[f628,f118])).

fof(f628,plain,
    ( ! [X2] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k1_xboole_0)
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f624,f71])).

fof(f624,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) )
    | ~ spl10_18 ),
    inference(superposition,[],[f611,f120])).

fof(f611,plain,
    ( ! [X4,X3] : k1_xboole_0 = k8_relset_1(k1_xboole_0,X3,k1_xboole_0,X4)
    | ~ spl10_18 ),
    inference(resolution,[],[f405,f71])).

fof(f405,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X3) )
    | ~ spl10_18 ),
    inference(forward_demodulation,[],[f402,f127])).

fof(f127,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f402,plain,
    ( ! [X2,X3,X1] :
        ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl10_18 ),
    inference(resolution,[],[f342,f122])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f524,plain,
    ( ~ spl10_36
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_11
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f413,f296,f272,f198,f184,f179,f154,f149,f144,f139,f134,f129,f521])).

fof(f129,plain,
    ( spl10_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f149,plain,
    ( spl10_5
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f179,plain,
    ( spl10_7
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f184,plain,
    ( spl10_8
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f198,plain,
    ( spl10_11
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f296,plain,
    ( spl10_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f413,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK7(sK0,sK1,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK7(sK0,sK1,k1_xboole_0))))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_11
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(backward_demodulation,[],[f283,f403])).

fof(f403,plain,
    ( k1_xboole_0 = sK2
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(resolution,[],[f342,f298])).

fof(f298,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f296])).

fof(f283,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2))))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_11
    | ~ spl10_18 ),
    inference(backward_demodulation,[],[f238,f277])).

fof(f238,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2))))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f237,f181])).

fof(f181,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f179])).

fof(f237,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f236,f200])).

fof(f200,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f198])).

fof(f236,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f235,f136])).

fof(f235,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2))))
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f234,f141])).

fof(f234,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2))))
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(resolution,[],[f226,f186])).

fof(f186,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f184])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK7(sK0,X0,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,k2_pre_topc(X0,sK7(sK0,X0,sK2))))
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v5_pre_topc(sK2,sK0,X0) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(resolution,[],[f207,f131])).

fof(f131,plain,
    ( v1_funct_1(sK2)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f129])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(sK0,X0,X1))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f206,f122])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(sK0,X0,X1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v5_pre_topc(X1,sK0,X0)
        | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f205,f146])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(sK0,X0,X1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X1,sK0,X0)
        | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f203,f156])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(sK0,X0,X1))))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X1,sK0,X0)
        | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(superposition,[],[f98,f177])).

fof(f177,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f176,f173])).

fof(f173,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f172,f146])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f169,f156])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl10_5 ),
    inference(resolution,[],[f151,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).

fof(f151,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f149])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl10_6 ),
    inference(resolution,[],[f156,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK7(X0,X1,X2))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f469,plain,
    ( spl10_30
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f416,f301,f296,f272,f466])).

fof(f301,plain,
    ( spl10_20
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f416,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_20 ),
    inference(backward_demodulation,[],[f303,f403])).

fof(f303,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f301])).

fof(f459,plain,
    ( ~ spl10_28
    | spl10_7
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f410,f296,f272,f179,f456])).

fof(f410,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl10_7
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(backward_demodulation,[],[f181,f403])).

fof(f444,plain,
    ( spl10_26
    | ~ spl10_1
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f406,f296,f272,f129,f441])).

fof(f406,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl10_1
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(backward_demodulation,[],[f131,f403])).

fof(f309,plain,
    ( spl10_21
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f277,f272,f306])).

fof(f304,plain,
    ( spl10_20
    | ~ spl10_8
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f280,f272,f184,f301])).

fof(f280,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl10_8
    | ~ spl10_18 ),
    inference(backward_demodulation,[],[f186,f277])).

fof(f299,plain,
    ( spl10_19
    | ~ spl10_11
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f289,f272,f198,f296])).

fof(f289,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_11
    | ~ spl10_18 ),
    inference(forward_demodulation,[],[f281,f126])).

fof(f281,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl10_11
    | ~ spl10_18 ),
    inference(backward_demodulation,[],[f200,f277])).

fof(f275,plain,
    ( spl10_18
    | ~ spl10_16
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f270,f262,f258,f272])).

fof(f258,plain,
    ( spl10_16
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f262,plain,
    ( spl10_17
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f270,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_16
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f269,f263])).

fof(f263,plain,
    ( l1_struct_0(sK1)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f262])).

fof(f269,plain,
    ( ~ l1_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_16 ),
    inference(resolution,[],[f260,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f260,plain,
    ( v2_struct_0(sK1)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f258])).

fof(f268,plain,
    ( ~ spl10_3
    | spl10_17 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | ~ spl10_3
    | spl10_17 ),
    inference(subsumption_resolution,[],[f266,f141])).

fof(f266,plain,
    ( ~ l1_pre_topc(sK1)
    | spl10_17 ),
    inference(resolution,[],[f264,f75])).

fof(f75,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f264,plain,
    ( ~ l1_struct_0(sK1)
    | spl10_17 ),
    inference(avatar_component_clause,[],[f262])).

fof(f265,plain,
    ( spl10_16
    | ~ spl10_17
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f254,f220,f262,f258])).

fof(f220,plain,
    ( spl10_13
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f254,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f249,f69])).

fof(f69,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f249,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_13 ),
    inference(superposition,[],[f88,f222])).

fof(f222,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f220])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f248,plain,
    ( ~ spl10_11
    | spl10_15 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | ~ spl10_11
    | spl10_15 ),
    inference(subsumption_resolution,[],[f244,f200])).

fof(f244,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl10_15 ),
    inference(resolution,[],[f242,f122])).

fof(f242,plain,
    ( ~ m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl10_15 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl10_15
  <=> m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f243,plain,
    ( ~ spl10_15
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_14 ),
    inference(avatar_split_clause,[],[f233,f228,f154,f149,f144,f240])).

fof(f228,plain,
    ( spl10_14
  <=> v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f233,plain,
    ( ~ m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_14 ),
    inference(resolution,[],[f230,f175])).

fof(f175,plain,
    ( ! [X1] :
        ( v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f174,f146])).

fof(f174,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X1,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f170,f156])).

fof(f170,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X1,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl10_5 ),
    inference(resolution,[],[f151,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f230,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0)
    | spl10_14 ),
    inference(avatar_component_clause,[],[f228])).

fof(f231,plain,
    ( ~ spl10_14
    | spl10_12 ),
    inference(avatar_split_clause,[],[f225,f216,f228])).

fof(f216,plain,
    ( spl10_12
  <=> sP3(sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f225,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0)
    | spl10_12 ),
    inference(resolution,[],[f218,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X1,X0)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

fof(f218,plain,
    ( ~ sP3(sK2,sK1,sK0)
    | spl10_12 ),
    inference(avatar_component_clause,[],[f216])).

fof(f223,plain,
    ( ~ spl10_12
    | spl10_13
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f214,f198,f184,f179,f154,f139,f129,f220,f216])).

fof(f214,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ sP3(sK2,sK1,sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f213,f181])).

fof(f213,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ sP3(sK2,sK1,sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f212,f200])).

fof(f212,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ sP3(sK2,sK1,sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f211,f141])).

fof(f211,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ sP3(sK2,sK1,sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f210,f156])).

fof(f210,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ sP3(sK2,sK1,sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_1
    | ~ spl10_8 ),
    inference(resolution,[],[f159,f186])).

fof(f159,plain,
    ( ! [X4,X3] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X4),u1_struct_0(X3))
        | ~ l1_pre_topc(X4)
        | ~ l1_pre_topc(X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))
        | k1_xboole_0 = k2_struct_0(X3)
        | ~ sP3(sK2,X3,X4)
        | v5_pre_topc(sK2,X4,X3) )
    | ~ spl10_1 ),
    inference(resolution,[],[f131,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ sP3(X2,X1,X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f201,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f62,f198])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => v5_pre_topc(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tex_2)).

fof(f187,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f61,f184])).

fof(f61,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f182,plain,(
    ~ spl10_7 ),
    inference(avatar_split_clause,[],[f63,f179])).

fof(f63,plain,(
    ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f157,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f68,f154])).

fof(f68,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f152,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f67,f149])).

fof(f67,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f147,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f66,f144])).

fof(f66,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f142,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f65,f139])).

fof(f65,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f137,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f64,f134])).

fof(f64,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f132,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f60,f129])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (14959)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (14951)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (14952)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (14955)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (14974)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (14959)Refutation not found, incomplete strategy% (14959)------------------------------
% 0.20/0.53  % (14959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (14954)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (14959)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (14959)Memory used [KB]: 10618
% 0.20/0.53  % (14959)Time elapsed: 0.003 s
% 0.20/0.53  % (14959)------------------------------
% 0.20/0.53  % (14959)------------------------------
% 0.20/0.53  % (14965)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (14968)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (14950)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (14956)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (14968)Refutation not found, incomplete strategy% (14968)------------------------------
% 0.20/0.54  % (14968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14968)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14968)Memory used [KB]: 10618
% 0.20/0.54  % (14968)Time elapsed: 0.113 s
% 0.20/0.54  % (14968)------------------------------
% 0.20/0.54  % (14968)------------------------------
% 0.20/0.54  % (14963)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (14951)Refutation not found, incomplete strategy% (14951)------------------------------
% 0.20/0.54  % (14951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14951)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14951)Memory used [KB]: 11129
% 0.20/0.54  % (14951)Time elapsed: 0.113 s
% 0.20/0.54  % (14951)------------------------------
% 0.20/0.54  % (14951)------------------------------
% 0.20/0.54  % (14958)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.44/0.54  % (14979)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.44/0.54  % (14978)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.44/0.54  % (14981)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.54  % (14980)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.44/0.54  % (14958)Refutation not found, incomplete strategy% (14958)------------------------------
% 1.44/0.54  % (14958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (14958)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (14958)Memory used [KB]: 10874
% 1.44/0.54  % (14958)Time elapsed: 0.134 s
% 1.44/0.54  % (14958)------------------------------
% 1.44/0.54  % (14958)------------------------------
% 1.44/0.55  % (14957)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.44/0.55  % (14974)Refutation not found, incomplete strategy% (14974)------------------------------
% 1.44/0.55  % (14974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (14974)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (14974)Memory used [KB]: 10874
% 1.44/0.55  % (14974)Time elapsed: 0.074 s
% 1.44/0.55  % (14974)------------------------------
% 1.44/0.55  % (14974)------------------------------
% 1.44/0.55  % (14976)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.44/0.55  % (14969)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.44/0.55  % (14972)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.44/0.55  % (14970)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.44/0.55  % (14971)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.44/0.55  % (14961)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.44/0.55  % (14949)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.44/0.55  % (14949)Refutation not found, incomplete strategy% (14949)------------------------------
% 1.44/0.55  % (14949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (14949)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (14949)Memory used [KB]: 1663
% 1.44/0.55  % (14949)Time elapsed: 0.001 s
% 1.44/0.55  % (14949)------------------------------
% 1.44/0.55  % (14949)------------------------------
% 1.44/0.55  % (14961)Refutation not found, incomplete strategy% (14961)------------------------------
% 1.44/0.55  % (14961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (14961)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (14961)Memory used [KB]: 10618
% 1.44/0.55  % (14961)Time elapsed: 0.143 s
% 1.44/0.55  % (14961)------------------------------
% 1.44/0.55  % (14961)------------------------------
% 1.44/0.55  % (14962)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.55  % (14964)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.44/0.55  % (14960)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.44/0.56  % (14960)Refutation not found, incomplete strategy% (14960)------------------------------
% 1.44/0.56  % (14960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (14960)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (14960)Memory used [KB]: 10618
% 1.44/0.56  % (14960)Time elapsed: 0.147 s
% 1.44/0.56  % (14960)------------------------------
% 1.44/0.56  % (14960)------------------------------
% 1.44/0.56  % (14977)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.59/0.56  % (14967)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.59/0.57  % (14975)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.96/0.63  % (15017)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.96/0.63  % (14971)Refutation found. Thanks to Tanya!
% 1.96/0.63  % SZS status Theorem for theBenchmark
% 1.96/0.63  % SZS output start Proof for theBenchmark
% 1.96/0.63  fof(f855,plain,(
% 1.96/0.63    $false),
% 1.96/0.63    inference(avatar_sat_refutation,[],[f132,f137,f142,f147,f152,f157,f182,f187,f201,f223,f231,f243,f248,f265,f268,f275,f299,f304,f309,f444,f459,f469,f524,f641,f787,f812,f837,f846,f854])).
% 1.96/0.63  fof(f854,plain,(
% 1.96/0.63    spl10_61),
% 1.96/0.63    inference(avatar_contradiction_clause,[],[f853])).
% 1.96/0.63  fof(f853,plain,(
% 1.96/0.63    $false | spl10_61),
% 1.96/0.63    inference(subsumption_resolution,[],[f852,f71])).
% 1.96/0.63  fof(f71,plain,(
% 1.96/0.63    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.96/0.63    inference(cnf_transformation,[],[f7])).
% 1.96/0.63  fof(f7,axiom,(
% 1.96/0.63    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.96/0.63  fof(f852,plain,(
% 1.96/0.63    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))) | spl10_61),
% 1.96/0.63    inference(resolution,[],[f845,f114])).
% 1.96/0.63  fof(f114,plain,(
% 1.96/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.96/0.63    inference(cnf_transformation,[],[f8])).
% 1.96/0.63  fof(f8,axiom,(
% 1.96/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.96/0.63  fof(f845,plain,(
% 1.96/0.63    ~r1_tarski(k1_xboole_0,k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | spl10_61),
% 1.96/0.63    inference(avatar_component_clause,[],[f843])).
% 1.96/0.63  fof(f843,plain,(
% 1.96/0.63    spl10_61 <=> r1_tarski(k1_xboole_0,k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).
% 1.96/0.63  fof(f846,plain,(
% 1.96/0.63    ~spl10_61 | ~spl10_45 | spl10_60),
% 1.96/0.63    inference(avatar_split_clause,[],[f841,f834,f638,f843])).
% 1.96/0.63  fof(f638,plain,(
% 1.96/0.63    spl10_45 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).
% 1.96/0.63  fof(f834,plain,(
% 1.96/0.63    spl10_60 <=> r1_tarski(k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).
% 1.96/0.63  fof(f841,plain,(
% 1.96/0.63    ~r1_tarski(k1_xboole_0,k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | (~spl10_45 | spl10_60)),
% 1.96/0.63    inference(forward_demodulation,[],[f840,f640])).
% 1.96/0.63  fof(f640,plain,(
% 1.96/0.63    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl10_45),
% 1.96/0.63    inference(avatar_component_clause,[],[f638])).
% 1.96/0.63  fof(f840,plain,(
% 1.96/0.63    ~r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | spl10_60),
% 1.96/0.63    inference(subsumption_resolution,[],[f839,f71])).
% 1.96/0.63  fof(f839,plain,(
% 1.96/0.63    ~r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | spl10_60),
% 1.96/0.63    inference(superposition,[],[f836,f118])).
% 1.96/0.63  fof(f118,plain,(
% 1.96/0.63    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.96/0.63    inference(cnf_transformation,[],[f55])).
% 1.96/0.63  fof(f55,plain,(
% 1.96/0.63    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/0.63    inference(ennf_transformation,[],[f15])).
% 1.96/0.63  fof(f15,axiom,(
% 1.96/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.96/0.63  fof(f836,plain,(
% 1.96/0.63    ~r1_tarski(k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | spl10_60),
% 1.96/0.63    inference(avatar_component_clause,[],[f834])).
% 1.96/0.63  fof(f837,plain,(
% 1.96/0.63    ~spl10_60 | spl10_58),
% 1.96/0.63    inference(avatar_split_clause,[],[f820,f809,f834])).
% 1.96/0.63  fof(f809,plain,(
% 1.96/0.63    spl10_58 <=> r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).
% 1.96/0.63  fof(f820,plain,(
% 1.96/0.63    ~r1_tarski(k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | spl10_58),
% 1.96/0.63    inference(subsumption_resolution,[],[f819,f71])).
% 1.96/0.63  fof(f819,plain,(
% 1.96/0.63    ~r1_tarski(k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | spl10_58),
% 1.96/0.63    inference(superposition,[],[f811,f120])).
% 1.96/0.63  fof(f120,plain,(
% 1.96/0.63    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.96/0.63    inference(cnf_transformation,[],[f56])).
% 1.96/0.63  fof(f56,plain,(
% 1.96/0.63    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/0.63    inference(ennf_transformation,[],[f16])).
% 1.96/0.63  fof(f16,axiom,(
% 1.96/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 1.96/0.63  fof(f811,plain,(
% 1.96/0.63    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | spl10_58),
% 1.96/0.63    inference(avatar_component_clause,[],[f809])).
% 1.96/0.63  fof(f812,plain,(
% 1.96/0.63    ~spl10_58 | ~spl10_18 | spl10_36 | ~spl10_39),
% 1.96/0.63    inference(avatar_split_clause,[],[f793,f545,f521,f272,f809])).
% 1.96/0.63  fof(f272,plain,(
% 1.96/0.63    spl10_18 <=> v1_xboole_0(u1_struct_0(sK1))),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 1.96/0.63  fof(f521,plain,(
% 1.96/0.63    spl10_36 <=> r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK7(sK0,sK1,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK7(sK0,sK1,k1_xboole_0))))),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).
% 1.96/0.63  fof(f545,plain,(
% 1.96/0.63    spl10_39 <=> r1_tarski(sK7(sK0,sK1,k1_xboole_0),k1_xboole_0)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).
% 1.96/0.63  fof(f793,plain,(
% 1.96/0.63    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | (~spl10_18 | spl10_36 | ~spl10_39)),
% 1.96/0.63    inference(backward_demodulation,[],[f523,f790])).
% 1.96/0.63  fof(f790,plain,(
% 1.96/0.63    k1_xboole_0 = sK7(sK0,sK1,k1_xboole_0) | (~spl10_18 | ~spl10_39)),
% 1.96/0.63    inference(resolution,[],[f546,f400])).
% 1.96/0.63  fof(f400,plain,(
% 1.96/0.63    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl10_18),
% 1.96/0.63    inference(resolution,[],[f342,f113])).
% 1.96/0.63  fof(f113,plain,(
% 1.96/0.63    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.96/0.63    inference(cnf_transformation,[],[f8])).
% 1.96/0.63  fof(f342,plain,(
% 1.96/0.63    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X3) ) | ~spl10_18),
% 1.96/0.63    inference(resolution,[],[f294,f87])).
% 1.96/0.63  fof(f87,plain,(
% 1.96/0.63    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.96/0.63    inference(cnf_transformation,[],[f40])).
% 1.96/0.63  fof(f40,plain,(
% 1.96/0.63    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.96/0.63    inference(ennf_transformation,[],[f4])).
% 1.96/0.63  fof(f4,axiom,(
% 1.96/0.63    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.96/0.63  fof(f294,plain,(
% 1.96/0.63    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl10_18),
% 1.96/0.63    inference(forward_demodulation,[],[f288,f126])).
% 1.96/0.63  fof(f126,plain,(
% 1.96/0.63    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.96/0.63    inference(equality_resolution,[],[f117])).
% 1.96/0.63  fof(f117,plain,(
% 1.96/0.63    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.96/0.63    inference(cnf_transformation,[],[f6])).
% 1.96/0.63  fof(f6,axiom,(
% 1.96/0.63    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.96/0.63  fof(f288,plain,(
% 1.96/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) ) | ~spl10_18),
% 1.96/0.63    inference(backward_demodulation,[],[f276,f277])).
% 1.96/0.63  fof(f277,plain,(
% 1.96/0.63    k1_xboole_0 = u1_struct_0(sK1) | ~spl10_18),
% 1.96/0.63    inference(resolution,[],[f274,f87])).
% 1.96/0.63  fof(f274,plain,(
% 1.96/0.63    v1_xboole_0(u1_struct_0(sK1)) | ~spl10_18),
% 1.96/0.63    inference(avatar_component_clause,[],[f272])).
% 1.96/0.63  fof(f276,plain,(
% 1.96/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1)))) | v1_xboole_0(X0)) ) | ~spl10_18),
% 1.96/0.63    inference(resolution,[],[f274,f104])).
% 1.96/0.63  fof(f104,plain,(
% 1.96/0.63    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 1.96/0.63    inference(cnf_transformation,[],[f51])).
% 1.96/0.63  fof(f51,plain,(
% 1.96/0.63    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.96/0.63    inference(ennf_transformation,[],[f13])).
% 1.96/0.63  fof(f13,axiom,(
% 1.96/0.63    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.96/0.63  fof(f546,plain,(
% 1.96/0.63    r1_tarski(sK7(sK0,sK1,k1_xboole_0),k1_xboole_0) | ~spl10_39),
% 1.96/0.63    inference(avatar_component_clause,[],[f545])).
% 1.96/0.63  fof(f523,plain,(
% 1.96/0.63    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK7(sK0,sK1,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK7(sK0,sK1,k1_xboole_0)))) | spl10_36),
% 1.96/0.63    inference(avatar_component_clause,[],[f521])).
% 1.96/0.63  fof(f787,plain,(
% 1.96/0.63    ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_6 | ~spl10_21 | ~spl10_26 | spl10_28 | ~spl10_30 | spl10_39),
% 1.96/0.63    inference(avatar_contradiction_clause,[],[f786])).
% 1.96/0.63  fof(f786,plain,(
% 1.96/0.63    $false | (~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_6 | ~spl10_21 | ~spl10_26 | spl10_28 | ~spl10_30 | spl10_39)),
% 1.96/0.63    inference(subsumption_resolution,[],[f552,f785])).
% 1.96/0.63  fof(f785,plain,(
% 1.96/0.63    m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_6 | ~spl10_21 | ~spl10_26 | spl10_28 | ~spl10_30)),
% 1.96/0.63    inference(subsumption_resolution,[],[f784,f458])).
% 1.96/0.63  fof(f458,plain,(
% 1.96/0.63    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | spl10_28),
% 1.96/0.63    inference(avatar_component_clause,[],[f456])).
% 1.96/0.63  fof(f456,plain,(
% 1.96/0.63    spl10_28 <=> v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).
% 1.96/0.63  fof(f784,plain,(
% 1.96/0.63    m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_6 | ~spl10_21 | ~spl10_26 | ~spl10_30)),
% 1.96/0.63    inference(subsumption_resolution,[],[f779,f146])).
% 1.96/0.63  fof(f146,plain,(
% 1.96/0.63    v2_pre_topc(sK0) | ~spl10_4),
% 1.96/0.63    inference(avatar_component_clause,[],[f144])).
% 1.96/0.63  fof(f144,plain,(
% 1.96/0.63    spl10_4 <=> v2_pre_topc(sK0)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.96/0.63  fof(f779,plain,(
% 1.96/0.63    m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl10_2 | ~spl10_3 | ~spl10_6 | ~spl10_21 | ~spl10_26 | ~spl10_30)),
% 1.96/0.63    inference(subsumption_resolution,[],[f777,f156])).
% 1.96/0.63  fof(f156,plain,(
% 1.96/0.63    l1_pre_topc(sK0) | ~spl10_6),
% 1.96/0.63    inference(avatar_component_clause,[],[f154])).
% 1.96/0.63  fof(f154,plain,(
% 1.96/0.63    spl10_6 <=> l1_pre_topc(sK0)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.96/0.63  fof(f777,plain,(
% 1.96/0.63    ~l1_pre_topc(sK0) | m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl10_2 | ~spl10_3 | ~spl10_21 | ~spl10_26 | ~spl10_30)),
% 1.96/0.63    inference(resolution,[],[f636,f468])).
% 1.96/0.63  fof(f468,plain,(
% 1.96/0.63    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~spl10_30),
% 1.96/0.63    inference(avatar_component_clause,[],[f466])).
% 1.96/0.63  fof(f466,plain,(
% 1.96/0.63    spl10_30 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 1.96/0.63  fof(f636,plain,(
% 1.96/0.63    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~l1_pre_topc(X0) | m1_subset_1(sK7(X0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(X0) | v5_pre_topc(k1_xboole_0,X0,sK1)) ) | (~spl10_2 | ~spl10_3 | ~spl10_21 | ~spl10_26)),
% 1.96/0.63    inference(subsumption_resolution,[],[f635,f71])).
% 1.96/0.63  fof(f635,plain,(
% 1.96/0.63    ( ! [X0] : (m1_subset_1(sK7(X0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v2_pre_topc(X0) | v5_pre_topc(k1_xboole_0,X0,sK1)) ) | (~spl10_2 | ~spl10_3 | ~spl10_21 | ~spl10_26)),
% 1.96/0.63    inference(resolution,[],[f328,f443])).
% 1.96/0.63  fof(f443,plain,(
% 1.96/0.63    v1_funct_1(k1_xboole_0) | ~spl10_26),
% 1.96/0.63    inference(avatar_component_clause,[],[f441])).
% 1.96/0.63  fof(f441,plain,(
% 1.96/0.63    spl10_26 <=> v1_funct_1(k1_xboole_0)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 1.96/0.63  fof(f328,plain,(
% 1.96/0.63    ( ! [X8,X9] : (~v1_funct_1(X9) | m1_subset_1(sK7(X8,sK1,X9),k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc(X8) | ~m1_subset_1(X9,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X9,u1_struct_0(X8),k1_xboole_0) | ~v2_pre_topc(X8) | v5_pre_topc(X9,X8,sK1)) ) | (~spl10_2 | ~spl10_3 | ~spl10_21)),
% 1.96/0.63    inference(forward_demodulation,[],[f327,f126])).
% 1.96/0.63  fof(f327,plain,(
% 1.96/0.63    ( ! [X8,X9] : (m1_subset_1(sK7(X8,sK1,X9),k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc(X8) | ~v1_funct_1(X9) | ~v1_funct_2(X9,u1_struct_0(X8),k1_xboole_0) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),k1_xboole_0))) | ~v2_pre_topc(X8) | v5_pre_topc(X9,X8,sK1)) ) | (~spl10_2 | ~spl10_3 | ~spl10_21)),
% 1.96/0.63    inference(subsumption_resolution,[],[f326,f141])).
% 1.96/0.63  fof(f141,plain,(
% 1.96/0.63    l1_pre_topc(sK1) | ~spl10_3),
% 1.96/0.63    inference(avatar_component_clause,[],[f139])).
% 1.96/0.63  fof(f139,plain,(
% 1.96/0.63    spl10_3 <=> l1_pre_topc(sK1)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.96/0.63  fof(f326,plain,(
% 1.96/0.63    ( ! [X8,X9] : (m1_subset_1(sK7(X8,sK1,X9),k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc(X8) | ~l1_pre_topc(sK1) | ~v1_funct_1(X9) | ~v1_funct_2(X9,u1_struct_0(X8),k1_xboole_0) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),k1_xboole_0))) | ~v2_pre_topc(X8) | v5_pre_topc(X9,X8,sK1)) ) | (~spl10_2 | ~spl10_21)),
% 1.96/0.63    inference(subsumption_resolution,[],[f315,f136])).
% 1.96/0.63  fof(f136,plain,(
% 1.96/0.63    v2_pre_topc(sK1) | ~spl10_2),
% 1.96/0.63    inference(avatar_component_clause,[],[f134])).
% 1.96/0.63  fof(f134,plain,(
% 1.96/0.63    spl10_2 <=> v2_pre_topc(sK1)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.96/0.63  fof(f315,plain,(
% 1.96/0.63    ( ! [X8,X9] : (m1_subset_1(sK7(X8,sK1,X9),k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc(X8) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X9) | ~v1_funct_2(X9,u1_struct_0(X8),k1_xboole_0) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),k1_xboole_0))) | ~v2_pre_topc(X8) | v5_pre_topc(X9,X8,sK1)) ) | ~spl10_21),
% 1.96/0.63    inference(superposition,[],[f97,f308])).
% 1.96/0.63  fof(f308,plain,(
% 1.96/0.63    k1_xboole_0 = u1_struct_0(sK1) | ~spl10_21),
% 1.96/0.63    inference(avatar_component_clause,[],[f306])).
% 1.96/0.63  fof(f306,plain,(
% 1.96/0.63    spl10_21 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 1.96/0.63  fof(f97,plain,(
% 1.96/0.63    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | v5_pre_topc(X2,X0,X1)) )),
% 1.96/0.63    inference(cnf_transformation,[],[f50])).
% 1.96/0.63  fof(f50,plain,(
% 1.96/0.63    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.96/0.63    inference(flattening,[],[f49])).
% 1.96/0.63  fof(f49,plain,(
% 1.96/0.63    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.96/0.63    inference(ennf_transformation,[],[f25])).
% 1.96/0.63  fof(f25,axiom,(
% 1.96/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))))))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_2)).
% 1.96/0.63  fof(f552,plain,(
% 1.96/0.63    ~m1_subset_1(sK7(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | spl10_39),
% 1.96/0.63    inference(resolution,[],[f547,f114])).
% 1.96/0.63  fof(f547,plain,(
% 1.96/0.63    ~r1_tarski(sK7(sK0,sK1,k1_xboole_0),k1_xboole_0) | spl10_39),
% 1.96/0.63    inference(avatar_component_clause,[],[f545])).
% 1.96/0.63  fof(f641,plain,(
% 1.96/0.63    spl10_45 | ~spl10_18),
% 1.96/0.63    inference(avatar_split_clause,[],[f634,f272,f638])).
% 1.96/0.63  fof(f634,plain,(
% 1.96/0.63    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl10_18),
% 1.96/0.63    inference(subsumption_resolution,[],[f632,f71])).
% 1.96/0.63  fof(f632,plain,(
% 1.96/0.63    ( ! [X1] : (k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) ) | ~spl10_18),
% 1.96/0.63    inference(superposition,[],[f628,f118])).
% 1.96/0.63  fof(f628,plain,(
% 1.96/0.63    ( ! [X2] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k1_xboole_0)) ) | ~spl10_18),
% 1.96/0.63    inference(subsumption_resolution,[],[f624,f71])).
% 1.96/0.63  fof(f624,plain,(
% 1.96/0.63    ( ! [X2] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) ) | ~spl10_18),
% 1.96/0.63    inference(superposition,[],[f611,f120])).
% 1.96/0.63  fof(f611,plain,(
% 1.96/0.63    ( ! [X4,X3] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X3,k1_xboole_0,X4)) ) | ~spl10_18),
% 1.96/0.63    inference(resolution,[],[f405,f71])).
% 1.96/0.63  fof(f405,plain,(
% 1.96/0.63    ( ! [X2,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X3)) ) | ~spl10_18),
% 1.96/0.63    inference(forward_demodulation,[],[f402,f127])).
% 1.96/0.63  fof(f127,plain,(
% 1.96/0.63    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.96/0.63    inference(equality_resolution,[],[f116])).
% 1.96/0.63  fof(f116,plain,(
% 1.96/0.63    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.96/0.63    inference(cnf_transformation,[],[f6])).
% 1.96/0.63  fof(f402,plain,(
% 1.96/0.63    ( ! [X2,X3,X1] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) ) | ~spl10_18),
% 1.96/0.63    inference(resolution,[],[f342,f122])).
% 1.96/0.63  fof(f122,plain,(
% 1.96/0.63    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.96/0.63    inference(cnf_transformation,[],[f59])).
% 1.96/0.63  fof(f59,plain,(
% 1.96/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/0.63    inference(ennf_transformation,[],[f14])).
% 1.96/0.63  fof(f14,axiom,(
% 1.96/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 1.96/0.63  fof(f524,plain,(
% 1.96/0.63    ~spl10_36 | ~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_11 | ~spl10_18 | ~spl10_19),
% 1.96/0.63    inference(avatar_split_clause,[],[f413,f296,f272,f198,f184,f179,f154,f149,f144,f139,f134,f129,f521])).
% 1.96/0.63  fof(f129,plain,(
% 1.96/0.63    spl10_1 <=> v1_funct_1(sK2)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.96/0.63  fof(f149,plain,(
% 1.96/0.63    spl10_5 <=> v1_tdlat_3(sK0)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.96/0.63  fof(f179,plain,(
% 1.96/0.63    spl10_7 <=> v5_pre_topc(sK2,sK0,sK1)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 1.96/0.63  fof(f184,plain,(
% 1.96/0.63    spl10_8 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 1.96/0.63  fof(f198,plain,(
% 1.96/0.63    spl10_11 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 1.96/0.63  fof(f296,plain,(
% 1.96/0.63    spl10_19 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 1.96/0.63  fof(f413,plain,(
% 1.96/0.63    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK7(sK0,sK1,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK7(sK0,sK1,k1_xboole_0)))) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_11 | ~spl10_18 | ~spl10_19)),
% 1.96/0.63    inference(backward_demodulation,[],[f283,f403])).
% 1.96/0.63  fof(f403,plain,(
% 1.96/0.63    k1_xboole_0 = sK2 | (~spl10_18 | ~spl10_19)),
% 1.96/0.63    inference(resolution,[],[f342,f298])).
% 1.96/0.63  fof(f298,plain,(
% 1.96/0.63    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl10_19),
% 1.96/0.63    inference(avatar_component_clause,[],[f296])).
% 1.96/0.63  fof(f283,plain,(
% 1.96/0.63    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2)))) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_11 | ~spl10_18)),
% 1.96/0.63    inference(backward_demodulation,[],[f238,f277])).
% 1.96/0.63  fof(f238,plain,(
% 1.96/0.63    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2)))) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_11)),
% 1.96/0.63    inference(subsumption_resolution,[],[f237,f181])).
% 1.96/0.63  fof(f181,plain,(
% 1.96/0.63    ~v5_pre_topc(sK2,sK0,sK1) | spl10_7),
% 1.96/0.63    inference(avatar_component_clause,[],[f179])).
% 1.96/0.63  fof(f237,plain,(
% 1.96/0.63    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2)))) | v5_pre_topc(sK2,sK0,sK1) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_8 | ~spl10_11)),
% 1.96/0.63    inference(subsumption_resolution,[],[f236,f200])).
% 1.96/0.63  fof(f200,plain,(
% 1.96/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl10_11),
% 1.96/0.63    inference(avatar_component_clause,[],[f198])).
% 1.96/0.63  fof(f236,plain,(
% 1.96/0.63    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_8)),
% 1.96/0.63    inference(subsumption_resolution,[],[f235,f136])).
% 1.96/0.63  fof(f235,plain,(
% 1.96/0.63    ~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2)))) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | (~spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_8)),
% 1.96/0.63    inference(subsumption_resolution,[],[f234,f141])).
% 1.96/0.63  fof(f234,plain,(
% 1.96/0.63    ~l1_pre_topc(sK1) | ~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(sK0,sK1,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK7(sK0,sK1,sK2)))) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | (~spl10_1 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_8)),
% 1.96/0.63    inference(resolution,[],[f226,f186])).
% 1.96/0.63  fof(f186,plain,(
% 1.96/0.63    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl10_8),
% 1.96/0.63    inference(avatar_component_clause,[],[f184])).
% 1.96/0.63  fof(f226,plain,(
% 1.96/0.63    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK7(sK0,X0,sK2)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,k2_pre_topc(X0,sK7(sK0,X0,sK2)))) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v5_pre_topc(sK2,sK0,X0)) ) | (~spl10_1 | ~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.96/0.63    inference(resolution,[],[f207,f131])).
% 1.96/0.63  fof(f131,plain,(
% 1.96/0.63    v1_funct_1(sK2) | ~spl10_1),
% 1.96/0.63    inference(avatar_component_clause,[],[f129])).
% 1.96/0.63  fof(f207,plain,(
% 1.96/0.63    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(sK0,X0,X1)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v5_pre_topc(X1,sK0,X0)) ) | (~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.96/0.63    inference(subsumption_resolution,[],[f206,f122])).
% 1.96/0.63  fof(f206,plain,(
% 1.96/0.63    ( ! [X0,X1] : (~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(sK0,X0,X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.96/0.63    inference(subsumption_resolution,[],[f205,f146])).
% 1.96/0.63  fof(f205,plain,(
% 1.96/0.63    ( ! [X0,X1] : (~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(sK0,X0,X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v2_pre_topc(sK0) | v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.96/0.63    inference(subsumption_resolution,[],[f203,f156])).
% 1.96/0.63  fof(f203,plain,(
% 1.96/0.63    ( ! [X0,X1] : (~r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(sK0,X0,X1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v2_pre_topc(sK0) | v5_pre_topc(X1,sK0,X0) | ~m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK7(sK0,X0,X1)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.96/0.63    inference(superposition,[],[f98,f177])).
% 1.96/0.63  fof(f177,plain,(
% 1.96/0.63    ( ! [X0] : (k2_pre_topc(sK0,X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.96/0.63    inference(subsumption_resolution,[],[f176,f173])).
% 1.96/0.63  fof(f173,plain,(
% 1.96/0.63    ( ! [X0] : (v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.96/0.63    inference(subsumption_resolution,[],[f172,f146])).
% 1.96/0.63  fof(f172,plain,(
% 1.96/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~v2_pre_topc(sK0)) ) | (~spl10_5 | ~spl10_6)),
% 1.96/0.63    inference(subsumption_resolution,[],[f169,f156])).
% 1.96/0.63  fof(f169,plain,(
% 1.96/0.63    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~v2_pre_topc(sK0)) ) | ~spl10_5),
% 1.96/0.63    inference(resolution,[],[f151,f93])).
% 1.96/0.63  fof(f93,plain,(
% 1.96/0.63    ( ! [X0,X1] : (~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 1.96/0.63    inference(cnf_transformation,[],[f48])).
% 1.96/0.63  fof(f48,plain,(
% 1.96/0.63    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.96/0.63    inference(flattening,[],[f47])).
% 1.96/0.63  fof(f47,plain,(
% 1.96/0.63    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.96/0.63    inference(ennf_transformation,[],[f28])).
% 1.96/0.63  fof(f28,axiom,(
% 1.96/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v4_pre_topc(X1,X0))))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).
% 1.96/0.63  fof(f151,plain,(
% 1.96/0.63    v1_tdlat_3(sK0) | ~spl10_5),
% 1.96/0.63    inference(avatar_component_clause,[],[f149])).
% 1.96/0.63  fof(f176,plain,(
% 1.96/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) = X0) ) | ~spl10_6),
% 1.96/0.63    inference(resolution,[],[f156,f86])).
% 1.96/0.63  fof(f86,plain,(
% 1.96/0.63    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.96/0.63    inference(cnf_transformation,[],[f39])).
% 1.96/0.63  fof(f39,plain,(
% 1.96/0.63    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.96/0.63    inference(flattening,[],[f38])).
% 1.96/0.63  fof(f38,plain,(
% 1.96/0.63    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.96/0.63    inference(ennf_transformation,[],[f23])).
% 1.96/0.63  fof(f23,axiom,(
% 1.96/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.96/0.63  fof(f98,plain,(
% 1.96/0.63    ( ! [X2,X0,X1] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK7(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK7(X0,X1,X2)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | v5_pre_topc(X2,X0,X1)) )),
% 1.96/0.63    inference(cnf_transformation,[],[f50])).
% 1.96/0.63  fof(f469,plain,(
% 1.96/0.63    spl10_30 | ~spl10_18 | ~spl10_19 | ~spl10_20),
% 1.96/0.63    inference(avatar_split_clause,[],[f416,f301,f296,f272,f466])).
% 1.96/0.63  fof(f301,plain,(
% 1.96/0.63    spl10_20 <=> v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 1.96/0.63  fof(f416,plain,(
% 1.96/0.63    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl10_18 | ~spl10_19 | ~spl10_20)),
% 1.96/0.63    inference(backward_demodulation,[],[f303,f403])).
% 1.96/0.63  fof(f303,plain,(
% 1.96/0.63    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~spl10_20),
% 1.96/0.63    inference(avatar_component_clause,[],[f301])).
% 1.96/0.63  fof(f459,plain,(
% 1.96/0.63    ~spl10_28 | spl10_7 | ~spl10_18 | ~spl10_19),
% 1.96/0.63    inference(avatar_split_clause,[],[f410,f296,f272,f179,f456])).
% 1.96/0.63  fof(f410,plain,(
% 1.96/0.63    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl10_7 | ~spl10_18 | ~spl10_19)),
% 1.96/0.63    inference(backward_demodulation,[],[f181,f403])).
% 1.96/0.63  fof(f444,plain,(
% 1.96/0.63    spl10_26 | ~spl10_1 | ~spl10_18 | ~spl10_19),
% 1.96/0.63    inference(avatar_split_clause,[],[f406,f296,f272,f129,f441])).
% 1.96/0.63  fof(f406,plain,(
% 1.96/0.63    v1_funct_1(k1_xboole_0) | (~spl10_1 | ~spl10_18 | ~spl10_19)),
% 1.96/0.63    inference(backward_demodulation,[],[f131,f403])).
% 1.96/0.63  fof(f309,plain,(
% 1.96/0.63    spl10_21 | ~spl10_18),
% 1.96/0.63    inference(avatar_split_clause,[],[f277,f272,f306])).
% 1.96/0.63  fof(f304,plain,(
% 1.96/0.63    spl10_20 | ~spl10_8 | ~spl10_18),
% 1.96/0.63    inference(avatar_split_clause,[],[f280,f272,f184,f301])).
% 1.96/0.63  fof(f280,plain,(
% 1.96/0.63    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (~spl10_8 | ~spl10_18)),
% 1.96/0.63    inference(backward_demodulation,[],[f186,f277])).
% 1.96/0.63  fof(f299,plain,(
% 1.96/0.63    spl10_19 | ~spl10_11 | ~spl10_18),
% 1.96/0.63    inference(avatar_split_clause,[],[f289,f272,f198,f296])).
% 1.96/0.63  fof(f289,plain,(
% 1.96/0.63    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl10_11 | ~spl10_18)),
% 1.96/0.63    inference(forward_demodulation,[],[f281,f126])).
% 1.96/0.63  fof(f281,plain,(
% 1.96/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | (~spl10_11 | ~spl10_18)),
% 1.96/0.63    inference(backward_demodulation,[],[f200,f277])).
% 1.96/0.63  fof(f275,plain,(
% 1.96/0.63    spl10_18 | ~spl10_16 | ~spl10_17),
% 1.96/0.63    inference(avatar_split_clause,[],[f270,f262,f258,f272])).
% 1.96/0.63  fof(f258,plain,(
% 1.96/0.63    spl10_16 <=> v2_struct_0(sK1)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 1.96/0.63  fof(f262,plain,(
% 1.96/0.63    spl10_17 <=> l1_struct_0(sK1)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 1.96/0.63  fof(f270,plain,(
% 1.96/0.63    v1_xboole_0(u1_struct_0(sK1)) | (~spl10_16 | ~spl10_17)),
% 1.96/0.63    inference(subsumption_resolution,[],[f269,f263])).
% 1.96/0.63  fof(f263,plain,(
% 1.96/0.63    l1_struct_0(sK1) | ~spl10_17),
% 1.96/0.63    inference(avatar_component_clause,[],[f262])).
% 1.96/0.63  fof(f269,plain,(
% 1.96/0.63    ~l1_struct_0(sK1) | v1_xboole_0(u1_struct_0(sK1)) | ~spl10_16),
% 1.96/0.63    inference(resolution,[],[f260,f89])).
% 1.96/0.63  fof(f89,plain,(
% 1.96/0.63    ( ! [X0] : (~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) )),
% 1.96/0.63    inference(cnf_transformation,[],[f44])).
% 1.96/0.63  fof(f44,plain,(
% 1.96/0.63    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 1.96/0.63    inference(flattening,[],[f43])).
% 1.96/0.63  fof(f43,plain,(
% 1.96/0.63    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 1.96/0.63    inference(ennf_transformation,[],[f21])).
% 1.96/0.63  fof(f21,axiom,(
% 1.96/0.63    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).
% 1.96/0.63  fof(f260,plain,(
% 1.96/0.63    v2_struct_0(sK1) | ~spl10_16),
% 1.96/0.63    inference(avatar_component_clause,[],[f258])).
% 1.96/0.63  fof(f268,plain,(
% 1.96/0.63    ~spl10_3 | spl10_17),
% 1.96/0.63    inference(avatar_contradiction_clause,[],[f267])).
% 1.96/0.63  fof(f267,plain,(
% 1.96/0.63    $false | (~spl10_3 | spl10_17)),
% 1.96/0.63    inference(subsumption_resolution,[],[f266,f141])).
% 1.96/0.63  fof(f266,plain,(
% 1.96/0.63    ~l1_pre_topc(sK1) | spl10_17),
% 1.96/0.63    inference(resolution,[],[f264,f75])).
% 1.96/0.63  fof(f75,plain,(
% 1.96/0.63    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.96/0.63    inference(cnf_transformation,[],[f33])).
% 1.96/0.63  fof(f33,plain,(
% 1.96/0.63    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.96/0.63    inference(ennf_transformation,[],[f20])).
% 1.96/0.63  fof(f20,axiom,(
% 1.96/0.63    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.96/0.63  fof(f264,plain,(
% 1.96/0.63    ~l1_struct_0(sK1) | spl10_17),
% 1.96/0.63    inference(avatar_component_clause,[],[f262])).
% 1.96/0.63  fof(f265,plain,(
% 1.96/0.63    spl10_16 | ~spl10_17 | ~spl10_13),
% 1.96/0.63    inference(avatar_split_clause,[],[f254,f220,f262,f258])).
% 1.96/0.63  fof(f220,plain,(
% 1.96/0.63    spl10_13 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 1.96/0.63  fof(f254,plain,(
% 1.96/0.63    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl10_13),
% 1.96/0.63    inference(subsumption_resolution,[],[f249,f69])).
% 1.96/0.63  fof(f69,plain,(
% 1.96/0.63    v1_xboole_0(k1_xboole_0)),
% 1.96/0.63    inference(cnf_transformation,[],[f3])).
% 1.96/0.63  fof(f3,axiom,(
% 1.96/0.63    v1_xboole_0(k1_xboole_0)),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.96/0.63  fof(f249,plain,(
% 1.96/0.63    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl10_13),
% 1.96/0.63    inference(superposition,[],[f88,f222])).
% 1.96/0.63  fof(f222,plain,(
% 1.96/0.63    k1_xboole_0 = k2_struct_0(sK1) | ~spl10_13),
% 1.96/0.63    inference(avatar_component_clause,[],[f220])).
% 1.96/0.63  fof(f88,plain,(
% 1.96/0.63    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.96/0.63    inference(cnf_transformation,[],[f42])).
% 1.96/0.63  fof(f42,plain,(
% 1.96/0.63    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.96/0.63    inference(flattening,[],[f41])).
% 1.96/0.63  fof(f41,plain,(
% 1.96/0.63    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.96/0.63    inference(ennf_transformation,[],[f22])).
% 1.96/0.63  fof(f22,axiom,(
% 1.96/0.63    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 1.96/0.63  fof(f248,plain,(
% 1.96/0.63    ~spl10_11 | spl10_15),
% 1.96/0.63    inference(avatar_contradiction_clause,[],[f247])).
% 1.96/0.63  fof(f247,plain,(
% 1.96/0.63    $false | (~spl10_11 | spl10_15)),
% 1.96/0.63    inference(subsumption_resolution,[],[f244,f200])).
% 1.96/0.63  fof(f244,plain,(
% 1.96/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl10_15),
% 1.96/0.63    inference(resolution,[],[f242,f122])).
% 1.96/0.63  fof(f242,plain,(
% 1.96/0.63    ~m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl10_15),
% 1.96/0.63    inference(avatar_component_clause,[],[f240])).
% 1.96/0.63  fof(f240,plain,(
% 1.96/0.63    spl10_15 <=> m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 1.96/0.63  fof(f243,plain,(
% 1.96/0.63    ~spl10_15 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_14),
% 1.96/0.63    inference(avatar_split_clause,[],[f233,f228,f154,f149,f144,f240])).
% 1.96/0.63  fof(f228,plain,(
% 1.96/0.63    spl10_14 <=> v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 1.96/0.63  fof(f233,plain,(
% 1.96/0.63    ~m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_14)),
% 1.96/0.63    inference(resolution,[],[f230,f175])).
% 1.96/0.63  fof(f175,plain,(
% 1.96/0.63    ( ! [X1] : (v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl10_4 | ~spl10_5 | ~spl10_6)),
% 1.96/0.63    inference(subsumption_resolution,[],[f174,f146])).
% 1.96/0.63  fof(f174,plain,(
% 1.96/0.63    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK0) | ~v2_pre_topc(sK0)) ) | (~spl10_5 | ~spl10_6)),
% 1.96/0.63    inference(subsumption_resolution,[],[f170,f156])).
% 1.96/0.63  fof(f170,plain,(
% 1.96/0.63    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK0) | ~v2_pre_topc(sK0)) ) | ~spl10_5),
% 1.96/0.63    inference(resolution,[],[f151,f90])).
% 1.96/0.63  fof(f90,plain,(
% 1.96/0.63    ( ! [X0,X1] : (~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 1.96/0.63    inference(cnf_transformation,[],[f46])).
% 1.96/0.63  fof(f46,plain,(
% 1.96/0.63    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.96/0.63    inference(flattening,[],[f45])).
% 1.96/0.63  fof(f45,plain,(
% 1.96/0.63    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.96/0.63    inference(ennf_transformation,[],[f27])).
% 1.96/0.63  fof(f27,axiom,(
% 1.96/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).
% 1.96/0.63  fof(f230,plain,(
% 1.96/0.63    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0) | spl10_14),
% 1.96/0.63    inference(avatar_component_clause,[],[f228])).
% 1.96/0.63  fof(f231,plain,(
% 1.96/0.63    ~spl10_14 | spl10_12),
% 1.96/0.63    inference(avatar_split_clause,[],[f225,f216,f228])).
% 1.96/0.63  fof(f216,plain,(
% 1.96/0.63    spl10_12 <=> sP3(sK2,sK1,sK0)),
% 1.96/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 1.96/0.63  fof(f225,plain,(
% 1.96/0.63    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0) | spl10_12),
% 1.96/0.63    inference(resolution,[],[f218,f79])).
% 1.96/0.63  fof(f79,plain,(
% 1.96/0.63    ( ! [X2,X0,X1] : (sP3(X2,X1,X0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)) )),
% 1.96/0.63    inference(cnf_transformation,[],[f37])).
% 1.96/0.63  fof(f37,plain,(
% 1.96/0.63    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.96/0.63    inference(flattening,[],[f36])).
% 1.96/0.63  fof(f36,plain,(
% 1.96/0.63    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.96/0.63    inference(ennf_transformation,[],[f24])).
% 1.96/0.63  fof(f24,axiom,(
% 1.96/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).
% 1.96/0.63  fof(f218,plain,(
% 1.96/0.63    ~sP3(sK2,sK1,sK0) | spl10_12),
% 1.96/0.63    inference(avatar_component_clause,[],[f216])).
% 1.96/0.63  fof(f223,plain,(
% 1.96/0.63    ~spl10_12 | spl10_13 | ~spl10_1 | ~spl10_3 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_11),
% 1.96/0.63    inference(avatar_split_clause,[],[f214,f198,f184,f179,f154,f139,f129,f220,f216])).
% 1.96/0.63  fof(f214,plain,(
% 1.96/0.63    k1_xboole_0 = k2_struct_0(sK1) | ~sP3(sK2,sK1,sK0) | (~spl10_1 | ~spl10_3 | ~spl10_6 | spl10_7 | ~spl10_8 | ~spl10_11)),
% 1.96/0.63    inference(subsumption_resolution,[],[f213,f181])).
% 1.96/0.63  fof(f213,plain,(
% 1.96/0.63    k1_xboole_0 = k2_struct_0(sK1) | ~sP3(sK2,sK1,sK0) | v5_pre_topc(sK2,sK0,sK1) | (~spl10_1 | ~spl10_3 | ~spl10_6 | ~spl10_8 | ~spl10_11)),
% 1.96/0.63    inference(subsumption_resolution,[],[f212,f200])).
% 1.96/0.63  fof(f212,plain,(
% 1.96/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1) | ~sP3(sK2,sK1,sK0) | v5_pre_topc(sK2,sK0,sK1) | (~spl10_1 | ~spl10_3 | ~spl10_6 | ~spl10_8)),
% 1.96/0.63    inference(subsumption_resolution,[],[f211,f141])).
% 1.96/0.63  fof(f211,plain,(
% 1.96/0.63    ~l1_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1) | ~sP3(sK2,sK1,sK0) | v5_pre_topc(sK2,sK0,sK1) | (~spl10_1 | ~spl10_6 | ~spl10_8)),
% 1.96/0.63    inference(subsumption_resolution,[],[f210,f156])).
% 1.96/0.63  fof(f210,plain,(
% 1.96/0.63    ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1) | ~sP3(sK2,sK1,sK0) | v5_pre_topc(sK2,sK0,sK1) | (~spl10_1 | ~spl10_8)),
% 1.96/0.63    inference(resolution,[],[f159,f186])).
% 1.96/0.63  fof(f159,plain,(
% 1.96/0.63    ( ! [X4,X3] : (~v1_funct_2(sK2,u1_struct_0(X4),u1_struct_0(X3)) | ~l1_pre_topc(X4) | ~l1_pre_topc(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3)))) | k1_xboole_0 = k2_struct_0(X3) | ~sP3(sK2,X3,X4) | v5_pre_topc(sK2,X4,X3)) ) | ~spl10_1),
% 1.96/0.63    inference(resolution,[],[f131,f83])).
% 1.96/0.63  fof(f83,plain,(
% 1.96/0.63    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k1_xboole_0 = k2_struct_0(X1) | ~sP3(X2,X1,X0) | v5_pre_topc(X2,X0,X1)) )),
% 1.96/0.63    inference(cnf_transformation,[],[f37])).
% 1.96/0.63  fof(f201,plain,(
% 1.96/0.63    spl10_11),
% 1.96/0.63    inference(avatar_split_clause,[],[f62,f198])).
% 1.96/0.63  fof(f62,plain,(
% 1.96/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.96/0.63    inference(cnf_transformation,[],[f32])).
% 1.96/0.63  fof(f32,plain,(
% 1.96/0.63    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0))),
% 1.96/0.63    inference(flattening,[],[f31])).
% 1.96/0.63  fof(f31,plain,(
% 1.96/0.63    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)))),
% 1.96/0.63    inference(ennf_transformation,[],[f30])).
% 1.96/0.63  fof(f30,negated_conjecture,(
% 1.96/0.63    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 1.96/0.63    inference(negated_conjecture,[],[f29])).
% 1.96/0.63  fof(f29,conjecture,(
% 1.96/0.63    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tex_2)).
% 1.96/0.63  fof(f187,plain,(
% 1.96/0.63    spl10_8),
% 1.96/0.63    inference(avatar_split_clause,[],[f61,f184])).
% 1.96/0.63  fof(f61,plain,(
% 1.96/0.63    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.96/0.63    inference(cnf_transformation,[],[f32])).
% 1.96/0.63  fof(f182,plain,(
% 1.96/0.63    ~spl10_7),
% 1.96/0.63    inference(avatar_split_clause,[],[f63,f179])).
% 1.96/0.63  fof(f63,plain,(
% 1.96/0.63    ~v5_pre_topc(sK2,sK0,sK1)),
% 1.96/0.63    inference(cnf_transformation,[],[f32])).
% 1.96/0.63  fof(f157,plain,(
% 1.96/0.63    spl10_6),
% 1.96/0.63    inference(avatar_split_clause,[],[f68,f154])).
% 1.96/0.63  fof(f68,plain,(
% 1.96/0.63    l1_pre_topc(sK0)),
% 1.96/0.63    inference(cnf_transformation,[],[f32])).
% 1.96/0.63  fof(f152,plain,(
% 1.96/0.63    spl10_5),
% 1.96/0.63    inference(avatar_split_clause,[],[f67,f149])).
% 1.96/0.63  fof(f67,plain,(
% 1.96/0.63    v1_tdlat_3(sK0)),
% 1.96/0.63    inference(cnf_transformation,[],[f32])).
% 1.96/0.63  fof(f147,plain,(
% 1.96/0.63    spl10_4),
% 1.96/0.63    inference(avatar_split_clause,[],[f66,f144])).
% 1.96/0.63  fof(f66,plain,(
% 1.96/0.63    v2_pre_topc(sK0)),
% 1.96/0.63    inference(cnf_transformation,[],[f32])).
% 1.96/0.63  fof(f142,plain,(
% 1.96/0.63    spl10_3),
% 1.96/0.63    inference(avatar_split_clause,[],[f65,f139])).
% 1.96/0.63  fof(f65,plain,(
% 1.96/0.63    l1_pre_topc(sK1)),
% 1.96/0.63    inference(cnf_transformation,[],[f32])).
% 1.96/0.63  fof(f137,plain,(
% 1.96/0.63    spl10_2),
% 1.96/0.63    inference(avatar_split_clause,[],[f64,f134])).
% 1.96/0.63  fof(f64,plain,(
% 1.96/0.63    v2_pre_topc(sK1)),
% 1.96/0.63    inference(cnf_transformation,[],[f32])).
% 1.96/0.63  fof(f132,plain,(
% 1.96/0.63    spl10_1),
% 1.96/0.63    inference(avatar_split_clause,[],[f60,f129])).
% 1.96/0.63  fof(f60,plain,(
% 1.96/0.63    v1_funct_1(sK2)),
% 1.96/0.63    inference(cnf_transformation,[],[f32])).
% 1.96/0.63  % SZS output end Proof for theBenchmark
% 1.96/0.63  % (14971)------------------------------
% 1.96/0.63  % (14971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.63  % (14971)Termination reason: Refutation
% 1.96/0.63  
% 1.96/0.63  % (14971)Memory used [KB]: 11513
% 1.96/0.63  % (14971)Time elapsed: 0.231 s
% 1.96/0.63  % (14971)------------------------------
% 1.96/0.63  % (14971)------------------------------
% 1.96/0.64  % (14940)Success in time 0.275 s
%------------------------------------------------------------------------------
