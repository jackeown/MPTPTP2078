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
% DateTime   : Thu Dec  3 13:11:51 EST 2020

% Result     : Theorem 2.60s
% Output     : Refutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 380 expanded)
%              Number of leaves         :   34 ( 143 expanded)
%              Depth                    :   16
%              Number of atoms          :  405 ( 969 expanded)
%              Number of equality atoms :  102 ( 290 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3813,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f124,f129,f163,f166,f275,f313,f638,f2572,f2691,f3714,f3731,f3802])).

fof(f3802,plain,
    ( ~ spl2_3
    | spl2_6
    | ~ spl2_35
    | ~ spl2_42 ),
    inference(avatar_contradiction_clause,[],[f3801])).

fof(f3801,plain,
    ( $false
    | ~ spl2_3
    | spl2_6
    | ~ spl2_35
    | ~ spl2_42 ),
    inference(subsumption_resolution,[],[f3796,f3717])).

fof(f3717,plain,
    ( k2_tops_1(sK0,sK1) != k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | spl2_6 ),
    inference(superposition,[],[f161,f229])).

fof(f229,plain,
    ( ! [X0] : k6_subset_1(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f128,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) ) ),
    inference(definition_unfolding,[],[f95,f78])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f128,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f161,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f3796,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_35
    | ~ spl2_42 ),
    inference(backward_demodulation,[],[f3033,f3793])).

fof(f3793,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_35
    | ~ spl2_42 ),
    inference(forward_demodulation,[],[f3768,f3791])).

fof(f3791,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_35
    | ~ spl2_42 ),
    inference(forward_demodulation,[],[f3769,f2690])).

fof(f2690,plain,
    ( k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f2688])).

fof(f2688,plain,
    ( spl2_35
  <=> k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f3769,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_42 ),
    inference(unit_resulting_resolution,[],[f3730,f195])).

fof(f195,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(resolution,[],[f108,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f87,f78])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f3730,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f3728])).

fof(f3728,plain,
    ( spl2_42
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f3768,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_42 ),
    inference(unit_resulting_resolution,[],[f3730,f189])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f88,f94])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f3033,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_35 ),
    inference(superposition,[],[f194,f2690])).

fof(f194,plain,(
    ! [X0,X1] : k3_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f76,f108])).

fof(f76,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f3731,plain,
    ( spl2_42
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f3715,f156,f126,f121,f3728])).

fof(f121,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f156,plain,
    ( spl2_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f3715,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f128,f158,f266])).

fof(f266,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | r1_tarski(k2_tops_1(sK0,X0),X0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f74,f123])).

fof(f123,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f158,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f156])).

fof(f3714,plain,
    ( spl2_5
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_31
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f3699,f2688,f2569,f310,f272,f126,f121,f156])).

fof(f272,plain,
    ( spl2_7
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f310,plain,
    ( spl2_9
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f2569,plain,
    ( spl2_31
  <=> k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f3699,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_31
    | ~ spl2_35 ),
    inference(backward_demodulation,[],[f274,f3695])).

fof(f3695,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_31
    | ~ spl2_35 ),
    inference(backward_demodulation,[],[f3046,f3693])).

fof(f3693,plain,
    ( sK1 = k5_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_31
    | ~ spl2_35 ),
    inference(backward_demodulation,[],[f3031,f3692])).

fof(f3692,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_31
    | ~ spl2_35 ),
    inference(forward_demodulation,[],[f3615,f2571])).

fof(f2571,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f2569])).

fof(f3615,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_35 ),
    inference(superposition,[],[f3294,f2690])).

fof(f3294,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(backward_demodulation,[],[f194,f3291])).

fof(f3291,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(forward_demodulation,[],[f3247,f3289])).

fof(f3289,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k3_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(forward_demodulation,[],[f3248,f107])).

fof(f107,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f85,f78,f78,f80])).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f85,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f3248,plain,(
    ! [X0,X1] : k6_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f464,f195])).

fof(f464,plain,(
    ! [X2,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(superposition,[],[f214,f103])).

fof(f103,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f79,f81,f80])).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f214,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(unit_resulting_resolution,[],[f102,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f97,f81,f78])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f102,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f75,f78])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f3247,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_subset_1(X0,k3_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(unit_resulting_resolution,[],[f464,f189])).

fof(f3031,plain,
    ( sK1 = k5_xboole_0(k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1))
    | ~ spl2_35 ),
    inference(superposition,[],[f186,f2690])).

fof(f186,plain,(
    ! [X0,X1] : k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f185,f103])).

fof(f185,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1)) ),
    inference(forward_demodulation,[],[f181,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f181,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1)) ),
    inference(superposition,[],[f104,f107])).

fof(f104,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f82,f81,f78])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f3046,plain,
    ( k2_pre_topc(sK0,sK1) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_35 ),
    inference(forward_demodulation,[],[f3045,f344])).

fof(f344,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f336,f300])).

fof(f300,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f123,f128,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f336,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f128,f312,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f99,f81])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f312,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f310])).

fof(f3045,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_35 ),
    inference(forward_demodulation,[],[f3025,f77])).

fof(f3025,plain,
    ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_35 ),
    inference(superposition,[],[f104,f2690])).

fof(f274,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f272])).

fof(f2691,plain,
    ( spl2_35
    | ~ spl2_3
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f649,f635,f126,f2688])).

fof(f635,plain,
    ( spl2_17
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f649,plain,
    ( k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_17 ),
    inference(superposition,[],[f637,f229])).

fof(f637,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f635])).

fof(f2572,plain,
    ( spl2_31
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f425,f160,f126,f2569])).

fof(f425,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f229,f162])).

fof(f162,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f160])).

fof(f638,plain,
    ( spl2_17
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f296,f126,f121,f635])).

fof(f296,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f123,f128,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f313,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f258,f126,f121,f310])).

fof(f258,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f123,f128,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f275,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f253,f126,f121,f116,f272])).

fof(f116,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f253,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f118,f123,f128,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f118,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f166,plain,
    ( ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f165,f160,f156])).

fof(f165,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f67,f162])).

fof(f67,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f58,f60,f59])).

fof(f59,plain,
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

fof(f60,plain,
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

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f163,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f66,f160,f156])).

fof(f66,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f129,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f65,f126])).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f61])).

fof(f124,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f64,f121])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f119,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f63,f116])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 15:34:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.45  % (23118)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.45  % (23131)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.45  % (23130)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.46  % (23116)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.46  % (23121)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.46  % (23120)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.47  % (23129)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.47  % (23122)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.47  % (23117)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.47  % (23126)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.47  % (23124)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.47  % (23123)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.48  % (23132)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.48  % (23128)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.48  % (23133)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.48  % (23119)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.49  % (23125)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.50  % (23127)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 2.60/0.70  % (23131)Refutation found. Thanks to Tanya!
% 2.60/0.70  % SZS status Theorem for theBenchmark
% 2.60/0.70  % SZS output start Proof for theBenchmark
% 2.60/0.70  fof(f3813,plain,(
% 2.60/0.70    $false),
% 2.60/0.70    inference(avatar_sat_refutation,[],[f119,f124,f129,f163,f166,f275,f313,f638,f2572,f2691,f3714,f3731,f3802])).
% 2.60/0.70  fof(f3802,plain,(
% 2.60/0.70    ~spl2_3 | spl2_6 | ~spl2_35 | ~spl2_42),
% 2.60/0.70    inference(avatar_contradiction_clause,[],[f3801])).
% 2.60/0.70  fof(f3801,plain,(
% 2.60/0.70    $false | (~spl2_3 | spl2_6 | ~spl2_35 | ~spl2_42)),
% 2.60/0.70    inference(subsumption_resolution,[],[f3796,f3717])).
% 2.60/0.70  fof(f3717,plain,(
% 2.60/0.70    k2_tops_1(sK0,sK1) != k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | spl2_6)),
% 2.60/0.70    inference(superposition,[],[f161,f229])).
% 2.60/0.70  fof(f229,plain,(
% 2.60/0.70    ( ! [X0] : (k6_subset_1(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_3),
% 2.60/0.70    inference(unit_resulting_resolution,[],[f128,f110])).
% 2.60/0.70  fof(f110,plain,(
% 2.60/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)) )),
% 2.60/0.70    inference(definition_unfolding,[],[f95,f78])).
% 2.60/0.70  fof(f78,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.60/0.70    inference(cnf_transformation,[],[f21])).
% 2.60/0.70  fof(f21,axiom,(
% 2.60/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.60/0.70  fof(f95,plain,(
% 2.60/0.70    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.60/0.70    inference(cnf_transformation,[],[f50])).
% 2.60/0.70  fof(f50,plain,(
% 2.60/0.70    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.60/0.70    inference(ennf_transformation,[],[f22])).
% 2.60/0.70  fof(f22,axiom,(
% 2.60/0.70    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.60/0.70  fof(f128,plain,(
% 2.60/0.70    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 2.60/0.70    inference(avatar_component_clause,[],[f126])).
% 2.60/0.70  fof(f126,plain,(
% 2.60/0.70    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.60/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.60/0.70  fof(f161,plain,(
% 2.60/0.70    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_6),
% 2.60/0.70    inference(avatar_component_clause,[],[f160])).
% 2.60/0.70  fof(f160,plain,(
% 2.60/0.70    spl2_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.60/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 2.60/0.70  fof(f3796,plain,(
% 2.60/0.70    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_35 | ~spl2_42)),
% 2.60/0.70    inference(backward_demodulation,[],[f3033,f3793])).
% 2.60/0.70  fof(f3793,plain,(
% 2.60/0.70    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_35 | ~spl2_42)),
% 2.60/0.70    inference(forward_demodulation,[],[f3768,f3791])).
% 2.60/0.70  fof(f3791,plain,(
% 2.60/0.70    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_35 | ~spl2_42)),
% 2.60/0.70    inference(forward_demodulation,[],[f3769,f2690])).
% 2.60/0.70  fof(f2690,plain,(
% 2.60/0.70    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_35),
% 2.60/0.70    inference(avatar_component_clause,[],[f2688])).
% 2.60/0.70  fof(f2688,plain,(
% 2.60/0.70    spl2_35 <=> k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 2.60/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 2.60/0.70  fof(f3769,plain,(
% 2.60/0.70    k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_42),
% 2.60/0.70    inference(unit_resulting_resolution,[],[f3730,f195])).
% 2.60/0.70  fof(f195,plain,(
% 2.60/0.70    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.60/0.70    inference(resolution,[],[f108,f94])).
% 2.60/0.70  fof(f94,plain,(
% 2.60/0.70    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.60/0.70    inference(cnf_transformation,[],[f62])).
% 2.60/0.70  fof(f62,plain,(
% 2.60/0.70    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.60/0.70    inference(nnf_transformation,[],[f25])).
% 2.60/0.70  fof(f25,axiom,(
% 2.60/0.70    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.60/0.70  fof(f108,plain,(
% 2.60/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.60/0.70    inference(definition_unfolding,[],[f87,f78])).
% 2.60/0.70  fof(f87,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.60/0.70    inference(cnf_transformation,[],[f42])).
% 2.60/0.70  fof(f42,plain,(
% 2.60/0.70    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.60/0.70    inference(ennf_transformation,[],[f16])).
% 2.60/0.70  fof(f16,axiom,(
% 2.60/0.70    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.60/0.70  fof(f3730,plain,(
% 2.60/0.70    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_42),
% 2.60/0.70    inference(avatar_component_clause,[],[f3728])).
% 2.60/0.70  fof(f3728,plain,(
% 2.60/0.70    spl2_42 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.60/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 2.60/0.70  fof(f3768,plain,(
% 2.60/0.70    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_42),
% 2.60/0.70    inference(unit_resulting_resolution,[],[f3730,f189])).
% 2.60/0.70  fof(f189,plain,(
% 2.60/0.70    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.60/0.70    inference(resolution,[],[f88,f94])).
% 2.60/0.70  fof(f88,plain,(
% 2.60/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.60/0.70    inference(cnf_transformation,[],[f43])).
% 2.60/0.70  fof(f43,plain,(
% 2.60/0.70    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.60/0.70    inference(ennf_transformation,[],[f19])).
% 2.60/0.70  fof(f19,axiom,(
% 2.60/0.70    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.60/0.70  fof(f3033,plain,(
% 2.60/0.70    k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_35),
% 2.60/0.70    inference(superposition,[],[f194,f2690])).
% 2.60/0.70  fof(f194,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k3_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 2.60/0.70    inference(unit_resulting_resolution,[],[f76,f108])).
% 2.60/0.70  fof(f76,plain,(
% 2.60/0.70    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.60/0.70    inference(cnf_transformation,[],[f18])).
% 2.60/0.70  fof(f18,axiom,(
% 2.60/0.70    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 2.60/0.70  fof(f3731,plain,(
% 2.60/0.70    spl2_42 | ~spl2_2 | ~spl2_3 | ~spl2_5),
% 2.60/0.70    inference(avatar_split_clause,[],[f3715,f156,f126,f121,f3728])).
% 2.60/0.70  fof(f121,plain,(
% 2.60/0.70    spl2_2 <=> l1_pre_topc(sK0)),
% 2.60/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.60/0.70  fof(f156,plain,(
% 2.60/0.70    spl2_5 <=> v4_pre_topc(sK1,sK0)),
% 2.60/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.60/0.70  fof(f3715,plain,(
% 2.60/0.70    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_3 | ~spl2_5)),
% 2.60/0.70    inference(unit_resulting_resolution,[],[f128,f158,f266])).
% 2.60/0.70  fof(f266,plain,(
% 2.60/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | r1_tarski(k2_tops_1(sK0,X0),X0)) ) | ~spl2_2),
% 2.60/0.70    inference(resolution,[],[f74,f123])).
% 2.60/0.70  fof(f123,plain,(
% 2.60/0.70    l1_pre_topc(sK0) | ~spl2_2),
% 2.60/0.70    inference(avatar_component_clause,[],[f121])).
% 2.60/0.70  fof(f74,plain,(
% 2.60/0.70    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 2.60/0.70    inference(cnf_transformation,[],[f40])).
% 2.60/0.70  fof(f40,plain,(
% 2.60/0.70    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.60/0.70    inference(flattening,[],[f39])).
% 2.60/0.70  fof(f39,plain,(
% 2.60/0.70    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.60/0.70    inference(ennf_transformation,[],[f30])).
% 2.60/0.70  fof(f30,axiom,(
% 2.60/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 2.60/0.70  fof(f158,plain,(
% 2.60/0.70    v4_pre_topc(sK1,sK0) | ~spl2_5),
% 2.60/0.70    inference(avatar_component_clause,[],[f156])).
% 2.60/0.70  fof(f3714,plain,(
% 2.60/0.70    spl2_5 | ~spl2_2 | ~spl2_3 | ~spl2_7 | ~spl2_9 | ~spl2_31 | ~spl2_35),
% 2.60/0.70    inference(avatar_split_clause,[],[f3699,f2688,f2569,f310,f272,f126,f121,f156])).
% 2.60/0.70  fof(f272,plain,(
% 2.60/0.70    spl2_7 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 2.60/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 2.60/0.70  fof(f310,plain,(
% 2.60/0.70    spl2_9 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.60/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 2.60/0.70  fof(f2569,plain,(
% 2.60/0.70    spl2_31 <=> k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 2.60/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 2.60/0.70  fof(f3699,plain,(
% 2.60/0.70    v4_pre_topc(sK1,sK0) | (~spl2_2 | ~spl2_3 | ~spl2_7 | ~spl2_9 | ~spl2_31 | ~spl2_35)),
% 2.60/0.70    inference(backward_demodulation,[],[f274,f3695])).
% 2.60/0.70  fof(f3695,plain,(
% 2.60/0.70    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_3 | ~spl2_9 | ~spl2_31 | ~spl2_35)),
% 2.60/0.70    inference(backward_demodulation,[],[f3046,f3693])).
% 2.60/0.70  fof(f3693,plain,(
% 2.60/0.70    sK1 = k5_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_31 | ~spl2_35)),
% 2.60/0.70    inference(backward_demodulation,[],[f3031,f3692])).
% 2.60/0.70  fof(f3692,plain,(
% 2.60/0.70    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_31 | ~spl2_35)),
% 2.60/0.70    inference(forward_demodulation,[],[f3615,f2571])).
% 2.60/0.70  fof(f2571,plain,(
% 2.60/0.70    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_31),
% 2.60/0.70    inference(avatar_component_clause,[],[f2569])).
% 2.60/0.70  fof(f3615,plain,(
% 2.60/0.70    k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_35),
% 2.60/0.70    inference(superposition,[],[f3294,f2690])).
% 2.60/0.70  fof(f3294,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 2.60/0.70    inference(backward_demodulation,[],[f194,f3291])).
% 2.60/0.70  fof(f3291,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_subset_1(X0,k6_subset_1(X0,X1))) )),
% 2.60/0.70    inference(forward_demodulation,[],[f3247,f3289])).
% 2.60/0.70  fof(f3289,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k3_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.60/0.70    inference(forward_demodulation,[],[f3248,f107])).
% 2.60/0.70  fof(f107,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.60/0.70    inference(definition_unfolding,[],[f85,f78,f78,f80])).
% 2.60/0.70  fof(f80,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.60/0.70    inference(cnf_transformation,[],[f24])).
% 2.60/0.70  fof(f24,axiom,(
% 2.60/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.60/0.70  fof(f85,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.60/0.70    inference(cnf_transformation,[],[f10])).
% 2.60/0.70  fof(f10,axiom,(
% 2.60/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.60/0.70  fof(f3248,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k6_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.60/0.70    inference(unit_resulting_resolution,[],[f464,f195])).
% 2.60/0.70  fof(f464,plain,(
% 2.60/0.70    ( ! [X2,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)) )),
% 2.60/0.70    inference(superposition,[],[f214,f103])).
% 2.60/0.70  fof(f103,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0) )),
% 2.60/0.70    inference(definition_unfolding,[],[f79,f81,f80])).
% 2.60/0.70  fof(f81,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.60/0.70    inference(cnf_transformation,[],[f14])).
% 2.60/0.70  fof(f14,axiom,(
% 2.60/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.60/0.70  fof(f79,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.60/0.70    inference(cnf_transformation,[],[f4])).
% 2.60/0.70  fof(f4,axiom,(
% 2.60/0.70    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.60/0.70  fof(f214,plain,(
% 2.60/0.70    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) )),
% 2.60/0.70    inference(unit_resulting_resolution,[],[f102,f112])).
% 2.60/0.70  fof(f112,plain,(
% 2.60/0.70    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.60/0.70    inference(definition_unfolding,[],[f97,f81,f78])).
% 2.60/0.70  fof(f97,plain,(
% 2.60/0.70    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.60/0.70    inference(cnf_transformation,[],[f52])).
% 2.60/0.70  fof(f52,plain,(
% 2.60/0.70    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.60/0.70    inference(ennf_transformation,[],[f9])).
% 2.60/0.70  fof(f9,axiom,(
% 2.60/0.70    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.60/0.70  fof(f102,plain,(
% 2.60/0.70    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 2.60/0.70    inference(definition_unfolding,[],[f75,f78])).
% 2.60/0.70  fof(f75,plain,(
% 2.60/0.70    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.60/0.70    inference(cnf_transformation,[],[f5])).
% 2.60/0.70  fof(f5,axiom,(
% 2.60/0.70    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.60/0.70  fof(f3247,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_subset_1(X0,k3_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 2.60/0.70    inference(unit_resulting_resolution,[],[f464,f189])).
% 2.60/0.70  fof(f3031,plain,(
% 2.60/0.70    sK1 = k5_xboole_0(k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1)) | ~spl2_35),
% 2.60/0.70    inference(superposition,[],[f186,f2690])).
% 2.60/0.70  fof(f186,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1)) = X0) )),
% 2.60/0.70    inference(forward_demodulation,[],[f185,f103])).
% 2.60/0.70  fof(f185,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1))) )),
% 2.60/0.70    inference(forward_demodulation,[],[f181,f77])).
% 2.60/0.70  fof(f77,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.60/0.70    inference(cnf_transformation,[],[f13])).
% 2.60/0.70  fof(f13,axiom,(
% 2.60/0.70    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.60/0.70  fof(f181,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1))) )),
% 2.60/0.70    inference(superposition,[],[f104,f107])).
% 2.60/0.70  fof(f104,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 2.60/0.70    inference(definition_unfolding,[],[f82,f81,f78])).
% 2.60/0.70  fof(f82,plain,(
% 2.60/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.60/0.70    inference(cnf_transformation,[],[f12])).
% 2.60/0.70  fof(f12,axiom,(
% 2.60/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.60/0.70  fof(f3046,plain,(
% 2.60/0.70    k2_pre_topc(sK0,sK1) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_9 | ~spl2_35)),
% 2.60/0.70    inference(forward_demodulation,[],[f3045,f344])).
% 2.60/0.70  fof(f344,plain,(
% 2.60/0.70    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_2 | ~spl2_3 | ~spl2_9)),
% 2.60/0.70    inference(forward_demodulation,[],[f336,f300])).
% 2.60/0.70  fof(f300,plain,(
% 2.60/0.70    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 2.60/0.70    inference(unit_resulting_resolution,[],[f123,f128,f73])).
% 2.60/0.70  fof(f73,plain,(
% 2.60/0.70    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.60/0.70    inference(cnf_transformation,[],[f38])).
% 2.60/0.70  fof(f38,plain,(
% 2.60/0.70    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.60/0.70    inference(ennf_transformation,[],[f29])).
% 2.60/0.70  fof(f29,axiom,(
% 2.60/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.60/0.70  fof(f336,plain,(
% 2.60/0.70    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_9)),
% 2.60/0.70    inference(unit_resulting_resolution,[],[f128,f312,f113])).
% 2.60/0.70  fof(f113,plain,(
% 2.60/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.60/0.70    inference(definition_unfolding,[],[f99,f81])).
% 2.60/0.70  fof(f99,plain,(
% 2.60/0.70    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.60/0.70    inference(cnf_transformation,[],[f56])).
% 2.60/0.70  fof(f56,plain,(
% 2.60/0.70    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.60/0.70    inference(flattening,[],[f55])).
% 2.60/0.70  fof(f55,plain,(
% 2.60/0.70    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.60/0.70    inference(ennf_transformation,[],[f20])).
% 2.60/0.70  fof(f20,axiom,(
% 2.60/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.60/0.70  fof(f312,plain,(
% 2.60/0.70    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_9),
% 2.60/0.70    inference(avatar_component_clause,[],[f310])).
% 2.60/0.70  fof(f3045,plain,(
% 2.60/0.70    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_35),
% 2.60/0.70    inference(forward_demodulation,[],[f3025,f77])).
% 2.60/0.70  fof(f3025,plain,(
% 2.60/0.70    k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_35),
% 2.60/0.70    inference(superposition,[],[f104,f2690])).
% 2.60/0.70  fof(f274,plain,(
% 2.60/0.70    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~spl2_7),
% 2.60/0.70    inference(avatar_component_clause,[],[f272])).
% 2.60/0.70  fof(f2691,plain,(
% 2.60/0.70    spl2_35 | ~spl2_3 | ~spl2_17),
% 2.60/0.70    inference(avatar_split_clause,[],[f649,f635,f126,f2688])).
% 2.60/0.70  fof(f635,plain,(
% 2.60/0.70    spl2_17 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.60/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 2.60/0.70  fof(f649,plain,(
% 2.60/0.70    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_17)),
% 2.60/0.70    inference(superposition,[],[f637,f229])).
% 2.60/0.70  fof(f637,plain,(
% 2.60/0.70    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_17),
% 2.60/0.70    inference(avatar_component_clause,[],[f635])).
% 2.60/0.70  fof(f2572,plain,(
% 2.60/0.70    spl2_31 | ~spl2_3 | ~spl2_6),
% 2.60/0.70    inference(avatar_split_clause,[],[f425,f160,f126,f2569])).
% 2.60/0.70  fof(f425,plain,(
% 2.60/0.70    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6)),
% 2.60/0.70    inference(superposition,[],[f229,f162])).
% 2.60/0.70  fof(f162,plain,(
% 2.60/0.70    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 2.60/0.70    inference(avatar_component_clause,[],[f160])).
% 2.60/0.70  fof(f638,plain,(
% 2.60/0.70    spl2_17 | ~spl2_2 | ~spl2_3),
% 2.60/0.70    inference(avatar_split_clause,[],[f296,f126,f121,f635])).
% 2.60/0.70  fof(f296,plain,(
% 2.60/0.70    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 2.60/0.70    inference(unit_resulting_resolution,[],[f123,f128,f72])).
% 2.60/0.70  fof(f72,plain,(
% 2.60/0.70    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.60/0.70    inference(cnf_transformation,[],[f37])).
% 2.60/0.70  fof(f37,plain,(
% 2.60/0.70    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.60/0.70    inference(ennf_transformation,[],[f31])).
% 2.60/0.70  fof(f31,axiom,(
% 2.60/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.60/0.70  fof(f313,plain,(
% 2.60/0.70    spl2_9 | ~spl2_2 | ~spl2_3),
% 2.60/0.70    inference(avatar_split_clause,[],[f258,f126,f121,f310])).
% 2.60/0.70  fof(f258,plain,(
% 2.60/0.70    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 2.60/0.70    inference(unit_resulting_resolution,[],[f123,f128,f92])).
% 2.60/0.70  fof(f92,plain,(
% 2.60/0.70    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.60/0.70    inference(cnf_transformation,[],[f49])).
% 2.60/0.70  fof(f49,plain,(
% 2.60/0.70    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.60/0.70    inference(flattening,[],[f48])).
% 2.60/0.70  fof(f48,plain,(
% 2.60/0.70    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.60/0.70    inference(ennf_transformation,[],[f26])).
% 2.60/0.70  fof(f26,axiom,(
% 2.60/0.70    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.60/0.70  fof(f275,plain,(
% 2.60/0.70    spl2_7 | ~spl2_1 | ~spl2_2 | ~spl2_3),
% 2.60/0.70    inference(avatar_split_clause,[],[f253,f126,f121,f116,f272])).
% 2.60/0.70  fof(f116,plain,(
% 2.60/0.70    spl2_1 <=> v2_pre_topc(sK0)),
% 2.60/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.60/0.70  fof(f253,plain,(
% 2.60/0.70    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 2.60/0.70    inference(unit_resulting_resolution,[],[f118,f123,f128,f91])).
% 2.60/0.70  fof(f91,plain,(
% 2.60/0.70    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(k2_pre_topc(X0,X1),X0)) )),
% 2.60/0.70    inference(cnf_transformation,[],[f47])).
% 2.60/0.70  fof(f47,plain,(
% 2.60/0.70    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.60/0.70    inference(flattening,[],[f46])).
% 2.60/0.70  fof(f46,plain,(
% 2.60/0.70    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.60/0.70    inference(ennf_transformation,[],[f27])).
% 2.60/0.70  fof(f27,axiom,(
% 2.60/0.70    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 2.60/0.70  fof(f118,plain,(
% 2.60/0.70    v2_pre_topc(sK0) | ~spl2_1),
% 2.60/0.70    inference(avatar_component_clause,[],[f116])).
% 2.60/0.70  fof(f166,plain,(
% 2.60/0.70    ~spl2_5 | ~spl2_6),
% 2.60/0.70    inference(avatar_split_clause,[],[f165,f160,f156])).
% 2.60/0.70  fof(f165,plain,(
% 2.60/0.70    ~v4_pre_topc(sK1,sK0) | ~spl2_6),
% 2.60/0.70    inference(trivial_inequality_removal,[],[f164])).
% 2.60/0.70  fof(f164,plain,(
% 2.60/0.70    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0) | ~spl2_6),
% 2.60/0.70    inference(backward_demodulation,[],[f67,f162])).
% 2.60/0.70  fof(f67,plain,(
% 2.60/0.70    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.60/0.70    inference(cnf_transformation,[],[f61])).
% 2.60/0.70  fof(f61,plain,(
% 2.60/0.70    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.60/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f58,f60,f59])).
% 2.60/0.70  fof(f59,plain,(
% 2.60/0.70    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.60/0.70    introduced(choice_axiom,[])).
% 2.60/0.70  fof(f60,plain,(
% 2.60/0.70    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.60/0.70    introduced(choice_axiom,[])).
% 2.60/0.70  fof(f58,plain,(
% 2.60/0.70    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.60/0.70    inference(flattening,[],[f57])).
% 2.60/0.70  fof(f57,plain,(
% 2.60/0.70    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.60/0.70    inference(nnf_transformation,[],[f35])).
% 2.60/0.70  fof(f35,plain,(
% 2.60/0.70    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.60/0.70    inference(flattening,[],[f34])).
% 2.60/0.70  fof(f34,plain,(
% 2.60/0.70    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.60/0.70    inference(ennf_transformation,[],[f33])).
% 2.60/0.70  fof(f33,negated_conjecture,(
% 2.60/0.70    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.60/0.70    inference(negated_conjecture,[],[f32])).
% 2.60/0.70  fof(f32,conjecture,(
% 2.60/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.60/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 2.60/0.70  fof(f163,plain,(
% 2.60/0.70    spl2_5 | spl2_6),
% 2.60/0.70    inference(avatar_split_clause,[],[f66,f160,f156])).
% 2.60/0.70  fof(f66,plain,(
% 2.60/0.70    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.60/0.70    inference(cnf_transformation,[],[f61])).
% 2.60/0.70  fof(f129,plain,(
% 2.60/0.70    spl2_3),
% 2.60/0.70    inference(avatar_split_clause,[],[f65,f126])).
% 2.60/0.70  fof(f65,plain,(
% 2.60/0.70    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.60/0.70    inference(cnf_transformation,[],[f61])).
% 2.60/0.70  fof(f124,plain,(
% 2.60/0.70    spl2_2),
% 2.60/0.70    inference(avatar_split_clause,[],[f64,f121])).
% 2.60/0.70  fof(f64,plain,(
% 2.60/0.70    l1_pre_topc(sK0)),
% 2.60/0.70    inference(cnf_transformation,[],[f61])).
% 2.60/0.70  fof(f119,plain,(
% 2.60/0.70    spl2_1),
% 2.60/0.70    inference(avatar_split_clause,[],[f63,f116])).
% 2.60/0.70  fof(f63,plain,(
% 2.60/0.70    v2_pre_topc(sK0)),
% 2.60/0.70    inference(cnf_transformation,[],[f61])).
% 2.60/0.70  % SZS output end Proof for theBenchmark
% 2.60/0.70  % (23131)------------------------------
% 2.60/0.70  % (23131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.60/0.70  % (23131)Termination reason: Refutation
% 2.60/0.70  
% 2.60/0.70  % (23131)Memory used [KB]: 13688
% 2.60/0.70  % (23131)Time elapsed: 0.258 s
% 2.60/0.70  % (23131)------------------------------
% 2.60/0.70  % (23131)------------------------------
% 2.60/0.72  % (23115)Success in time 0.378 s
%------------------------------------------------------------------------------
