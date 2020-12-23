%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:51 EST 2020

% Result     : Theorem 3.17s
% Output     : Refutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 432 expanded)
%              Number of leaves         :   32 ( 152 expanded)
%              Depth                    :   17
%              Number of atoms          :  416 (1089 expanded)
%              Number of equality atoms :  117 ( 348 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4546,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f125,f130,f164,f167,f318,f648,f2740,f2867,f3898,f4490,f4542])).

fof(f4542,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_5
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_37 ),
    inference(avatar_contradiction_clause,[],[f4541])).

fof(f4541,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_5
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f4540,f277])).

fof(f277,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f124,f119,f158,f129,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

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
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
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

fof(f129,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f158,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl2_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f119,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f124,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f4540,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_37 ),
    inference(backward_demodulation,[],[f4534,f4538])).

fof(f4538,plain,
    ( sK1 = k5_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_37 ),
    inference(backward_demodulation,[],[f3855,f4535])).

fof(f4535,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_37 ),
    inference(forward_demodulation,[],[f3195,f435])).

fof(f435,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f230,f163])).

fof(f163,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f230,plain,
    ( ! [X0] : k6_subset_1(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f129,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) ) ),
    inference(definition_unfolding,[],[f96,f79])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f96,plain,(
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

fof(f3195,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(superposition,[],[f195,f2866])).

fof(f2866,plain,
    ( k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f2864])).

fof(f2864,plain,
    ( spl2_37
  <=> k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f195,plain,(
    ! [X0,X1] : k3_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f77,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f88,f79])).

fof(f88,plain,(
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

fof(f77,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f3855,plain,
    ( sK1 = k5_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(backward_demodulation,[],[f3193,f3854])).

fof(f3854,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_37 ),
    inference(forward_demodulation,[],[f3782,f3195])).

fof(f3782,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_37 ),
    inference(superposition,[],[f3456,f2866])).

fof(f3456,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(backward_demodulation,[],[f195,f3453])).

fof(f3453,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(forward_demodulation,[],[f3409,f3451])).

fof(f3451,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k3_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(forward_demodulation,[],[f3410,f108])).

fof(f108,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f86,f79,f79,f81])).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f86,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f3410,plain,(
    ! [X0,X1] : k6_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f474,f196])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(resolution,[],[f109,f95])).

fof(f95,plain,(
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

fof(f474,plain,(
    ! [X2,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(superposition,[],[f215,f104])).

fof(f104,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f80,f82,f81])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f215,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(unit_resulting_resolution,[],[f103,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f98,f82,f79])).

fof(f98,plain,(
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

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f76,f79])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f3409,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_subset_1(X0,k3_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(unit_resulting_resolution,[],[f474,f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f89,f95])).

fof(f89,plain,(
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

fof(f3193,plain,
    ( sK1 = k5_xboole_0(k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(superposition,[],[f187,f2866])).

fof(f187,plain,(
    ! [X0,X1] : k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f186,f104])).

fof(f186,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1)) ),
    inference(forward_demodulation,[],[f182,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f182,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1)) ),
    inference(superposition,[],[f105,f108])).

fof(f105,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f83,f82,f79])).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f4534,plain,
    ( k2_pre_topc(sK0,sK1) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_37 ),
    inference(forward_demodulation,[],[f3207,f354])).

fof(f354,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f346,f304])).

fof(f304,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f124,f129,f73])).

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
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f346,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f129,f317,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f100,f82])).

fof(f100,plain,(
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

fof(f317,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl2_9
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f3207,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(forward_demodulation,[],[f3187,f78])).

fof(f3187,plain,
    ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(superposition,[],[f105,f2866])).

fof(f4490,plain,
    ( ~ spl2_3
    | spl2_6
    | ~ spl2_37
    | ~ spl2_47 ),
    inference(avatar_contradiction_clause,[],[f4489])).

fof(f4489,plain,
    ( $false
    | ~ spl2_3
    | spl2_6
    | ~ spl2_37
    | ~ spl2_47 ),
    inference(subsumption_resolution,[],[f2730,f4478])).

fof(f4478,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_37
    | ~ spl2_47 ),
    inference(backward_demodulation,[],[f3195,f4475])).

fof(f4475,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_37
    | ~ spl2_47 ),
    inference(forward_demodulation,[],[f4450,f4473])).

fof(f4473,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_37
    | ~ spl2_47 ),
    inference(forward_demodulation,[],[f4451,f2866])).

fof(f4451,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_47 ),
    inference(unit_resulting_resolution,[],[f3897,f196])).

fof(f3897,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f3895])).

fof(f3895,plain,
    ( spl2_47
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f4450,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_47 ),
    inference(unit_resulting_resolution,[],[f3897,f190])).

fof(f2730,plain,
    ( k2_tops_1(sK0,sK1) != k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | spl2_6 ),
    inference(superposition,[],[f162,f230])).

fof(f162,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f161])).

fof(f3898,plain,
    ( spl2_47
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f2746,f2737,f3895])).

fof(f2737,plain,
    ( spl2_34
  <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f2746,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_34 ),
    inference(superposition,[],[f215,f2739])).

fof(f2739,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f2737])).

fof(f2867,plain,
    ( spl2_37
    | ~ spl2_3
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f654,f645,f127,f2864])).

fof(f645,plain,
    ( spl2_18
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f654,plain,
    ( k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_18 ),
    inference(superposition,[],[f647,f230])).

fof(f647,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f645])).

fof(f2740,plain,
    ( spl2_34
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f2726,f315,f157,f127,f122,f2737])).

fof(f2726,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f354,f2723])).

fof(f2723,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f765,f159])).

fof(f159,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f157])).

fof(f765,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f267,f129])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_2 ),
    inference(resolution,[],[f74,f124])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f648,plain,
    ( spl2_18
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f300,f127,f122,f645])).

fof(f300,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f124,f129,f72])).

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

fof(f318,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f259,f127,f122,f315])).

fof(f259,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f124,f129,f93])).

fof(f93,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f167,plain,
    ( ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f166,f161,f157])).

fof(f166,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f165])).

fof(f165,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f67,f163])).

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

fof(f164,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f66,f161,f157])).

fof(f66,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f130,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f65,f127])).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f61])).

fof(f125,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f64,f122])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f120,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f63,f117])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:54:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (27208)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.45  % (27196)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (27204)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (27198)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (27205)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (27209)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (27202)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (27206)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (27197)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (27201)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.51  % (27213)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (27199)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (27200)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (27211)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (27203)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.52  % (27210)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.52  % (27207)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.52  % (27212)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 3.17/0.78  % (27211)Refutation found. Thanks to Tanya!
% 3.17/0.78  % SZS status Theorem for theBenchmark
% 3.17/0.78  % SZS output start Proof for theBenchmark
% 3.17/0.78  fof(f4546,plain,(
% 3.17/0.78    $false),
% 3.17/0.78    inference(avatar_sat_refutation,[],[f120,f125,f130,f164,f167,f318,f648,f2740,f2867,f3898,f4490,f4542])).
% 3.17/0.78  fof(f4542,plain,(
% 3.17/0.78    ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_5 | ~spl2_6 | ~spl2_9 | ~spl2_37),
% 3.17/0.78    inference(avatar_contradiction_clause,[],[f4541])).
% 3.17/0.78  fof(f4541,plain,(
% 3.17/0.78    $false | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_5 | ~spl2_6 | ~spl2_9 | ~spl2_37)),
% 3.17/0.78    inference(subsumption_resolution,[],[f4540,f277])).
% 3.17/0.78  fof(f277,plain,(
% 3.17/0.78    sK1 != k2_pre_topc(sK0,sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_5)),
% 3.17/0.78    inference(unit_resulting_resolution,[],[f124,f119,f158,f129,f75])).
% 3.17/0.78  fof(f75,plain,(
% 3.17/0.78    ( ! [X0,X1] : (~v2_pre_topc(X0) | k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.17/0.78    inference(cnf_transformation,[],[f40])).
% 3.17/0.78  fof(f40,plain,(
% 3.17/0.78    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.17/0.78    inference(flattening,[],[f39])).
% 3.17/0.78  fof(f39,plain,(
% 3.17/0.78    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.17/0.78    inference(ennf_transformation,[],[f26])).
% 3.17/0.78  fof(f26,axiom,(
% 3.17/0.78    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 3.17/0.78  fof(f129,plain,(
% 3.17/0.78    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 3.17/0.78    inference(avatar_component_clause,[],[f127])).
% 3.17/0.78  fof(f127,plain,(
% 3.17/0.78    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.17/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 3.17/0.78  fof(f158,plain,(
% 3.17/0.78    ~v4_pre_topc(sK1,sK0) | spl2_5),
% 3.17/0.78    inference(avatar_component_clause,[],[f157])).
% 3.17/0.78  fof(f157,plain,(
% 3.17/0.78    spl2_5 <=> v4_pre_topc(sK1,sK0)),
% 3.17/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 3.17/0.78  fof(f119,plain,(
% 3.17/0.78    v2_pre_topc(sK0) | ~spl2_1),
% 3.17/0.78    inference(avatar_component_clause,[],[f117])).
% 3.17/0.78  fof(f117,plain,(
% 3.17/0.78    spl2_1 <=> v2_pre_topc(sK0)),
% 3.17/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.17/0.78  fof(f124,plain,(
% 3.17/0.78    l1_pre_topc(sK0) | ~spl2_2),
% 3.17/0.78    inference(avatar_component_clause,[],[f122])).
% 3.17/0.78  fof(f122,plain,(
% 3.17/0.78    spl2_2 <=> l1_pre_topc(sK0)),
% 3.17/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.17/0.78  fof(f4540,plain,(
% 3.17/0.78    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_9 | ~spl2_37)),
% 3.17/0.78    inference(backward_demodulation,[],[f4534,f4538])).
% 3.17/0.78  fof(f4538,plain,(
% 3.17/0.78    sK1 = k5_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6 | ~spl2_37)),
% 3.17/0.78    inference(backward_demodulation,[],[f3855,f4535])).
% 3.17/0.78  fof(f4535,plain,(
% 3.17/0.78    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6 | ~spl2_37)),
% 3.17/0.78    inference(forward_demodulation,[],[f3195,f435])).
% 3.17/0.78  fof(f435,plain,(
% 3.17/0.78    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6)),
% 3.17/0.78    inference(superposition,[],[f230,f163])).
% 3.17/0.78  fof(f163,plain,(
% 3.17/0.78    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 3.17/0.78    inference(avatar_component_clause,[],[f161])).
% 3.17/0.78  fof(f161,plain,(
% 3.17/0.78    spl2_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 3.17/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 3.17/0.78  fof(f230,plain,(
% 3.17/0.78    ( ! [X0] : (k6_subset_1(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_3),
% 3.17/0.78    inference(unit_resulting_resolution,[],[f129,f111])).
% 3.17/0.78  fof(f111,plain,(
% 3.17/0.78    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)) )),
% 3.17/0.78    inference(definition_unfolding,[],[f96,f79])).
% 3.17/0.78  fof(f79,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.17/0.78    inference(cnf_transformation,[],[f21])).
% 3.17/0.78  fof(f21,axiom,(
% 3.17/0.78    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 3.17/0.78  fof(f96,plain,(
% 3.17/0.78    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.17/0.78    inference(cnf_transformation,[],[f50])).
% 3.17/0.78  fof(f50,plain,(
% 3.17/0.78    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.17/0.78    inference(ennf_transformation,[],[f22])).
% 3.17/0.78  fof(f22,axiom,(
% 3.17/0.78    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.17/0.78  fof(f3195,plain,(
% 3.17/0.78    k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_37),
% 3.17/0.78    inference(superposition,[],[f195,f2866])).
% 3.17/0.78  fof(f2866,plain,(
% 3.17/0.78    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_37),
% 3.17/0.78    inference(avatar_component_clause,[],[f2864])).
% 3.17/0.78  fof(f2864,plain,(
% 3.17/0.78    spl2_37 <=> k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 3.17/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 3.17/0.78  fof(f195,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k3_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 3.17/0.78    inference(unit_resulting_resolution,[],[f77,f109])).
% 3.17/0.78  fof(f109,plain,(
% 3.17/0.78    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.17/0.78    inference(definition_unfolding,[],[f88,f79])).
% 3.17/0.78  fof(f88,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.17/0.78    inference(cnf_transformation,[],[f42])).
% 3.17/0.78  fof(f42,plain,(
% 3.17/0.78    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.17/0.78    inference(ennf_transformation,[],[f16])).
% 3.17/0.78  fof(f16,axiom,(
% 3.17/0.78    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 3.17/0.78  fof(f77,plain,(
% 3.17/0.78    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 3.17/0.78    inference(cnf_transformation,[],[f18])).
% 3.17/0.78  fof(f18,axiom,(
% 3.17/0.78    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 3.17/0.78  fof(f3855,plain,(
% 3.17/0.78    sK1 = k5_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | ~spl2_37),
% 3.17/0.78    inference(backward_demodulation,[],[f3193,f3854])).
% 3.17/0.78  fof(f3854,plain,(
% 3.17/0.78    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_37),
% 3.17/0.78    inference(forward_demodulation,[],[f3782,f3195])).
% 3.17/0.78  fof(f3782,plain,(
% 3.17/0.78    k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_37),
% 3.17/0.78    inference(superposition,[],[f3456,f2866])).
% 3.17/0.78  fof(f3456,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 3.17/0.78    inference(backward_demodulation,[],[f195,f3453])).
% 3.17/0.78  fof(f3453,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_subset_1(X0,k6_subset_1(X0,X1))) )),
% 3.17/0.78    inference(forward_demodulation,[],[f3409,f3451])).
% 3.17/0.78  fof(f3451,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k3_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 3.17/0.78    inference(forward_demodulation,[],[f3410,f108])).
% 3.17/0.78  fof(f108,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 3.17/0.78    inference(definition_unfolding,[],[f86,f79,f79,f81])).
% 3.17/0.78  fof(f81,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.17/0.78    inference(cnf_transformation,[],[f24])).
% 3.17/0.78  fof(f24,axiom,(
% 3.17/0.78    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.17/0.78  fof(f86,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.17/0.78    inference(cnf_transformation,[],[f10])).
% 3.17/0.78  fof(f10,axiom,(
% 3.17/0.78    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 3.17/0.78  fof(f3410,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k6_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 3.17/0.78    inference(unit_resulting_resolution,[],[f474,f196])).
% 3.17/0.78  fof(f196,plain,(
% 3.17/0.78    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.17/0.78    inference(resolution,[],[f109,f95])).
% 3.17/0.78  fof(f95,plain,(
% 3.17/0.78    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.17/0.78    inference(cnf_transformation,[],[f62])).
% 3.17/0.78  fof(f62,plain,(
% 3.17/0.78    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.17/0.78    inference(nnf_transformation,[],[f25])).
% 3.17/0.78  fof(f25,axiom,(
% 3.17/0.78    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.17/0.78  fof(f474,plain,(
% 3.17/0.78    ( ! [X2,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)) )),
% 3.17/0.78    inference(superposition,[],[f215,f104])).
% 3.17/0.78  fof(f104,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0) )),
% 3.17/0.78    inference(definition_unfolding,[],[f80,f82,f81])).
% 3.17/0.78  fof(f82,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.17/0.78    inference(cnf_transformation,[],[f14])).
% 3.17/0.78  fof(f14,axiom,(
% 3.17/0.78    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.17/0.78  fof(f80,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.17/0.78    inference(cnf_transformation,[],[f4])).
% 3.17/0.78  fof(f4,axiom,(
% 3.17/0.78    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 3.17/0.78  fof(f215,plain,(
% 3.17/0.78    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) )),
% 3.17/0.78    inference(unit_resulting_resolution,[],[f103,f113])).
% 3.17/0.78  fof(f113,plain,(
% 3.17/0.78    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 3.17/0.78    inference(definition_unfolding,[],[f98,f82,f79])).
% 3.17/0.78  fof(f98,plain,(
% 3.17/0.78    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 3.17/0.78    inference(cnf_transformation,[],[f52])).
% 3.17/0.78  fof(f52,plain,(
% 3.17/0.78    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.17/0.78    inference(ennf_transformation,[],[f9])).
% 3.17/0.78  fof(f9,axiom,(
% 3.17/0.78    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 3.17/0.78  fof(f103,plain,(
% 3.17/0.78    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 3.17/0.78    inference(definition_unfolding,[],[f76,f79])).
% 3.17/0.78  fof(f76,plain,(
% 3.17/0.78    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.17/0.78    inference(cnf_transformation,[],[f5])).
% 3.17/0.78  fof(f5,axiom,(
% 3.17/0.78    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.17/0.78  fof(f3409,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_subset_1(X0,k3_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 3.17/0.78    inference(unit_resulting_resolution,[],[f474,f190])).
% 3.17/0.78  fof(f190,plain,(
% 3.17/0.78    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 3.17/0.78    inference(resolution,[],[f89,f95])).
% 3.17/0.78  fof(f89,plain,(
% 3.17/0.78    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 3.17/0.78    inference(cnf_transformation,[],[f43])).
% 3.17/0.78  fof(f43,plain,(
% 3.17/0.78    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.17/0.78    inference(ennf_transformation,[],[f19])).
% 3.17/0.78  fof(f19,axiom,(
% 3.17/0.78    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 3.17/0.78  fof(f3193,plain,(
% 3.17/0.78    sK1 = k5_xboole_0(k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1)) | ~spl2_37),
% 3.17/0.78    inference(superposition,[],[f187,f2866])).
% 3.17/0.78  fof(f187,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1)) = X0) )),
% 3.17/0.78    inference(forward_demodulation,[],[f186,f104])).
% 3.17/0.78  fof(f186,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1))) )),
% 3.17/0.78    inference(forward_demodulation,[],[f182,f78])).
% 3.17/0.78  fof(f78,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.17/0.78    inference(cnf_transformation,[],[f13])).
% 3.17/0.78  fof(f13,axiom,(
% 3.17/0.78    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.17/0.78  fof(f182,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1))) )),
% 3.17/0.78    inference(superposition,[],[f105,f108])).
% 3.17/0.78  fof(f105,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 3.17/0.78    inference(definition_unfolding,[],[f83,f82,f79])).
% 3.17/0.78  fof(f83,plain,(
% 3.17/0.78    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.17/0.78    inference(cnf_transformation,[],[f12])).
% 3.17/0.78  fof(f12,axiom,(
% 3.17/0.78    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.17/0.78  fof(f4534,plain,(
% 3.17/0.78    k2_pre_topc(sK0,sK1) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_9 | ~spl2_37)),
% 3.17/0.78    inference(forward_demodulation,[],[f3207,f354])).
% 3.17/0.78  fof(f354,plain,(
% 3.17/0.78    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_2 | ~spl2_3 | ~spl2_9)),
% 3.17/0.78    inference(forward_demodulation,[],[f346,f304])).
% 3.17/0.78  fof(f304,plain,(
% 3.17/0.78    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 3.17/0.78    inference(unit_resulting_resolution,[],[f124,f129,f73])).
% 3.17/0.78  fof(f73,plain,(
% 3.17/0.78    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 3.17/0.78    inference(cnf_transformation,[],[f38])).
% 3.17/0.78  fof(f38,plain,(
% 3.17/0.78    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.17/0.78    inference(ennf_transformation,[],[f30])).
% 3.17/0.78  fof(f30,axiom,(
% 3.17/0.78    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 3.17/0.78  fof(f346,plain,(
% 3.17/0.78    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_9)),
% 3.17/0.78    inference(unit_resulting_resolution,[],[f129,f317,f114])).
% 3.17/0.78  fof(f114,plain,(
% 3.17/0.78    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.17/0.78    inference(definition_unfolding,[],[f100,f82])).
% 3.17/0.78  fof(f100,plain,(
% 3.17/0.78    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.17/0.78    inference(cnf_transformation,[],[f56])).
% 3.17/0.78  fof(f56,plain,(
% 3.17/0.78    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.17/0.78    inference(flattening,[],[f55])).
% 3.17/0.78  fof(f55,plain,(
% 3.17/0.78    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.17/0.78    inference(ennf_transformation,[],[f20])).
% 3.17/0.78  fof(f20,axiom,(
% 3.17/0.78    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.17/0.78  fof(f317,plain,(
% 3.17/0.78    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_9),
% 3.17/0.78    inference(avatar_component_clause,[],[f315])).
% 3.17/0.78  fof(f315,plain,(
% 3.17/0.78    spl2_9 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.17/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 3.17/0.78  fof(f3207,plain,(
% 3.17/0.78    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_37),
% 3.17/0.78    inference(forward_demodulation,[],[f3187,f78])).
% 3.17/0.78  fof(f3187,plain,(
% 3.17/0.78    k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_37),
% 3.17/0.78    inference(superposition,[],[f105,f2866])).
% 3.17/0.78  fof(f4490,plain,(
% 3.17/0.78    ~spl2_3 | spl2_6 | ~spl2_37 | ~spl2_47),
% 3.17/0.78    inference(avatar_contradiction_clause,[],[f4489])).
% 3.17/0.78  fof(f4489,plain,(
% 3.17/0.78    $false | (~spl2_3 | spl2_6 | ~spl2_37 | ~spl2_47)),
% 3.17/0.78    inference(subsumption_resolution,[],[f2730,f4478])).
% 3.17/0.78  fof(f4478,plain,(
% 3.17/0.78    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_37 | ~spl2_47)),
% 3.17/0.78    inference(backward_demodulation,[],[f3195,f4475])).
% 3.17/0.78  fof(f4475,plain,(
% 3.17/0.78    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_37 | ~spl2_47)),
% 3.17/0.78    inference(forward_demodulation,[],[f4450,f4473])).
% 3.17/0.78  fof(f4473,plain,(
% 3.17/0.78    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_37 | ~spl2_47)),
% 3.17/0.78    inference(forward_demodulation,[],[f4451,f2866])).
% 3.17/0.78  fof(f4451,plain,(
% 3.17/0.78    k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_47),
% 3.17/0.78    inference(unit_resulting_resolution,[],[f3897,f196])).
% 3.17/0.78  fof(f3897,plain,(
% 3.17/0.78    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_47),
% 3.17/0.78    inference(avatar_component_clause,[],[f3895])).
% 3.17/0.78  fof(f3895,plain,(
% 3.17/0.78    spl2_47 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 3.17/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 3.17/0.78  fof(f4450,plain,(
% 3.17/0.78    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_47),
% 3.17/0.78    inference(unit_resulting_resolution,[],[f3897,f190])).
% 3.17/0.78  fof(f2730,plain,(
% 3.17/0.78    k2_tops_1(sK0,sK1) != k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | spl2_6)),
% 3.17/0.78    inference(superposition,[],[f162,f230])).
% 3.17/0.78  fof(f162,plain,(
% 3.17/0.78    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_6),
% 3.17/0.78    inference(avatar_component_clause,[],[f161])).
% 3.17/0.78  fof(f3898,plain,(
% 3.17/0.78    spl2_47 | ~spl2_34),
% 3.17/0.78    inference(avatar_split_clause,[],[f2746,f2737,f3895])).
% 3.17/0.78  fof(f2737,plain,(
% 3.17/0.78    spl2_34 <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 3.17/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 3.17/0.78  fof(f2746,plain,(
% 3.17/0.78    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_34),
% 3.17/0.78    inference(superposition,[],[f215,f2739])).
% 3.17/0.78  fof(f2739,plain,(
% 3.17/0.78    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_34),
% 3.17/0.78    inference(avatar_component_clause,[],[f2737])).
% 3.17/0.78  fof(f2867,plain,(
% 3.17/0.78    spl2_37 | ~spl2_3 | ~spl2_18),
% 3.17/0.78    inference(avatar_split_clause,[],[f654,f645,f127,f2864])).
% 3.17/0.78  fof(f645,plain,(
% 3.17/0.78    spl2_18 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 3.17/0.78    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 3.17/0.78  fof(f654,plain,(
% 3.17/0.78    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_18)),
% 3.17/0.78    inference(superposition,[],[f647,f230])).
% 3.17/0.78  fof(f647,plain,(
% 3.17/0.78    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_18),
% 3.17/0.78    inference(avatar_component_clause,[],[f645])).
% 3.17/0.78  fof(f2740,plain,(
% 3.17/0.78    spl2_34 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_9),
% 3.17/0.78    inference(avatar_split_clause,[],[f2726,f315,f157,f127,f122,f2737])).
% 3.17/0.78  fof(f2726,plain,(
% 3.17/0.78    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_9)),
% 3.17/0.78    inference(backward_demodulation,[],[f354,f2723])).
% 3.17/0.78  fof(f2723,plain,(
% 3.17/0.78    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_3 | ~spl2_5)),
% 3.17/0.78    inference(subsumption_resolution,[],[f765,f159])).
% 3.17/0.78  fof(f159,plain,(
% 3.17/0.78    v4_pre_topc(sK1,sK0) | ~spl2_5),
% 3.17/0.78    inference(avatar_component_clause,[],[f157])).
% 3.17/0.78  fof(f765,plain,(
% 3.17/0.78    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_3)),
% 3.17/0.78    inference(resolution,[],[f267,f129])).
% 3.17/0.78  fof(f267,plain,(
% 3.17/0.78    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) = X0) ) | ~spl2_2),
% 3.17/0.78    inference(resolution,[],[f74,f124])).
% 3.17/0.78  fof(f74,plain,(
% 3.17/0.78    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 3.17/0.78    inference(cnf_transformation,[],[f40])).
% 3.17/0.78  fof(f648,plain,(
% 3.17/0.78    spl2_18 | ~spl2_2 | ~spl2_3),
% 3.17/0.78    inference(avatar_split_clause,[],[f300,f127,f122,f645])).
% 3.17/0.78  fof(f300,plain,(
% 3.17/0.78    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 3.17/0.78    inference(unit_resulting_resolution,[],[f124,f129,f72])).
% 3.17/0.78  fof(f72,plain,(
% 3.17/0.78    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 3.17/0.78    inference(cnf_transformation,[],[f37])).
% 3.17/0.78  fof(f37,plain,(
% 3.17/0.78    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.17/0.78    inference(ennf_transformation,[],[f31])).
% 3.17/0.78  fof(f31,axiom,(
% 3.17/0.78    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 3.17/0.78  fof(f318,plain,(
% 3.17/0.78    spl2_9 | ~spl2_2 | ~spl2_3),
% 3.17/0.78    inference(avatar_split_clause,[],[f259,f127,f122,f315])).
% 3.17/0.78  fof(f259,plain,(
% 3.17/0.78    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 3.17/0.78    inference(unit_resulting_resolution,[],[f124,f129,f93])).
% 3.17/0.78  fof(f93,plain,(
% 3.17/0.78    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.17/0.78    inference(cnf_transformation,[],[f49])).
% 3.17/0.78  fof(f49,plain,(
% 3.17/0.78    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.17/0.78    inference(flattening,[],[f48])).
% 3.17/0.78  fof(f48,plain,(
% 3.17/0.78    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.17/0.78    inference(ennf_transformation,[],[f27])).
% 3.17/0.78  fof(f27,axiom,(
% 3.17/0.78    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 3.17/0.78  fof(f167,plain,(
% 3.17/0.78    ~spl2_5 | ~spl2_6),
% 3.17/0.78    inference(avatar_split_clause,[],[f166,f161,f157])).
% 3.17/0.78  fof(f166,plain,(
% 3.17/0.78    ~v4_pre_topc(sK1,sK0) | ~spl2_6),
% 3.17/0.78    inference(trivial_inequality_removal,[],[f165])).
% 3.17/0.78  fof(f165,plain,(
% 3.17/0.78    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0) | ~spl2_6),
% 3.17/0.78    inference(backward_demodulation,[],[f67,f163])).
% 3.17/0.78  fof(f67,plain,(
% 3.17/0.78    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 3.17/0.78    inference(cnf_transformation,[],[f61])).
% 3.17/0.78  fof(f61,plain,(
% 3.17/0.78    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.17/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f58,f60,f59])).
% 3.17/0.78  fof(f59,plain,(
% 3.17/0.78    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.17/0.78    introduced(choice_axiom,[])).
% 3.17/0.78  fof(f60,plain,(
% 3.17/0.78    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.17/0.78    introduced(choice_axiom,[])).
% 3.17/0.78  fof(f58,plain,(
% 3.17/0.78    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.17/0.78    inference(flattening,[],[f57])).
% 3.17/0.78  fof(f57,plain,(
% 3.17/0.78    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.17/0.78    inference(nnf_transformation,[],[f35])).
% 3.17/0.78  fof(f35,plain,(
% 3.17/0.78    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.17/0.78    inference(flattening,[],[f34])).
% 3.17/0.78  fof(f34,plain,(
% 3.17/0.78    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.17/0.78    inference(ennf_transformation,[],[f33])).
% 3.17/0.78  fof(f33,negated_conjecture,(
% 3.17/0.78    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 3.17/0.78    inference(negated_conjecture,[],[f32])).
% 3.17/0.78  fof(f32,conjecture,(
% 3.17/0.78    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 3.17/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 3.17/0.78  fof(f164,plain,(
% 3.17/0.78    spl2_5 | spl2_6),
% 3.17/0.78    inference(avatar_split_clause,[],[f66,f161,f157])).
% 3.17/0.78  fof(f66,plain,(
% 3.17/0.78    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 3.17/0.78    inference(cnf_transformation,[],[f61])).
% 3.17/0.78  fof(f130,plain,(
% 3.17/0.78    spl2_3),
% 3.17/0.78    inference(avatar_split_clause,[],[f65,f127])).
% 3.17/0.78  fof(f65,plain,(
% 3.17/0.78    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.17/0.78    inference(cnf_transformation,[],[f61])).
% 3.17/0.78  fof(f125,plain,(
% 3.17/0.78    spl2_2),
% 3.17/0.78    inference(avatar_split_clause,[],[f64,f122])).
% 3.17/0.78  fof(f64,plain,(
% 3.17/0.78    l1_pre_topc(sK0)),
% 3.17/0.78    inference(cnf_transformation,[],[f61])).
% 3.17/0.78  fof(f120,plain,(
% 3.17/0.78    spl2_1),
% 3.17/0.78    inference(avatar_split_clause,[],[f63,f117])).
% 3.17/0.78  fof(f63,plain,(
% 3.17/0.78    v2_pre_topc(sK0)),
% 3.17/0.78    inference(cnf_transformation,[],[f61])).
% 3.17/0.78  % SZS output end Proof for theBenchmark
% 3.17/0.78  % (27211)------------------------------
% 3.17/0.78  % (27211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.78  % (27211)Termination reason: Refutation
% 3.17/0.78  
% 3.17/0.78  % (27211)Memory used [KB]: 14072
% 3.17/0.78  % (27211)Time elapsed: 0.370 s
% 3.17/0.78  % (27211)------------------------------
% 3.17/0.78  % (27211)------------------------------
% 3.17/0.80  % (27195)Success in time 0.437 s
%------------------------------------------------------------------------------
