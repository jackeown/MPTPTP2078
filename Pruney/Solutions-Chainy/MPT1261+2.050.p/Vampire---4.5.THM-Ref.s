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
% DateTime   : Thu Dec  3 13:11:55 EST 2020

% Result     : Theorem 3.78s
% Output     : Refutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 318 expanded)
%              Number of leaves         :   31 ( 125 expanded)
%              Depth                    :   12
%              Number of atoms          :  364 ( 858 expanded)
%              Number of equality atoms :   86 ( 251 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6327,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f108,f113,f151,f154,f253,f293,f763,f2759,f2768,f3618,f3628,f3901,f3949,f6324])).

fof(f6324,plain,
    ( spl2_6
    | ~ spl2_18
    | ~ spl2_57
    | ~ spl2_59 ),
    inference(avatar_contradiction_clause,[],[f6323])).

fof(f6323,plain,
    ( $false
    | spl2_6
    | ~ spl2_18
    | ~ spl2_57
    | ~ spl2_59 ),
    inference(subsumption_resolution,[],[f6314,f149])).

fof(f149,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f6314,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_18
    | ~ spl2_57
    | ~ spl2_59 ),
    inference(backward_demodulation,[],[f762,f6311])).

fof(f6311,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_57
    | ~ spl2_59 ),
    inference(backward_demodulation,[],[f3900,f6303])).

fof(f6303,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_59 ),
    inference(superposition,[],[f730,f3948])).

fof(f3948,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_59 ),
    inference(avatar_component_clause,[],[f3946])).

fof(f3946,plain,
    ( spl2_59
  <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f730,plain,(
    ! [X4,X5] : k3_tarski(k2_tarski(X4,k1_setfam_1(k2_tarski(X4,X5)))) = X4 ),
    inference(superposition,[],[f191,f90])).

fof(f90,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f72,f70,f69,f69])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f191,plain,(
    ! [X2,X3] : k3_tarski(k2_tarski(X2,k6_subset_1(X2,X3))) = X2 ),
    inference(forward_demodulation,[],[f190,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f190,plain,(
    ! [X2,X3] : k3_tarski(k2_tarski(k6_subset_1(X2,X3),X2)) = X2 ),
    inference(forward_demodulation,[],[f186,f98])).

fof(f98,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(forward_demodulation,[],[f93,f68])).

fof(f93,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f75,f71,f70,f69])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f186,plain,(
    ! [X2,X3] : k3_tarski(k2_tarski(k6_subset_1(X2,X3),X2)) = k3_tarski(k2_tarski(k6_subset_1(X2,X3),k1_setfam_1(k2_tarski(X2,X3)))) ),
    inference(superposition,[],[f92,f90])).

fof(f92,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0))) ),
    inference(definition_unfolding,[],[f74,f71,f69,f71])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f3900,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f3898])).

fof(f3898,plain,
    ( spl2_57
  <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f762,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f760])).

fof(f760,plain,
    ( spl2_18
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f3949,plain,
    ( spl2_59
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f3737,f2765,f3946])).

fof(f2765,plain,
    ( spl2_44
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f3737,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f3719,f68])).

fof(f3719,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_44 ),
    inference(unit_resulting_resolution,[],[f2767,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f76,f70])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f2767,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f2765])).

fof(f3901,plain,
    ( spl2_57
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f317,f290,f110,f105,f3898])).

fof(f105,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f110,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f290,plain,
    ( spl2_9
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f317,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f311,f276])).

fof(f276,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f107,f112,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f112,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f107,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f311,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f112,f292,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f86,f71])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f292,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f290])).

fof(f3628,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_5
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_43 ),
    inference(avatar_contradiction_clause,[],[f3627])).

fof(f3627,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | spl2_5
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_43 ),
    inference(subsumption_resolution,[],[f3623,f145])).

fof(f145,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl2_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f3623,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_43 ),
    inference(backward_demodulation,[],[f252,f3622])).

fof(f3622,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_43 ),
    inference(backward_demodulation,[],[f317,f3606])).

fof(f3606,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_43 ),
    inference(superposition,[],[f191,f2758])).

fof(f2758,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f2756])).

fof(f2756,plain,
    ( spl2_43
  <=> k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f252,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl2_7
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f3618,plain,
    ( ~ spl2_43
    | spl2_44 ),
    inference(avatar_contradiction_clause,[],[f3617])).

fof(f3617,plain,
    ( $false
    | ~ spl2_43
    | spl2_44 ),
    inference(subsumption_resolution,[],[f3599,f2766])).

fof(f2766,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_44 ),
    inference(avatar_component_clause,[],[f2765])).

fof(f3599,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_43 ),
    inference(superposition,[],[f88,f2758])).

fof(f88,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f65,f69])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2768,plain,
    ( spl2_44
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f2762,f144,f110,f105,f2765])).

fof(f2762,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f107,f112,f146,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f146,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f2759,plain,
    ( spl2_43
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f403,f148,f110,f2756])).

fof(f403,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f213,f150])).

fof(f150,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f148])).

fof(f213,plain,
    ( ! [X0] : k6_subset_1(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f112,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) ) ),
    inference(definition_unfolding,[],[f84,f69])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f763,plain,
    ( spl2_18
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f280,f110,f105,f760])).

fof(f280,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f107,f112,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f293,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f236,f110,f105,f290])).

fof(f236,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f107,f112,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f253,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f231,f110,f105,f100,f250])).

fof(f100,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f231,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f102,f107,f112,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f102,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f154,plain,
    ( ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f153,f148,f144])).

fof(f153,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f152])).

fof(f152,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f59,f150])).

fof(f59,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f52,f51])).

fof(f51,plain,
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

fof(f52,plain,
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

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f151,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f58,f148,f144])).

fof(f58,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f113,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f57,f110])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f108,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f56,f105])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f103,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f55,f100])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 21:01:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.47  % (20662)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (20664)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (20660)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (20661)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (20673)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (20658)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (20663)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (20672)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (20669)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (20668)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (20671)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.51  % (20667)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (20665)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (20670)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.52  % (20659)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.55  % (20674)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.56  % (20666)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.56  % (20675)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 3.78/0.84  % (20673)Refutation found. Thanks to Tanya!
% 3.78/0.84  % SZS status Theorem for theBenchmark
% 3.78/0.84  % SZS output start Proof for theBenchmark
% 3.78/0.84  fof(f6327,plain,(
% 3.78/0.84    $false),
% 3.78/0.84    inference(avatar_sat_refutation,[],[f103,f108,f113,f151,f154,f253,f293,f763,f2759,f2768,f3618,f3628,f3901,f3949,f6324])).
% 3.78/0.84  fof(f6324,plain,(
% 3.78/0.84    spl2_6 | ~spl2_18 | ~spl2_57 | ~spl2_59),
% 3.78/0.84    inference(avatar_contradiction_clause,[],[f6323])).
% 3.78/0.84  fof(f6323,plain,(
% 3.78/0.84    $false | (spl2_6 | ~spl2_18 | ~spl2_57 | ~spl2_59)),
% 3.78/0.84    inference(subsumption_resolution,[],[f6314,f149])).
% 3.78/0.84  fof(f149,plain,(
% 3.78/0.84    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_6),
% 3.78/0.84    inference(avatar_component_clause,[],[f148])).
% 3.78/0.84  fof(f148,plain,(
% 3.78/0.84    spl2_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 3.78/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 3.78/0.84  fof(f6314,plain,(
% 3.78/0.84    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_18 | ~spl2_57 | ~spl2_59)),
% 3.78/0.84    inference(backward_demodulation,[],[f762,f6311])).
% 3.78/0.84  fof(f6311,plain,(
% 3.78/0.84    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_57 | ~spl2_59)),
% 3.78/0.84    inference(backward_demodulation,[],[f3900,f6303])).
% 3.78/0.84  fof(f6303,plain,(
% 3.78/0.84    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_59),
% 3.78/0.84    inference(superposition,[],[f730,f3948])).
% 3.78/0.84  fof(f3948,plain,(
% 3.78/0.84    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_59),
% 3.78/0.84    inference(avatar_component_clause,[],[f3946])).
% 3.78/0.84  fof(f3946,plain,(
% 3.78/0.84    spl2_59 <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 3.78/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 3.78/0.84  fof(f730,plain,(
% 3.78/0.84    ( ! [X4,X5] : (k3_tarski(k2_tarski(X4,k1_setfam_1(k2_tarski(X4,X5)))) = X4) )),
% 3.78/0.84    inference(superposition,[],[f191,f90])).
% 3.78/0.84  fof(f90,plain,(
% 3.78/0.84    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 3.78/0.84    inference(definition_unfolding,[],[f72,f70,f69,f69])).
% 3.78/0.84  fof(f69,plain,(
% 3.78/0.84    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.78/0.84    inference(cnf_transformation,[],[f17])).
% 3.78/0.84  fof(f17,axiom,(
% 3.78/0.84    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.78/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 3.78/0.84  fof(f70,plain,(
% 3.78/0.84    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.78/0.84    inference(cnf_transformation,[],[f19])).
% 3.78/0.84  fof(f19,axiom,(
% 3.78/0.84    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.78/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.78/0.84  fof(f72,plain,(
% 3.78/0.84    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.78/0.84    inference(cnf_transformation,[],[f8])).
% 3.78/0.84  fof(f8,axiom,(
% 3.78/0.84    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.78/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.78/0.84  fof(f191,plain,(
% 3.78/0.84    ( ! [X2,X3] : (k3_tarski(k2_tarski(X2,k6_subset_1(X2,X3))) = X2) )),
% 3.78/0.84    inference(forward_demodulation,[],[f190,f68])).
% 3.78/0.84  fof(f68,plain,(
% 3.78/0.84    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.78/0.84    inference(cnf_transformation,[],[f10])).
% 3.78/0.84  fof(f10,axiom,(
% 3.78/0.84    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.78/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.78/0.84  fof(f190,plain,(
% 3.78/0.84    ( ! [X2,X3] : (k3_tarski(k2_tarski(k6_subset_1(X2,X3),X2)) = X2) )),
% 3.78/0.84    inference(forward_demodulation,[],[f186,f98])).
% 3.78/0.84  fof(f98,plain,(
% 3.78/0.84    ( ! [X0,X1] : (k3_tarski(k2_tarski(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = X0) )),
% 3.78/0.84    inference(forward_demodulation,[],[f93,f68])).
% 3.78/0.84  fof(f93,plain,(
% 3.78/0.84    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1))) = X0) )),
% 3.78/0.84    inference(definition_unfolding,[],[f75,f71,f70,f69])).
% 3.78/0.84  fof(f71,plain,(
% 3.78/0.84    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.78/0.84    inference(cnf_transformation,[],[f11])).
% 3.78/0.84  fof(f11,axiom,(
% 3.78/0.84    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.78/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.78/0.84  fof(f75,plain,(
% 3.78/0.84    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.78/0.84    inference(cnf_transformation,[],[f9])).
% 3.78/0.84  fof(f9,axiom,(
% 3.78/0.84    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.78/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 3.78/0.84  fof(f186,plain,(
% 3.78/0.84    ( ! [X2,X3] : (k3_tarski(k2_tarski(k6_subset_1(X2,X3),X2)) = k3_tarski(k2_tarski(k6_subset_1(X2,X3),k1_setfam_1(k2_tarski(X2,X3))))) )),
% 3.78/0.84    inference(superposition,[],[f92,f90])).
% 3.78/0.84  fof(f92,plain,(
% 3.78/0.84    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0)))) )),
% 3.78/0.84    inference(definition_unfolding,[],[f74,f71,f69,f71])).
% 3.78/0.84  fof(f74,plain,(
% 3.78/0.84    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.78/0.84    inference(cnf_transformation,[],[f6])).
% 3.78/0.84  fof(f6,axiom,(
% 3.78/0.84    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.78/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 3.78/0.84  fof(f3900,plain,(
% 3.78/0.84    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_57),
% 3.78/0.84    inference(avatar_component_clause,[],[f3898])).
% 3.78/0.84  fof(f3898,plain,(
% 3.78/0.84    spl2_57 <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 3.78/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 3.78/0.84  fof(f762,plain,(
% 3.78/0.84    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_18),
% 3.78/0.84    inference(avatar_component_clause,[],[f760])).
% 3.78/0.84  fof(f760,plain,(
% 3.78/0.84    spl2_18 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 3.78/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 3.78/0.84  fof(f3949,plain,(
% 3.78/0.84    spl2_59 | ~spl2_44),
% 3.78/0.84    inference(avatar_split_clause,[],[f3737,f2765,f3946])).
% 3.78/0.84  fof(f2765,plain,(
% 3.78/0.84    spl2_44 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 3.78/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 3.78/0.84  fof(f3737,plain,(
% 3.78/0.84    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_44),
% 3.78/0.84    inference(forward_demodulation,[],[f3719,f68])).
% 3.78/0.84  fof(f3719,plain,(
% 3.78/0.84    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) | ~spl2_44),
% 3.78/0.84    inference(unit_resulting_resolution,[],[f2767,f94])).
% 3.78/0.84  fof(f94,plain,(
% 3.78/0.84    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 3.78/0.84    inference(definition_unfolding,[],[f76,f70])).
% 3.78/0.84  fof(f76,plain,(
% 3.78/0.84    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.78/0.84    inference(cnf_transformation,[],[f36])).
% 3.78/0.84  fof(f36,plain,(
% 3.78/0.84    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.78/0.84    inference(ennf_transformation,[],[f4])).
% 3.78/0.84  fof(f4,axiom,(
% 3.78/0.84    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.78/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.78/0.84  fof(f2767,plain,(
% 3.78/0.84    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_44),
% 3.78/0.84    inference(avatar_component_clause,[],[f2765])).
% 3.78/0.84  fof(f3901,plain,(
% 3.78/0.84    spl2_57 | ~spl2_2 | ~spl2_3 | ~spl2_9),
% 3.78/0.84    inference(avatar_split_clause,[],[f317,f290,f110,f105,f3898])).
% 3.78/0.84  fof(f105,plain,(
% 3.78/0.84    spl2_2 <=> l1_pre_topc(sK0)),
% 3.78/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.78/0.84  fof(f110,plain,(
% 3.78/0.84    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.78/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 3.78/0.84  fof(f290,plain,(
% 3.78/0.84    spl2_9 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.78/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 3.78/0.84  fof(f317,plain,(
% 3.78/0.84    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_2 | ~spl2_3 | ~spl2_9)),
% 3.78/0.84    inference(forward_demodulation,[],[f311,f276])).
% 3.78/0.84  fof(f276,plain,(
% 3.78/0.84    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 3.78/0.84    inference(unit_resulting_resolution,[],[f107,f112,f62])).
% 3.78/0.84  fof(f62,plain,(
% 3.78/0.84    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 3.78/0.84    inference(cnf_transformation,[],[f32])).
% 3.78/0.84  fof(f32,plain,(
% 3.78/0.84    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.78/0.84    inference(ennf_transformation,[],[f25])).
% 3.78/0.84  fof(f25,axiom,(
% 3.78/0.84    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.78/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 3.78/0.84  fof(f112,plain,(
% 3.78/0.84    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 3.78/0.84    inference(avatar_component_clause,[],[f110])).
% 3.78/0.84  fof(f107,plain,(
% 3.78/0.84    l1_pre_topc(sK0) | ~spl2_2),
% 3.78/0.84    inference(avatar_component_clause,[],[f105])).
% 3.78/0.84  fof(f311,plain,(
% 3.78/0.84    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_9)),
% 3.78/0.84    inference(unit_resulting_resolution,[],[f112,f292,f97])).
% 3.78/0.84  fof(f97,plain,(
% 3.78/0.84    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.78/0.84    inference(definition_unfolding,[],[f86,f71])).
% 3.78/0.84  fof(f86,plain,(
% 3.78/0.84    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.78/0.84    inference(cnf_transformation,[],[f48])).
% 3.78/0.84  fof(f48,plain,(
% 3.78/0.84    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.78/0.84    inference(flattening,[],[f47])).
% 3.78/0.84  fof(f47,plain,(
% 3.78/0.84    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.78/0.84    inference(ennf_transformation,[],[f16])).
% 3.78/0.84  fof(f16,axiom,(
% 3.78/0.84    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 3.78/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.78/0.84  fof(f292,plain,(
% 3.78/0.84    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_9),
% 3.78/0.84    inference(avatar_component_clause,[],[f290])).
% 3.78/0.84  fof(f3628,plain,(
% 3.78/0.84    ~spl2_2 | ~spl2_3 | spl2_5 | ~spl2_7 | ~spl2_9 | ~spl2_43),
% 3.78/0.84    inference(avatar_contradiction_clause,[],[f3627])).
% 3.78/0.84  fof(f3627,plain,(
% 3.78/0.84    $false | (~spl2_2 | ~spl2_3 | spl2_5 | ~spl2_7 | ~spl2_9 | ~spl2_43)),
% 3.78/0.84    inference(subsumption_resolution,[],[f3623,f145])).
% 3.78/0.84  fof(f145,plain,(
% 3.78/0.84    ~v4_pre_topc(sK1,sK0) | spl2_5),
% 3.78/0.84    inference(avatar_component_clause,[],[f144])).
% 3.78/0.84  fof(f144,plain,(
% 3.78/0.84    spl2_5 <=> v4_pre_topc(sK1,sK0)),
% 3.78/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 3.78/0.84  fof(f3623,plain,(
% 3.78/0.84    v4_pre_topc(sK1,sK0) | (~spl2_2 | ~spl2_3 | ~spl2_7 | ~spl2_9 | ~spl2_43)),
% 3.78/0.84    inference(backward_demodulation,[],[f252,f3622])).
% 3.78/0.84  fof(f3622,plain,(
% 3.78/0.84    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_3 | ~spl2_9 | ~spl2_43)),
% 3.78/0.84    inference(backward_demodulation,[],[f317,f3606])).
% 3.78/0.84  fof(f3606,plain,(
% 3.78/0.84    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_43),
% 3.78/0.84    inference(superposition,[],[f191,f2758])).
% 3.78/0.84  fof(f2758,plain,(
% 3.78/0.84    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_43),
% 3.78/0.84    inference(avatar_component_clause,[],[f2756])).
% 3.78/0.84  fof(f2756,plain,(
% 3.78/0.84    spl2_43 <=> k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 3.78/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 3.78/0.84  fof(f252,plain,(
% 3.78/0.84    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~spl2_7),
% 3.78/0.84    inference(avatar_component_clause,[],[f250])).
% 3.78/0.84  fof(f250,plain,(
% 3.78/0.84    spl2_7 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 3.78/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 3.78/0.84  fof(f3618,plain,(
% 3.78/0.84    ~spl2_43 | spl2_44),
% 3.78/0.84    inference(avatar_contradiction_clause,[],[f3617])).
% 3.78/0.84  fof(f3617,plain,(
% 3.78/0.84    $false | (~spl2_43 | spl2_44)),
% 3.78/0.84    inference(subsumption_resolution,[],[f3599,f2766])).
% 3.78/0.84  fof(f2766,plain,(
% 3.78/0.84    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_44),
% 3.78/0.84    inference(avatar_component_clause,[],[f2765])).
% 3.78/0.84  fof(f3599,plain,(
% 3.78/0.84    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_43),
% 3.78/0.84    inference(superposition,[],[f88,f2758])).
% 3.78/0.84  fof(f88,plain,(
% 3.78/0.84    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 3.78/0.84    inference(definition_unfolding,[],[f65,f69])).
% 3.78/0.84  fof(f65,plain,(
% 3.78/0.84    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.78/0.84    inference(cnf_transformation,[],[f5])).
% 3.78/0.84  fof(f5,axiom,(
% 3.78/0.84    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.78/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.78/0.84  fof(f2768,plain,(
% 3.78/0.84    spl2_44 | ~spl2_2 | ~spl2_3 | ~spl2_5),
% 3.78/0.84    inference(avatar_split_clause,[],[f2762,f144,f110,f105,f2765])).
% 3.78/0.84  fof(f2762,plain,(
% 3.78/0.84    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_3 | ~spl2_5)),
% 3.78/0.84    inference(unit_resulting_resolution,[],[f107,f112,f146,f64])).
% 3.78/0.84  fof(f64,plain,(
% 3.78/0.84    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 3.78/0.84    inference(cnf_transformation,[],[f35])).
% 3.78/0.84  fof(f35,plain,(
% 3.78/0.84    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.78/0.84    inference(flattening,[],[f34])).
% 3.78/0.84  fof(f34,plain,(
% 3.78/0.84    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.78/0.84    inference(ennf_transformation,[],[f26])).
% 3.78/0.84  fof(f26,axiom,(
% 3.78/0.84    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.78/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 3.78/0.84  fof(f146,plain,(
% 3.78/0.84    v4_pre_topc(sK1,sK0) | ~spl2_5),
% 3.78/0.84    inference(avatar_component_clause,[],[f144])).
% 3.78/0.84  fof(f2759,plain,(
% 3.78/0.84    spl2_43 | ~spl2_3 | ~spl2_6),
% 3.78/0.84    inference(avatar_split_clause,[],[f403,f148,f110,f2756])).
% 3.78/0.84  fof(f403,plain,(
% 3.78/0.84    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6)),
% 3.78/0.84    inference(superposition,[],[f213,f150])).
% 3.78/0.84  fof(f150,plain,(
% 3.78/0.84    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 3.78/0.84    inference(avatar_component_clause,[],[f148])).
% 3.78/0.84  fof(f213,plain,(
% 3.78/0.84    ( ! [X0] : (k6_subset_1(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_3),
% 3.78/0.84    inference(unit_resulting_resolution,[],[f112,f96])).
% 3.78/0.84  fof(f96,plain,(
% 3.78/0.84    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)) )),
% 3.78/0.84    inference(definition_unfolding,[],[f84,f69])).
% 3.78/0.84  fof(f84,plain,(
% 3.78/0.84    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.78/0.84    inference(cnf_transformation,[],[f44])).
% 3.78/0.84  fof(f44,plain,(
% 3.78/0.84    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.78/0.84    inference(ennf_transformation,[],[f18])).
% 3.78/0.84  fof(f18,axiom,(
% 3.78/0.84    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.78/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.78/0.84  fof(f763,plain,(
% 3.78/0.84    spl2_18 | ~spl2_2 | ~spl2_3),
% 3.78/0.84    inference(avatar_split_clause,[],[f280,f110,f105,f760])).
% 3.78/0.84  fof(f280,plain,(
% 3.78/0.84    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 3.78/0.84    inference(unit_resulting_resolution,[],[f107,f112,f63])).
% 3.78/0.85  fof(f63,plain,(
% 3.78/0.85    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 3.78/0.85    inference(cnf_transformation,[],[f33])).
% 3.78/0.85  fof(f33,plain,(
% 3.78/0.85    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.78/0.85    inference(ennf_transformation,[],[f23])).
% 3.78/0.85  fof(f23,axiom,(
% 3.78/0.85    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 3.78/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 3.78/0.85  fof(f293,plain,(
% 3.78/0.85    spl2_9 | ~spl2_2 | ~spl2_3),
% 3.78/0.85    inference(avatar_split_clause,[],[f236,f110,f105,f290])).
% 3.78/0.85  fof(f236,plain,(
% 3.78/0.85    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 3.78/0.85    inference(unit_resulting_resolution,[],[f107,f112,f81])).
% 3.78/0.85  fof(f81,plain,(
% 3.78/0.85    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.78/0.85    inference(cnf_transformation,[],[f43])).
% 3.78/0.85  fof(f43,plain,(
% 3.78/0.85    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.78/0.85    inference(flattening,[],[f42])).
% 3.78/0.85  fof(f42,plain,(
% 3.78/0.85    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.78/0.85    inference(ennf_transformation,[],[f21])).
% 3.78/0.85  fof(f21,axiom,(
% 3.78/0.85    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.78/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 3.78/0.85  fof(f253,plain,(
% 3.78/0.85    spl2_7 | ~spl2_1 | ~spl2_2 | ~spl2_3),
% 3.78/0.85    inference(avatar_split_clause,[],[f231,f110,f105,f100,f250])).
% 3.78/0.85  fof(f100,plain,(
% 3.78/0.85    spl2_1 <=> v2_pre_topc(sK0)),
% 3.78/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.78/0.85  fof(f231,plain,(
% 3.78/0.85    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 3.78/0.85    inference(unit_resulting_resolution,[],[f102,f107,f112,f80])).
% 3.78/0.85  fof(f80,plain,(
% 3.78/0.85    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(k2_pre_topc(X0,X1),X0)) )),
% 3.78/0.85    inference(cnf_transformation,[],[f41])).
% 3.78/0.85  fof(f41,plain,(
% 3.78/0.85    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.78/0.85    inference(flattening,[],[f40])).
% 3.78/0.85  fof(f40,plain,(
% 3.78/0.85    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.78/0.85    inference(ennf_transformation,[],[f22])).
% 3.78/0.85  fof(f22,axiom,(
% 3.78/0.85    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 3.78/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 3.78/0.85  fof(f102,plain,(
% 3.78/0.85    v2_pre_topc(sK0) | ~spl2_1),
% 3.78/0.85    inference(avatar_component_clause,[],[f100])).
% 3.78/0.85  fof(f154,plain,(
% 3.78/0.85    ~spl2_5 | ~spl2_6),
% 3.78/0.85    inference(avatar_split_clause,[],[f153,f148,f144])).
% 3.78/0.85  fof(f153,plain,(
% 3.78/0.85    ~v4_pre_topc(sK1,sK0) | ~spl2_6),
% 3.78/0.85    inference(trivial_inequality_removal,[],[f152])).
% 3.78/0.85  fof(f152,plain,(
% 3.78/0.85    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0) | ~spl2_6),
% 3.78/0.85    inference(backward_demodulation,[],[f59,f150])).
% 3.78/0.85  fof(f59,plain,(
% 3.78/0.85    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 3.78/0.85    inference(cnf_transformation,[],[f53])).
% 3.78/0.85  fof(f53,plain,(
% 3.78/0.85    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.78/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f52,f51])).
% 3.78/0.85  fof(f51,plain,(
% 3.78/0.85    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.78/0.85    introduced(choice_axiom,[])).
% 3.78/0.85  fof(f52,plain,(
% 3.78/0.85    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.78/0.85    introduced(choice_axiom,[])).
% 3.78/0.85  fof(f50,plain,(
% 3.78/0.85    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.78/0.85    inference(flattening,[],[f49])).
% 3.78/0.85  fof(f49,plain,(
% 3.78/0.85    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.78/0.85    inference(nnf_transformation,[],[f30])).
% 3.78/0.85  fof(f30,plain,(
% 3.78/0.85    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.78/0.85    inference(flattening,[],[f29])).
% 3.78/0.85  fof(f29,plain,(
% 3.78/0.85    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.78/0.85    inference(ennf_transformation,[],[f28])).
% 3.78/0.85  fof(f28,negated_conjecture,(
% 3.78/0.85    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 3.78/0.85    inference(negated_conjecture,[],[f27])).
% 3.78/0.85  fof(f27,conjecture,(
% 3.78/0.85    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 3.78/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 3.78/0.85  fof(f151,plain,(
% 3.78/0.85    spl2_5 | spl2_6),
% 3.78/0.85    inference(avatar_split_clause,[],[f58,f148,f144])).
% 3.78/0.85  fof(f58,plain,(
% 3.78/0.85    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 3.78/0.85    inference(cnf_transformation,[],[f53])).
% 3.78/0.85  fof(f113,plain,(
% 3.78/0.85    spl2_3),
% 3.78/0.85    inference(avatar_split_clause,[],[f57,f110])).
% 3.78/0.85  fof(f57,plain,(
% 3.78/0.85    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.78/0.85    inference(cnf_transformation,[],[f53])).
% 3.78/0.85  fof(f108,plain,(
% 3.78/0.85    spl2_2),
% 3.78/0.85    inference(avatar_split_clause,[],[f56,f105])).
% 3.78/0.85  fof(f56,plain,(
% 3.78/0.85    l1_pre_topc(sK0)),
% 3.78/0.85    inference(cnf_transformation,[],[f53])).
% 3.78/0.85  fof(f103,plain,(
% 3.78/0.85    spl2_1),
% 3.78/0.85    inference(avatar_split_clause,[],[f55,f100])).
% 3.78/0.85  fof(f55,plain,(
% 3.78/0.85    v2_pre_topc(sK0)),
% 3.78/0.85    inference(cnf_transformation,[],[f53])).
% 3.78/0.85  % SZS output end Proof for theBenchmark
% 3.78/0.85  % (20673)------------------------------
% 3.78/0.85  % (20673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.78/0.85  % (20673)Termination reason: Refutation
% 3.78/0.85  
% 3.78/0.85  % (20673)Memory used [KB]: 15095
% 3.78/0.85  % (20673)Time elapsed: 0.385 s
% 3.78/0.85  % (20673)------------------------------
% 3.78/0.85  % (20673)------------------------------
% 3.78/0.85  % (20657)Success in time 0.481 s
%------------------------------------------------------------------------------
