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
% DateTime   : Thu Dec  3 13:10:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 341 expanded)
%              Number of leaves         :   35 ( 137 expanded)
%              Depth                    :    9
%              Number of atoms          :  377 ( 887 expanded)
%              Number of equality atoms :   30 ( 120 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f891,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f235,f246,f248,f266,f420,f422,f425,f428,f459,f474,f642,f739,f793,f807,f823,f866,f878])).

fof(f878,plain,
    ( ~ spl3_12
    | ~ spl3_29
    | spl3_49 ),
    inference(avatar_split_clause,[],[f868,f863,f633,f413])).

fof(f413,plain,
    ( spl3_12
  <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f633,plain,
    ( spl3_29
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f863,plain,
    ( spl3_49
  <=> r1_tarski(k3_tarski(k2_tarski(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f868,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_49 ),
    inference(resolution,[],[f865,f268])).

fof(f268,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f79,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f73,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f55,f59])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f49,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_subset_1(X1,X0,X2),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f54,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))),X2)
      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2)
      | ~ r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f64,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) ),
    inference(definition_unfolding,[],[f50,f48,f59,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f48])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f865,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2))),u1_struct_0(sK0))
    | spl3_49 ),
    inference(avatar_component_clause,[],[f863])).

fof(f866,plain,
    ( ~ spl3_11
    | ~ spl3_12
    | ~ spl3_49
    | spl3_34 ),
    inference(avatar_split_clause,[],[f856,f732,f863,f413,f409])).

fof(f409,plain,
    ( spl3_11
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f732,plain,
    ( spl3_34
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f856,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2))),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_34 ),
    inference(superposition,[],[f840,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f58,f48])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f840,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | spl3_34 ),
    inference(resolution,[],[f734,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f734,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_34 ),
    inference(avatar_component_clause,[],[f732])).

fof(f823,plain,(
    spl3_43 ),
    inference(avatar_contradiction_clause,[],[f822])).

fof(f822,plain,
    ( $false
    | spl3_43 ),
    inference(resolution,[],[f806,f60])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f806,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2)))
    | spl3_43 ),
    inference(avatar_component_clause,[],[f804])).

fof(f804,plain,
    ( spl3_43
  <=> r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f807,plain,
    ( ~ spl3_4
    | ~ spl3_43
    | spl3_41 ),
    inference(avatar_split_clause,[],[f802,f790,f804,f243])).

fof(f243,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f790,plain,
    ( spl3_41
  <=> r1_tarski(sK1,k3_tarski(k2_tarski(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f802,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_41 ),
    inference(forward_demodulation,[],[f796,f181])).

fof(f181,plain,(
    ! [X2,X3] : k3_tarski(k2_tarski(X2,X3)) = k3_tarski(k2_tarski(X3,X2)) ),
    inference(superposition,[],[f124,f61])).

fof(f124,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f77,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f77,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X1,X0)) = k3_tarski(k2_tarski(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))))) ),
    inference(superposition,[],[f61,f46])).

fof(f796,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK2,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_41 ),
    inference(superposition,[],[f792,f100])).

fof(f100,plain,(
    ! [X8,X7,X9] :
      ( k3_tarski(k2_tarski(X8,X7)) = k3_tarski(k2_tarski(X8,k7_subset_1(X9,X7,X8)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(X9)) ) ),
    inference(superposition,[],[f61,f62])).

fof(f792,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | spl3_41 ),
    inference(avatar_component_clause,[],[f790])).

fof(f793,plain,
    ( ~ spl3_11
    | ~ spl3_12
    | ~ spl3_41
    | spl3_35 ),
    inference(avatar_split_clause,[],[f783,f736,f790,f413,f409])).

fof(f736,plain,
    ( spl3_35
  <=> r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f783,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_35 ),
    inference(superposition,[],[f738,f65])).

fof(f738,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_35 ),
    inference(avatar_component_clause,[],[f736])).

fof(f739,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_34
    | ~ spl3_35
    | spl3_13 ),
    inference(avatar_split_clause,[],[f727,f417,f736,f732,f243,f239])).

fof(f239,plain,
    ( spl3_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f417,plain,
    ( spl3_13
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f727,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_13 ),
    inference(resolution,[],[f419,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f419,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f417])).

fof(f642,plain,(
    spl3_29 ),
    inference(avatar_contradiction_clause,[],[f641])).

fof(f641,plain,
    ( $false
    | spl3_29 ),
    inference(resolution,[],[f635,f71])).

fof(f71,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f52,f41])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_1)).

fof(f635,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f633])).

fof(f474,plain,
    ( ~ spl3_3
    | ~ spl3_12
    | spl3_9 ),
    inference(avatar_split_clause,[],[f470,f401,f413,f239])).

fof(f401,plain,
    ( spl3_9
  <=> m1_subset_1(k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f470,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(resolution,[],[f403,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f403,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f401])).

fof(f459,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f457])).

fof(f457,plain,
    ( $false
    | spl3_12 ),
    inference(resolution,[],[f430,f40])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f430,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_12 ),
    inference(resolution,[],[f415,f54])).

fof(f415,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f413])).

fof(f428,plain,
    ( ~ spl3_3
    | ~ spl3_11
    | spl3_8 ),
    inference(avatar_split_clause,[],[f426,f397,f409,f239])).

fof(f397,plain,
    ( spl3_8
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f426,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_8 ),
    inference(resolution,[],[f399,f51])).

fof(f399,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f397])).

fof(f425,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f423])).

fof(f423,plain,
    ( $false
    | spl3_11 ),
    inference(resolution,[],[f411,f41])).

fof(f411,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f409])).

fof(f422,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f421])).

fof(f421,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f407,f38])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f407,plain,
    ( ~ v2_pre_topc(sK0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f405])).

fof(f405,plain,
    ( spl3_10
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f420,plain,
    ( ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | spl3_2 ),
    inference(avatar_split_clause,[],[f383,f232,f417,f413,f409,f239,f405,f401,f397])).

fof(f232,plain,
    ( spl3_2
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f383,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2 ),
    inference(superposition,[],[f234,f111])).

fof(f111,plain,(
    ! [X4,X5,X3] :
      ( k3_tarski(k2_tarski(k2_pre_topc(X3,X4),k2_pre_topc(X3,X5))) = k2_pre_topc(X3,k4_subset_1(u1_struct_0(X3),X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | ~ m1_subset_1(k2_pre_topc(X3,X5),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(k2_pre_topc(X3,X4),k1_zfmisc_1(u1_struct_0(X3))) ) ),
    inference(superposition,[],[f44,f65])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_pre_topc)).

fof(f234,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f232])).

fof(f266,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f245,f40])).

fof(f245,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f243])).

fof(f248,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f241,f39])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f241,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f239])).

fof(f246,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f236,f228,f243,f239])).

fof(f228,plain,
    ( spl3_1
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f236,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(resolution,[],[f230,f51])).

fof(f230,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f228])).

fof(f235,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f222,f232,f228])).

fof(f222,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f99,f42])).

fof(f42,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f99,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_tarski(k7_subset_1(X5,X3,X4),X6)
      | ~ r1_tarski(X3,k3_tarski(k2_tarski(X4,X6)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X5)) ) ),
    inference(superposition,[],[f63,f62])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2)
      | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f56,f59,f48])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:24:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (6252)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (6254)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (6246)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (6247)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (6245)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (6244)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (6249)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (6240)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (6251)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (6241)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (6243)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (6242)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (6248)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (6257)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (6250)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (6255)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (6244)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f891,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f235,f246,f248,f266,f420,f422,f425,f428,f459,f474,f642,f739,f793,f807,f823,f866,f878])).
% 0.21/0.51  fof(f878,plain,(
% 0.21/0.51    ~spl3_12 | ~spl3_29 | spl3_49),
% 0.21/0.51    inference(avatar_split_clause,[],[f868,f863,f633,f413])).
% 0.21/0.51  fof(f413,plain,(
% 0.21/0.51    spl3_12 <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.51  fof(f633,plain,(
% 0.21/0.51    spl3_29 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.51  fof(f863,plain,(
% 0.21/0.51    spl3_49 <=> r1_tarski(k3_tarski(k2_tarski(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2))),u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.21/0.51  fof(f868,plain,(
% 0.21/0.51    ~r1_tarski(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_49),
% 0.21/0.51    inference(resolution,[],[f865,f268])).
% 0.21/0.51  fof(f268,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2) | ~r1_tarski(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) )),
% 0.21/0.51    inference(resolution,[],[f79,f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(superposition,[],[f73,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f55,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f49,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k7_subset_1(X1,X0,X2),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(resolution,[],[f54,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))),X2) | r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2) | ~r1_tarski(X0,X2)) )),
% 0.21/0.51    inference(superposition,[],[f64,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f50,f48,f59,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f57,f48])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.51  fof(f865,plain,(
% 0.21/0.51    ~r1_tarski(k3_tarski(k2_tarski(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2))),u1_struct_0(sK0)) | spl3_49),
% 0.21/0.51    inference(avatar_component_clause,[],[f863])).
% 0.21/0.51  fof(f866,plain,(
% 0.21/0.51    ~spl3_11 | ~spl3_12 | ~spl3_49 | spl3_34),
% 0.21/0.51    inference(avatar_split_clause,[],[f856,f732,f863,f413,f409])).
% 0.21/0.51  fof(f409,plain,(
% 0.21/0.51    spl3_11 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.51  fof(f732,plain,(
% 0.21/0.51    spl3_34 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.51  fof(f856,plain,(
% 0.21/0.51    ~r1_tarski(k3_tarski(k2_tarski(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2))),u1_struct_0(sK0)) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_34),
% 0.21/0.51    inference(superposition,[],[f840,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f58,f48])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(flattening,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.51  fof(f840,plain,(
% 0.21/0.51    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0)) | spl3_34),
% 0.21/0.51    inference(resolution,[],[f734,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f734,plain,(
% 0.21/0.51    ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_34),
% 0.21/0.51    inference(avatar_component_clause,[],[f732])).
% 0.21/0.51  fof(f823,plain,(
% 0.21/0.51    spl3_43),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f822])).
% 0.21/0.51  fof(f822,plain,(
% 0.21/0.51    $false | spl3_43),
% 0.21/0.51    inference(resolution,[],[f806,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f45,f48])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.51  fof(f806,plain,(
% 0.21/0.51    ~r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2))) | spl3_43),
% 0.21/0.51    inference(avatar_component_clause,[],[f804])).
% 0.21/0.51  fof(f804,plain,(
% 0.21/0.51    spl3_43 <=> r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.51  fof(f807,plain,(
% 0.21/0.51    ~spl3_4 | ~spl3_43 | spl3_41),
% 0.21/0.51    inference(avatar_split_clause,[],[f802,f790,f804,f243])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f790,plain,(
% 0.21/0.51    spl3_41 <=> r1_tarski(sK1,k3_tarski(k2_tarski(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.51  fof(f802,plain,(
% 0.21/0.51    ~r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_41),
% 0.21/0.51    inference(forward_demodulation,[],[f796,f181])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k3_tarski(k2_tarski(X2,X3)) = k3_tarski(k2_tarski(X3,X2))) )),
% 0.21/0.51    inference(superposition,[],[f124,f61])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) = k3_tarski(k2_tarski(X1,X0))) )),
% 0.21/0.51    inference(superposition,[],[f77,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_tarski(k2_tarski(X1,X0)) = k3_tarski(k2_tarski(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))))) )),
% 0.21/0.51    inference(superposition,[],[f61,f46])).
% 0.21/0.51  fof(f796,plain,(
% 0.21/0.51    ~r1_tarski(sK1,k3_tarski(k2_tarski(sK2,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_41),
% 0.21/0.51    inference(superposition,[],[f792,f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X8,X7,X9] : (k3_tarski(k2_tarski(X8,X7)) = k3_tarski(k2_tarski(X8,k7_subset_1(X9,X7,X8))) | ~m1_subset_1(X7,k1_zfmisc_1(X9))) )),
% 0.21/0.51    inference(superposition,[],[f61,f62])).
% 0.21/0.51  fof(f792,plain,(
% 0.21/0.51    ~r1_tarski(sK1,k3_tarski(k2_tarski(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))) | spl3_41),
% 0.21/0.51    inference(avatar_component_clause,[],[f790])).
% 0.21/0.51  fof(f793,plain,(
% 0.21/0.51    ~spl3_11 | ~spl3_12 | ~spl3_41 | spl3_35),
% 0.21/0.51    inference(avatar_split_clause,[],[f783,f736,f790,f413,f409])).
% 0.21/0.51  fof(f736,plain,(
% 0.21/0.51    spl3_35 <=> r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.51  fof(f783,plain,(
% 0.21/0.51    ~r1_tarski(sK1,k3_tarski(k2_tarski(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_35),
% 0.21/0.51    inference(superposition,[],[f738,f65])).
% 0.21/0.51  fof(f738,plain,(
% 0.21/0.51    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_35),
% 0.21/0.51    inference(avatar_component_clause,[],[f736])).
% 0.21/0.51  fof(f739,plain,(
% 0.21/0.51    ~spl3_3 | ~spl3_4 | ~spl3_34 | ~spl3_35 | spl3_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f727,f417,f736,f732,f243,f239])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    spl3_3 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.51  fof(f417,plain,(
% 0.21/0.51    spl3_13 <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.51  fof(f727,plain,(
% 0.21/0.51    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_13),
% 0.21/0.51    inference(resolution,[],[f419,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).
% 0.21/0.51  fof(f419,plain,(
% 0.21/0.51    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))) | spl3_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f417])).
% 0.21/0.51  fof(f642,plain,(
% 0.21/0.51    spl3_29),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f641])).
% 0.21/0.51  fof(f641,plain,(
% 0.21/0.51    $false | spl3_29),
% 0.21/0.51    inference(resolution,[],[f635,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    r1_tarski(sK2,u1_struct_0(sK0))),
% 0.21/0.51    inference(resolution,[],[f52,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ((~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f35,f34,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f16])).
% 0.21/0.51  fof(f16,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_1)).
% 0.21/0.51  fof(f635,plain,(
% 0.21/0.51    ~r1_tarski(sK2,u1_struct_0(sK0)) | spl3_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f633])).
% 0.21/0.51  fof(f474,plain,(
% 0.21/0.51    ~spl3_3 | ~spl3_12 | spl3_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f470,f401,f413,f239])).
% 0.21/0.51  fof(f401,plain,(
% 0.21/0.51    spl3_9 <=> m1_subset_1(k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.51  fof(f470,plain,(
% 0.21/0.51    ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_9),
% 0.21/0.51    inference(resolution,[],[f403,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.51  fof(f403,plain,(
% 0.21/0.51    ~m1_subset_1(k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f401])).
% 0.21/0.51  fof(f459,plain,(
% 0.21/0.51    spl3_12),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f457])).
% 0.21/0.51  fof(f457,plain,(
% 0.21/0.51    $false | spl3_12),
% 0.21/0.51    inference(resolution,[],[f430,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f430,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_12),
% 0.21/0.51    inference(resolution,[],[f415,f54])).
% 0.21/0.51  fof(f415,plain,(
% 0.21/0.51    ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f413])).
% 0.21/0.51  fof(f428,plain,(
% 0.21/0.51    ~spl3_3 | ~spl3_11 | spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f426,f397,f409,f239])).
% 0.21/0.51  fof(f397,plain,(
% 0.21/0.51    spl3_8 <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.51  fof(f426,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_8),
% 0.21/0.51    inference(resolution,[],[f399,f51])).
% 0.21/0.51  fof(f399,plain,(
% 0.21/0.51    ~m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f397])).
% 0.21/0.51  fof(f425,plain,(
% 0.21/0.51    spl3_11),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f423])).
% 0.21/0.51  fof(f423,plain,(
% 0.21/0.51    $false | spl3_11),
% 0.21/0.51    inference(resolution,[],[f411,f41])).
% 0.21/0.51  fof(f411,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f409])).
% 0.21/0.51  fof(f422,plain,(
% 0.21/0.51    spl3_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f421])).
% 0.21/0.51  fof(f421,plain,(
% 0.21/0.51    $false | spl3_10),
% 0.21/0.51    inference(resolution,[],[f407,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f407,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | spl3_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f405])).
% 0.21/0.51  fof(f405,plain,(
% 0.21/0.51    spl3_10 <=> v2_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.51  fof(f420,plain,(
% 0.21/0.51    ~spl3_8 | ~spl3_9 | ~spl3_10 | ~spl3_3 | ~spl3_11 | ~spl3_12 | ~spl3_13 | spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f383,f232,f417,f413,f409,f239,f405,f401,f397])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    spl3_2 <=> r1_tarski(k2_pre_topc(sK0,sK1),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f383,plain,(
% 0.21/0.51    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))) | ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_2),
% 0.21/0.51    inference(superposition,[],[f234,f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (k3_tarski(k2_tarski(k2_pre_topc(X3,X4),k2_pre_topc(X3,X5))) = k2_pre_topc(X3,k4_subset_1(u1_struct_0(X3),X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | ~m1_subset_1(k2_pre_topc(X3,X5),k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(k2_pre_topc(X3,X4),k1_zfmisc_1(u1_struct_0(X3)))) )),
% 0.21/0.51    inference(superposition,[],[f44,f65])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_pre_topc)).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    ~r1_tarski(k2_pre_topc(sK0,sK1),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))))) | spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f232])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    spl3_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f264])).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    $false | spl3_4),
% 0.21/0.51    inference(resolution,[],[f245,f40])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f243])).
% 0.21/0.51  fof(f248,plain,(
% 0.21/0.51    spl3_3),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f247])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    $false | spl3_3),
% 0.21/0.51    inference(resolution,[],[f241,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f241,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | spl3_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f239])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    ~spl3_3 | ~spl3_4 | spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f236,f228,f243,f239])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    spl3_1 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_1),
% 0.21/0.51    inference(resolution,[],[f230,f51])).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f228])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    ~spl3_1 | ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f222,f232,f228])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    ~r1_tarski(k2_pre_topc(sK0,sK1),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))))) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(resolution,[],[f99,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ( ! [X6,X4,X5,X3] : (r1_tarski(k7_subset_1(X5,X3,X4),X6) | ~r1_tarski(X3,k3_tarski(k2_tarski(X4,X6))) | ~m1_subset_1(X3,k1_zfmisc_1(X5))) )),
% 0.21/0.51    inference(superposition,[],[f63,f62])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f56,f59,f48])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (6244)------------------------------
% 0.21/0.51  % (6244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6244)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (6244)Memory used [KB]: 6524
% 0.21/0.51  % (6244)Time elapsed: 0.083 s
% 0.21/0.51  % (6244)------------------------------
% 0.21/0.51  % (6244)------------------------------
% 0.21/0.51  % (6253)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (6239)Success in time 0.148 s
%------------------------------------------------------------------------------
