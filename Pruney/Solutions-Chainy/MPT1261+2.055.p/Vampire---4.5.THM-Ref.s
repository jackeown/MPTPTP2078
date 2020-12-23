%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:56 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 419 expanded)
%              Number of leaves         :   37 ( 157 expanded)
%              Depth                    :   13
%              Number of atoms          :  394 (1063 expanded)
%              Number of equality atoms :  113 ( 400 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1718,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f94,f294,f296,f298,f355,f358,f705,f964,f1069,f1305,f1342,f1463,f1559,f1572,f1712,f1717])).

fof(f1717,plain,
    ( ~ spl2_3
    | ~ spl2_6
    | spl2_42 ),
    inference(avatar_split_clause,[],[f1715,f1708,f348,f283])).

fof(f283,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f348,plain,
    ( spl2_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f1708,plain,
    ( spl2_42
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f1715,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_42 ),
    inference(resolution,[],[f1710,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f1710,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_42 ),
    inference(avatar_component_clause,[],[f1708])).

fof(f1712,plain,
    ( ~ spl2_3
    | ~ spl2_6
    | ~ spl2_42
    | spl2_5
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f1697,f1568,f291,f1708,f348,f283])).

fof(f291,plain,
    ( spl2_5
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1568,plain,
    ( spl2_30
  <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f1697,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_30 ),
    inference(superposition,[],[f301,f1618])).

fof(f1618,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f1617,f99])).

fof(f99,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f76,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f52,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f76,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f53,f74])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f66,f62])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1617,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f1596,f269])).

fof(f269,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f114,f254])).

fof(f254,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f253,f99])).

fof(f253,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k1_setfam_1(k2_tarski(X0,X0)) ),
    inference(forward_demodulation,[],[f235,f75])).

fof(f235,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k1_setfam_1(k2_tarski(X0,X0)) ),
    inference(superposition,[],[f80,f114])).

fof(f80,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f64,f62,f74,f74])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f114,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) ),
    inference(superposition,[],[f79,f77])).

fof(f77,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f58,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f58,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f79,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) ),
    inference(definition_unfolding,[],[f60,f74,f63])).

fof(f60,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f1596,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_30 ),
    inference(superposition,[],[f121,f1570])).

fof(f1570,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f1568])).

fof(f121,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(superposition,[],[f81,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f81,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f65,f63,f74])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f301,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f300])).

fof(f300,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f84,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f73,f63])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1572,plain,
    ( ~ spl2_23
    | spl2_30
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f1562,f1556,f1568,f1297])).

fof(f1297,plain,
    ( spl2_23
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f1556,plain,
    ( spl2_29
  <=> k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f1562,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_29 ),
    inference(superposition,[],[f68,f1558])).

fof(f1558,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f1556])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1559,plain,
    ( ~ spl2_27
    | spl2_29
    | ~ spl2_20
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f1528,f1301,f1066,f1556,f1447])).

fof(f1447,plain,
    ( spl2_27
  <=> m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f1066,plain,
    ( spl2_20
  <=> k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f1301,plain,
    ( spl2_24
  <=> k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f1528,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl2_20
    | ~ spl2_24 ),
    inference(superposition,[],[f244,f1375])).

fof(f1375,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_20
    | ~ spl2_24 ),
    inference(backward_demodulation,[],[f1068,f1303])).

fof(f1303,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f1301])).

fof(f1068,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f1066])).

fof(f244,plain,(
    ! [X6,X5] :
      ( k1_setfam_1(k2_tarski(X5,X6)) = k3_subset_1(X5,k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6))))
      | ~ m1_subset_1(k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6))),k1_zfmisc_1(X5)) ) ),
    inference(superposition,[],[f80,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f67,f74])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1463,plain,
    ( ~ spl2_24
    | spl2_27 ),
    inference(avatar_contradiction_clause,[],[f1461])).

fof(f1461,plain,
    ( $false
    | ~ spl2_24
    | spl2_27 ),
    inference(resolution,[],[f1460,f1388])).

fof(f1388,plain,
    ( r1_tarski(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),sK1)
    | ~ spl2_24 ),
    inference(superposition,[],[f249,f1303])).

fof(f249,plain,(
    ! [X8,X7] : r1_tarski(k1_setfam_1(k2_tarski(X7,X8)),X7) ),
    inference(superposition,[],[f78,f80])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f59,f74])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1460,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),sK1)
    | spl2_27 ),
    inference(resolution,[],[f1449,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1449,plain,
    ( ~ m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | spl2_27 ),
    inference(avatar_component_clause,[],[f1447])).

fof(f1342,plain,
    ( ~ spl2_7
    | spl2_23 ),
    inference(avatar_contradiction_clause,[],[f1341])).

fof(f1341,plain,
    ( $false
    | ~ spl2_7
    | spl2_23 ),
    inference(resolution,[],[f1307,f354])).

fof(f354,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl2_7
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f1307,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_23 ),
    inference(resolution,[],[f1299,f71])).

fof(f1299,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_23 ),
    inference(avatar_component_clause,[],[f1297])).

fof(f1305,plain,
    ( ~ spl2_23
    | spl2_24
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f1293,f1066,f1301,f1297])).

fof(f1293,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_20 ),
    inference(superposition,[],[f82,f1068])).

fof(f1069,plain,
    ( ~ spl2_6
    | spl2_20
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f1034,f90,f1066,f348])).

fof(f90,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1034,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f236,f91])).

fof(f91,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f236,plain,(
    ! [X2,X3,X1] :
      ( k1_setfam_1(k2_tarski(X1,X2)) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k7_subset_1(X3,X1,X2))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f80,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f72,f74])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f964,plain,
    ( ~ spl2_3
    | ~ spl2_6
    | spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f961,f291,f90,f348,f283])).

fof(f961,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(superposition,[],[f55,f292])).

fof(f292,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f291])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f705,plain,
    ( ~ spl2_3
    | spl2_5
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f195,f86,f291,f283])).

fof(f86,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f195,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f56,f49])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).

fof(f44,plain,
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

fof(f45,plain,
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

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f358,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f356])).

fof(f356,plain,
    ( $false
    | spl2_6 ),
    inference(resolution,[],[f350,f49])).

fof(f350,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f348])).

fof(f355,plain,
    ( ~ spl2_6
    | spl2_7
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f343,f90,f352,f348])).

fof(f343,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f215,f91])).

fof(f215,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k7_subset_1(X8,X6,X7),X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X8)) ) ),
    inference(superposition,[],[f78,f83])).

fof(f298,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f289,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f289,plain,
    ( ~ v2_pre_topc(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl2_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f296,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f285,f48])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f285,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f283])).

fof(f294,plain,
    ( ~ spl2_3
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f278,f291,f287,f86,f283])).

fof(f278,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f57,f49])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f94,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f50,f90,f86])).

fof(f50,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f51,f90,f86])).

fof(f51,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:25:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (19313)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.46  % (19304)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (19305)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (19303)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (19307)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (19301)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (19312)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (19299)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (19302)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (19298)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (19309)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (19315)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (19308)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (19306)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (19311)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (19310)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.52  % (19300)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 1.38/0.53  % (19314)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.38/0.54  % (19302)Refutation found. Thanks to Tanya!
% 1.38/0.54  % SZS status Theorem for theBenchmark
% 1.38/0.54  % SZS output start Proof for theBenchmark
% 1.38/0.54  fof(f1718,plain,(
% 1.38/0.54    $false),
% 1.38/0.54    inference(avatar_sat_refutation,[],[f93,f94,f294,f296,f298,f355,f358,f705,f964,f1069,f1305,f1342,f1463,f1559,f1572,f1712,f1717])).
% 1.38/0.54  fof(f1717,plain,(
% 1.38/0.54    ~spl2_3 | ~spl2_6 | spl2_42),
% 1.38/0.54    inference(avatar_split_clause,[],[f1715,f1708,f348,f283])).
% 1.38/0.54  fof(f283,plain,(
% 1.38/0.54    spl2_3 <=> l1_pre_topc(sK0)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.38/0.54  fof(f348,plain,(
% 1.38/0.54    spl2_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.38/0.54  fof(f1708,plain,(
% 1.38/0.54    spl2_42 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 1.38/0.54  fof(f1715,plain,(
% 1.38/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_42),
% 1.38/0.54    inference(resolution,[],[f1710,f70])).
% 1.38/0.54  fof(f70,plain,(
% 1.38/0.54    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f37])).
% 1.38/0.54  fof(f37,plain,(
% 1.38/0.54    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(flattening,[],[f36])).
% 1.38/0.54  fof(f36,plain,(
% 1.38/0.54    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f18])).
% 1.38/0.54  fof(f18,axiom,(
% 1.38/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.38/0.54  fof(f1710,plain,(
% 1.38/0.54    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_42),
% 1.38/0.54    inference(avatar_component_clause,[],[f1708])).
% 1.38/0.54  fof(f1712,plain,(
% 1.38/0.54    ~spl2_3 | ~spl2_6 | ~spl2_42 | spl2_5 | ~spl2_30),
% 1.38/0.54    inference(avatar_split_clause,[],[f1697,f1568,f291,f1708,f348,f283])).
% 1.38/0.54  fof(f291,plain,(
% 1.38/0.54    spl2_5 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.38/0.54  fof(f1568,plain,(
% 1.38/0.54    spl2_30 <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 1.38/0.54  fof(f1697,plain,(
% 1.38/0.54    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_30),
% 1.38/0.54    inference(superposition,[],[f301,f1618])).
% 1.38/0.54  fof(f1618,plain,(
% 1.38/0.54    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_30),
% 1.38/0.54    inference(forward_demodulation,[],[f1617,f99])).
% 1.38/0.54  fof(f99,plain,(
% 1.38/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.38/0.54    inference(forward_demodulation,[],[f76,f75])).
% 1.38/0.54  fof(f75,plain,(
% 1.38/0.54    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.38/0.54    inference(definition_unfolding,[],[f52,f62])).
% 1.38/0.54  fof(f62,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f15])).
% 1.38/0.54  fof(f15,axiom,(
% 1.38/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.38/0.54  fof(f52,plain,(
% 1.38/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f3])).
% 1.38/0.54  fof(f3,axiom,(
% 1.38/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.38/0.54  fof(f76,plain,(
% 1.38/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 1.38/0.54    inference(definition_unfolding,[],[f53,f74])).
% 1.38/0.54  fof(f74,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.38/0.54    inference(definition_unfolding,[],[f66,f62])).
% 1.38/0.54  fof(f66,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f2])).
% 1.38/0.54  fof(f2,axiom,(
% 1.38/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.38/0.54  fof(f53,plain,(
% 1.38/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.38/0.54    inference(cnf_transformation,[],[f5])).
% 1.38/0.54  fof(f5,axiom,(
% 1.38/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.38/0.54  fof(f1617,plain,(
% 1.38/0.54    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_xboole_0) | ~spl2_30),
% 1.38/0.54    inference(forward_demodulation,[],[f1596,f269])).
% 1.38/0.54  fof(f269,plain,(
% 1.38/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.38/0.54    inference(backward_demodulation,[],[f114,f254])).
% 1.38/0.54  fof(f254,plain,(
% 1.38/0.54    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 1.38/0.54    inference(forward_demodulation,[],[f253,f99])).
% 1.38/0.54  fof(f253,plain,(
% 1.38/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k1_setfam_1(k2_tarski(X0,X0))) )),
% 1.38/0.54    inference(forward_demodulation,[],[f235,f75])).
% 1.38/0.54  fof(f235,plain,(
% 1.38/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k1_setfam_1(k2_tarski(X0,X0))) )),
% 1.38/0.54    inference(superposition,[],[f80,f114])).
% 1.38/0.54  fof(f80,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 1.38/0.54    inference(definition_unfolding,[],[f64,f62,f74,f74])).
% 1.38/0.54  fof(f64,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f7])).
% 1.38/0.54  fof(f7,axiom,(
% 1.38/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.38/0.54  fof(f114,plain,(
% 1.38/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0)))) )),
% 1.38/0.54    inference(superposition,[],[f79,f77])).
% 1.38/0.54  fof(f77,plain,(
% 1.38/0.54    ( ! [X0] : (k3_tarski(k2_tarski(X0,X0)) = X0) )),
% 1.38/0.54    inference(definition_unfolding,[],[f58,f63])).
% 1.38/0.54  fof(f63,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f10])).
% 1.38/0.54  fof(f10,axiom,(
% 1.38/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.38/0.54  fof(f58,plain,(
% 1.38/0.54    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.38/0.54    inference(cnf_transformation,[],[f24])).
% 1.38/0.54  fof(f24,plain,(
% 1.38/0.54    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.38/0.54    inference(rectify,[],[f1])).
% 1.38/0.54  fof(f1,axiom,(
% 1.38/0.54    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.38/0.54  fof(f79,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))))) )),
% 1.38/0.54    inference(definition_unfolding,[],[f60,f74,f63])).
% 1.38/0.54  fof(f60,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f6])).
% 1.38/0.54  fof(f6,axiom,(
% 1.38/0.54    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.38/0.54  fof(f1596,plain,(
% 1.38/0.54    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) | ~spl2_30),
% 1.38/0.54    inference(superposition,[],[f121,f1570])).
% 1.38/0.54  fof(f1570,plain,(
% 1.38/0.54    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_30),
% 1.38/0.54    inference(avatar_component_clause,[],[f1568])).
% 1.38/0.54  fof(f121,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 1.38/0.54    inference(superposition,[],[f81,f61])).
% 1.38/0.54  fof(f61,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f9])).
% 1.38/0.54  fof(f9,axiom,(
% 1.38/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.38/0.54  fof(f81,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 1.38/0.54    inference(definition_unfolding,[],[f65,f63,f74])).
% 1.38/0.54  fof(f65,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f8])).
% 1.38/0.54  fof(f8,axiom,(
% 1.38/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.38/0.54  fof(f301,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(duplicate_literal_removal,[],[f300])).
% 1.38/0.54  fof(f300,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(superposition,[],[f84,f54])).
% 1.38/0.54  fof(f54,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f28])).
% 1.38/0.54  fof(f28,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f21])).
% 1.38/0.54  fof(f21,axiom,(
% 1.38/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.38/0.54  fof(f84,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.38/0.54    inference(definition_unfolding,[],[f73,f63])).
% 1.38/0.54  fof(f73,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f41])).
% 1.38/0.54  fof(f41,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.54    inference(flattening,[],[f40])).
% 1.38/0.54  fof(f40,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.38/0.54    inference(ennf_transformation,[],[f13])).
% 1.38/0.54  fof(f13,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.38/0.54  fof(f1572,plain,(
% 1.38/0.54    ~spl2_23 | spl2_30 | ~spl2_29),
% 1.38/0.54    inference(avatar_split_clause,[],[f1562,f1556,f1568,f1297])).
% 1.38/0.54  fof(f1297,plain,(
% 1.38/0.54    spl2_23 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 1.38/0.54  fof(f1556,plain,(
% 1.38/0.54    spl2_29 <=> k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 1.38/0.54  fof(f1562,plain,(
% 1.38/0.54    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_29),
% 1.38/0.54    inference(superposition,[],[f68,f1558])).
% 1.38/0.54  fof(f1558,plain,(
% 1.38/0.54    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_29),
% 1.38/0.54    inference(avatar_component_clause,[],[f1556])).
% 1.38/0.54  fof(f68,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f33])).
% 1.38/0.54  fof(f33,plain,(
% 1.38/0.54    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f12])).
% 1.38/0.54  fof(f12,axiom,(
% 1.38/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.38/0.54  fof(f1559,plain,(
% 1.38/0.54    ~spl2_27 | spl2_29 | ~spl2_20 | ~spl2_24),
% 1.38/0.54    inference(avatar_split_clause,[],[f1528,f1301,f1066,f1556,f1447])).
% 1.38/0.54  fof(f1447,plain,(
% 1.38/0.54    spl2_27 <=> m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 1.38/0.54  fof(f1066,plain,(
% 1.38/0.54    spl2_20 <=> k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 1.38/0.54  fof(f1301,plain,(
% 1.38/0.54    spl2_24 <=> k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 1.38/0.54  fof(f1528,plain,(
% 1.38/0.54    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | (~spl2_20 | ~spl2_24)),
% 1.38/0.54    inference(superposition,[],[f244,f1375])).
% 1.38/0.54  fof(f1375,plain,(
% 1.38/0.54    k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_20 | ~spl2_24)),
% 1.38/0.54    inference(backward_demodulation,[],[f1068,f1303])).
% 1.38/0.54  fof(f1303,plain,(
% 1.38/0.54    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_24),
% 1.38/0.54    inference(avatar_component_clause,[],[f1301])).
% 1.38/0.54  fof(f1068,plain,(
% 1.38/0.54    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) | ~spl2_20),
% 1.38/0.54    inference(avatar_component_clause,[],[f1066])).
% 1.38/0.54  fof(f244,plain,(
% 1.38/0.54    ( ! [X6,X5] : (k1_setfam_1(k2_tarski(X5,X6)) = k3_subset_1(X5,k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6)))) | ~m1_subset_1(k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X6))),k1_zfmisc_1(X5))) )),
% 1.38/0.54    inference(superposition,[],[f80,f82])).
% 1.38/0.54  fof(f82,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.38/0.54    inference(definition_unfolding,[],[f67,f74])).
% 1.38/0.54  fof(f67,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f32])).
% 1.38/0.54  fof(f32,plain,(
% 1.38/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f11])).
% 1.38/0.54  fof(f11,axiom,(
% 1.38/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.38/0.54  fof(f1463,plain,(
% 1.38/0.54    ~spl2_24 | spl2_27),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f1461])).
% 1.38/0.54  fof(f1461,plain,(
% 1.38/0.54    $false | (~spl2_24 | spl2_27)),
% 1.38/0.54    inference(resolution,[],[f1460,f1388])).
% 1.38/0.54  fof(f1388,plain,(
% 1.38/0.54    r1_tarski(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),sK1) | ~spl2_24),
% 1.38/0.54    inference(superposition,[],[f249,f1303])).
% 1.38/0.54  fof(f249,plain,(
% 1.38/0.54    ( ! [X8,X7] : (r1_tarski(k1_setfam_1(k2_tarski(X7,X8)),X7)) )),
% 1.38/0.54    inference(superposition,[],[f78,f80])).
% 1.38/0.54  fof(f78,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 1.38/0.54    inference(definition_unfolding,[],[f59,f74])).
% 1.38/0.54  fof(f59,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f4])).
% 1.38/0.54  fof(f4,axiom,(
% 1.38/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.38/0.54  fof(f1460,plain,(
% 1.38/0.54    ~r1_tarski(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),sK1) | spl2_27),
% 1.38/0.54    inference(resolution,[],[f1449,f71])).
% 1.38/0.54  fof(f71,plain,(
% 1.38/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f38])).
% 1.38/0.54  fof(f38,plain,(
% 1.38/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.38/0.54    inference(ennf_transformation,[],[f25])).
% 1.38/0.54  fof(f25,plain,(
% 1.38/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.38/0.54    inference(unused_predicate_definition_removal,[],[f16])).
% 1.38/0.54  fof(f16,axiom,(
% 1.38/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.38/0.54  fof(f1449,plain,(
% 1.38/0.54    ~m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | spl2_27),
% 1.38/0.54    inference(avatar_component_clause,[],[f1447])).
% 1.38/0.54  fof(f1342,plain,(
% 1.38/0.54    ~spl2_7 | spl2_23),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f1341])).
% 1.38/0.54  fof(f1341,plain,(
% 1.38/0.54    $false | (~spl2_7 | spl2_23)),
% 1.38/0.54    inference(resolution,[],[f1307,f354])).
% 1.38/0.54  fof(f354,plain,(
% 1.38/0.54    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_7),
% 1.38/0.54    inference(avatar_component_clause,[],[f352])).
% 1.38/0.54  fof(f352,plain,(
% 1.38/0.54    spl2_7 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.38/0.54  fof(f1307,plain,(
% 1.38/0.54    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_23),
% 1.38/0.54    inference(resolution,[],[f1299,f71])).
% 1.38/0.54  fof(f1299,plain,(
% 1.38/0.54    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_23),
% 1.38/0.54    inference(avatar_component_clause,[],[f1297])).
% 1.38/0.54  fof(f1305,plain,(
% 1.38/0.54    ~spl2_23 | spl2_24 | ~spl2_20),
% 1.38/0.54    inference(avatar_split_clause,[],[f1293,f1066,f1301,f1297])).
% 1.38/0.54  fof(f1293,plain,(
% 1.38/0.54    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_20),
% 1.38/0.54    inference(superposition,[],[f82,f1068])).
% 1.38/0.54  fof(f1069,plain,(
% 1.38/0.54    ~spl2_6 | spl2_20 | ~spl2_2),
% 1.38/0.54    inference(avatar_split_clause,[],[f1034,f90,f1066,f348])).
% 1.38/0.54  fof(f90,plain,(
% 1.38/0.54    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.38/0.54  fof(f1034,plain,(
% 1.38/0.54    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.38/0.54    inference(superposition,[],[f236,f91])).
% 1.38/0.54  fof(f91,plain,(
% 1.38/0.54    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 1.38/0.54    inference(avatar_component_clause,[],[f90])).
% 1.38/0.54  fof(f236,plain,(
% 1.38/0.54    ( ! [X2,X3,X1] : (k1_setfam_1(k2_tarski(X1,X2)) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k7_subset_1(X3,X1,X2)))) | ~m1_subset_1(X1,k1_zfmisc_1(X3))) )),
% 1.38/0.54    inference(superposition,[],[f80,f83])).
% 1.38/0.54  fof(f83,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.38/0.54    inference(definition_unfolding,[],[f72,f74])).
% 1.38/0.54  fof(f72,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f39])).
% 1.38/0.54  fof(f39,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f14])).
% 1.38/0.54  fof(f14,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.38/0.54  fof(f964,plain,(
% 1.38/0.54    ~spl2_3 | ~spl2_6 | spl2_2 | ~spl2_5),
% 1.38/0.54    inference(avatar_split_clause,[],[f961,f291,f90,f348,f283])).
% 1.38/0.54  fof(f961,plain,(
% 1.38/0.54    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_5),
% 1.38/0.54    inference(superposition,[],[f55,f292])).
% 1.38/0.54  fof(f292,plain,(
% 1.38/0.54    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_5),
% 1.38/0.54    inference(avatar_component_clause,[],[f291])).
% 1.38/0.54  fof(f55,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f29])).
% 1.38/0.54  fof(f29,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f20])).
% 1.38/0.54  fof(f20,axiom,(
% 1.38/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 1.38/0.54  fof(f705,plain,(
% 1.38/0.54    ~spl2_3 | spl2_5 | ~spl2_1),
% 1.38/0.54    inference(avatar_split_clause,[],[f195,f86,f291,f283])).
% 1.38/0.54  fof(f86,plain,(
% 1.38/0.54    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.38/0.54  fof(f195,plain,(
% 1.38/0.54    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.38/0.54    inference(resolution,[],[f56,f49])).
% 1.38/0.54  fof(f49,plain,(
% 1.38/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.38/0.54    inference(cnf_transformation,[],[f46])).
% 1.38/0.54  fof(f46,plain,(
% 1.38/0.54    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).
% 1.38/0.54  fof(f44,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f45,plain,(
% 1.38/0.54    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f43,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.38/0.54    inference(flattening,[],[f42])).
% 1.38/0.54  fof(f42,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.38/0.54    inference(nnf_transformation,[],[f27])).
% 1.38/0.54  fof(f27,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.38/0.54    inference(flattening,[],[f26])).
% 1.38/0.54  fof(f26,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f23])).
% 1.38/0.54  fof(f23,negated_conjecture,(
% 1.38/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.38/0.54    inference(negated_conjecture,[],[f22])).
% 1.38/0.54  fof(f22,conjecture,(
% 1.38/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 1.38/0.54  fof(f56,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f31])).
% 1.38/0.54  fof(f31,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(flattening,[],[f30])).
% 1.38/0.54  fof(f30,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f17])).
% 1.38/0.54  fof(f17,axiom,(
% 1.38/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.38/0.54  fof(f358,plain,(
% 1.38/0.54    spl2_6),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f356])).
% 1.38/0.54  fof(f356,plain,(
% 1.38/0.54    $false | spl2_6),
% 1.38/0.54    inference(resolution,[],[f350,f49])).
% 1.38/0.54  fof(f350,plain,(
% 1.38/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_6),
% 1.38/0.54    inference(avatar_component_clause,[],[f348])).
% 1.38/0.54  fof(f355,plain,(
% 1.38/0.54    ~spl2_6 | spl2_7 | ~spl2_2),
% 1.38/0.54    inference(avatar_split_clause,[],[f343,f90,f352,f348])).
% 1.38/0.54  fof(f343,plain,(
% 1.38/0.54    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.38/0.54    inference(superposition,[],[f215,f91])).
% 1.38/0.54  fof(f215,plain,(
% 1.38/0.54    ( ! [X6,X8,X7] : (r1_tarski(k7_subset_1(X8,X6,X7),X6) | ~m1_subset_1(X6,k1_zfmisc_1(X8))) )),
% 1.38/0.54    inference(superposition,[],[f78,f83])).
% 1.38/0.54  fof(f298,plain,(
% 1.38/0.54    spl2_4),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f297])).
% 1.38/0.54  fof(f297,plain,(
% 1.38/0.54    $false | spl2_4),
% 1.38/0.54    inference(resolution,[],[f289,f47])).
% 1.38/0.54  fof(f47,plain,(
% 1.38/0.54    v2_pre_topc(sK0)),
% 1.38/0.54    inference(cnf_transformation,[],[f46])).
% 1.38/0.54  fof(f289,plain,(
% 1.38/0.54    ~v2_pre_topc(sK0) | spl2_4),
% 1.38/0.54    inference(avatar_component_clause,[],[f287])).
% 1.38/0.54  fof(f287,plain,(
% 1.38/0.54    spl2_4 <=> v2_pre_topc(sK0)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.38/0.54  fof(f296,plain,(
% 1.38/0.54    spl2_3),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f295])).
% 1.38/0.54  fof(f295,plain,(
% 1.38/0.54    $false | spl2_3),
% 1.38/0.54    inference(resolution,[],[f285,f48])).
% 1.38/0.54  fof(f48,plain,(
% 1.38/0.54    l1_pre_topc(sK0)),
% 1.38/0.54    inference(cnf_transformation,[],[f46])).
% 1.38/0.54  fof(f285,plain,(
% 1.38/0.54    ~l1_pre_topc(sK0) | spl2_3),
% 1.38/0.54    inference(avatar_component_clause,[],[f283])).
% 1.38/0.54  fof(f294,plain,(
% 1.38/0.54    ~spl2_3 | spl2_1 | ~spl2_4 | ~spl2_5),
% 1.38/0.54    inference(avatar_split_clause,[],[f278,f291,f287,f86,f283])).
% 1.38/0.54  fof(f278,plain,(
% 1.38/0.54    sK1 != k2_pre_topc(sK0,sK1) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.38/0.54    inference(resolution,[],[f57,f49])).
% 1.38/0.54  fof(f57,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f31])).
% 1.38/0.54  fof(f94,plain,(
% 1.38/0.54    spl2_1 | spl2_2),
% 1.38/0.54    inference(avatar_split_clause,[],[f50,f90,f86])).
% 1.38/0.54  fof(f50,plain,(
% 1.38/0.54    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.38/0.54    inference(cnf_transformation,[],[f46])).
% 1.53/0.56  fof(f93,plain,(
% 1.53/0.56    ~spl2_1 | ~spl2_2),
% 1.53/0.56    inference(avatar_split_clause,[],[f51,f90,f86])).
% 1.53/0.56  fof(f51,plain,(
% 1.53/0.56    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 1.53/0.56    inference(cnf_transformation,[],[f46])).
% 1.53/0.56  % SZS output end Proof for theBenchmark
% 1.53/0.56  % (19302)------------------------------
% 1.53/0.56  % (19302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (19302)Termination reason: Refutation
% 1.53/0.56  
% 1.53/0.56  % (19302)Memory used [KB]: 6908
% 1.53/0.56  % (19302)Time elapsed: 0.131 s
% 1.53/0.56  % (19302)------------------------------
% 1.53/0.56  % (19302)------------------------------
% 1.53/0.56  % (19297)Success in time 0.203 s
%------------------------------------------------------------------------------
