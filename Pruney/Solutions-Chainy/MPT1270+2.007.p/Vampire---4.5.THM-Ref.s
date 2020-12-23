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
% DateTime   : Thu Dec  3 13:12:36 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 343 expanded)
%              Number of leaves         :   42 ( 128 expanded)
%              Depth                    :   14
%              Number of atoms          :  607 (1068 expanded)
%              Number of equality atoms :   67 (  99 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1158,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f113,f122,f129,f160,f182,f240,f282,f292,f352,f357,f375,f387,f396,f445,f1054,f1145])).

fof(f1145,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_19
    | spl3_21 ),
    inference(avatar_contradiction_clause,[],[f1144])).

fof(f1144,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_19
    | spl3_21 ),
    inference(subsumption_resolution,[],[f485,f1088])).

fof(f1088,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f1087,f1074])).

fof(f1074,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f664,f117])).

fof(f117,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_3
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f664,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f194,f112])).

fof(f112,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tops_1(X0,sK0)
        | k1_xboole_0 = k1_tops_1(sK0,X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f77,f107])).

fof(f107,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = k1_tops_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f1087,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f224,f452])).

fof(f452,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f107,f285,f444,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f444,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl3_19
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f285,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl3_13
  <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f224,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f107,f112,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f485,plain,
    ( k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f484])).

fof(f484,plain,
    ( spl3_21
  <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f1054,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_17
    | ~ spl3_19
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f1053])).

fof(f1053,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_17
    | ~ spl3_19
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f1052,f120])).

fof(f120,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_4
  <=> r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1052,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_17
    | ~ spl3_19
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f1051,f470])).

fof(f470,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f469,f214])).

fof(f214,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f107,f112,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(f469,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f468,f452])).

fof(f468,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f451,f144])).

fof(f144,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f112,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f451,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl3_1
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f107,f444,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

fof(f1051,plain,
    ( r1_tarski(sK1,k9_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_17
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f1050,f419])).

fof(f419,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK1)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_pre_topc(sK0,sK1)))
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f356,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f94,f86])).

fof(f86,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f356,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl3_17
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f1050,plain,
    ( r1_tarski(sK1,k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f1032,f99])).

fof(f99,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f85,f86,f86])).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1032,plain,
    ( r1_tarski(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(backward_demodulation,[],[f337,f1022])).

fof(f1022,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f1021,f486])).

fof(f486,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f484])).

fof(f1021,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f1019,f308])).

fof(f308,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0))
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f107,f128,f281,f81])).

fof(f281,plain,
    ( m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl3_12
  <=> m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f128,plain,
    ( v1_tops_1(sK2(sK0),sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl3_5
  <=> v1_tops_1(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f1019,plain,
    ( k2_pre_topc(sK0,sK2(sK0)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2(sK0))))
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f107,f281,f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | k2_pre_topc(X1,X0) = k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0))) ) ),
    inference(resolution,[],[f90,f88])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f337,plain,
    ( r1_tarski(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_xboole_0))))
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f159,f291,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f97,f86])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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

fof(f291,plain,
    ( r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl3_14
  <=> r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f159,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl3_6
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f445,plain,
    ( spl3_19
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f138,f110,f442])).

fof(f138,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f112,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f396,plain,
    ( ~ spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f391,f115,f119])).

fof(f391,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f68,f117])).

fof(f68,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f56,f55])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
            | ~ v2_tops_1(X1,sK0) )
          & ( r1_tarski(X1,k2_tops_1(sK0,X1))
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
          | ~ v2_tops_1(X1,sK0) )
        & ( r1_tarski(X1,k2_tops_1(sK0,X1))
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | ~ v2_tops_1(sK1,sK0) )
      & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

fof(f387,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_13 ),
    inference(subsumption_resolution,[],[f117,f321])).

fof(f321,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_13 ),
    inference(unit_resulting_resolution,[],[f107,f112,f286,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(f286,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f284])).

fof(f375,plain,
    ( ~ spl3_4
    | ~ spl3_7
    | spl3_9
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_7
    | spl3_9
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f365,f257])).

fof(f257,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_7
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f102,f181,f239,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f239,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl3_9
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f181,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl3_7
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f365,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f102,f121,f351,f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X1,X3)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f351,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl3_16
  <=> r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f121,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f357,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f183,f110,f105,f354])).

fof(f183,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f107,f112,f90])).

fof(f352,plain,
    ( spl3_16
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f174,f110,f105,f349])).

fof(f174,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f107,f112,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).

fof(f292,plain,
    ( spl3_14
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f217,f110,f289])).

fof(f217,plain,
    ( r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f70,f69,f112,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f69,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f282,plain,
    ( spl3_12
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f130,f105,f279])).

fof(f130,plain,
    ( m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f107,f83])).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( v1_tops_1(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_tops_1(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_tops_1)).

fof(f240,plain,
    ( ~ spl3_9
    | ~ spl3_1
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f195,f115,f110,f105,f237])).

fof(f195,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f107,f116,f112,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f116,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f182,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f153,f110,f105,f179])).

fof(f153,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f107,f112,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f160,plain,
    ( spl3_6
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f150,f110,f105,f157])).

fof(f150,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f107,f112,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f129,plain,
    ( spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f123,f105,f126])).

fof(f123,plain,
    ( v1_tops_1(sK2(sK0),sK0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f107,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v1_tops_1(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f122,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f67,f119,f115])).

fof(f67,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f113,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f66,f110])).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

fof(f108,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f65,f105])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (22132)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.48  % (22112)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (22127)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (22119)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (22113)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (22107)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (22108)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.56  % (22110)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.57  % (22118)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.57  % (22125)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.57  % (22114)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.57  % (22122)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.57  % (22124)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.57  % (22106)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.57  % (22133)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.57  % (22131)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.58  % (22116)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.58  % (22133)Refutation not found, incomplete strategy% (22133)------------------------------
% 0.21/0.58  % (22133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (22133)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (22133)Memory used [KB]: 10746
% 0.21/0.58  % (22133)Time elapsed: 0.178 s
% 0.21/0.58  % (22133)------------------------------
% 0.21/0.58  % (22133)------------------------------
% 0.21/0.58  % (22111)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.58  % (22105)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.58  % (22130)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.58  % (22123)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.58  % (22128)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.59  % (22121)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.59  % (22115)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.59  % (22120)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.59  % (22109)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.59  % (22115)Refutation not found, incomplete strategy% (22115)------------------------------
% 0.21/0.59  % (22115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (22115)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.60  % (22134)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.60  % (22134)Refutation not found, incomplete strategy% (22134)------------------------------
% 0.21/0.60  % (22134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (22134)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (22134)Memory used [KB]: 1663
% 0.21/0.60  % (22134)Time elapsed: 0.181 s
% 0.21/0.60  % (22134)------------------------------
% 0.21/0.60  % (22134)------------------------------
% 1.84/0.60  % (22129)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.84/0.61  % (22126)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.84/0.61  % (22115)Memory used [KB]: 10746
% 1.84/0.61  % (22115)Time elapsed: 0.190 s
% 1.84/0.61  % (22115)------------------------------
% 1.84/0.61  % (22115)------------------------------
% 1.98/0.62  % (22117)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.98/0.62  % (22121)Refutation not found, incomplete strategy% (22121)------------------------------
% 1.98/0.62  % (22121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.62  % (22121)Termination reason: Refutation not found, incomplete strategy
% 1.98/0.62  
% 1.98/0.62  % (22121)Memory used [KB]: 10746
% 1.98/0.62  % (22121)Time elapsed: 0.210 s
% 1.98/0.62  % (22121)------------------------------
% 1.98/0.62  % (22121)------------------------------
% 2.05/0.64  % (22125)Refutation found. Thanks to Tanya!
% 2.05/0.64  % SZS status Theorem for theBenchmark
% 2.05/0.64  % SZS output start Proof for theBenchmark
% 2.05/0.64  fof(f1158,plain,(
% 2.05/0.64    $false),
% 2.05/0.64    inference(avatar_sat_refutation,[],[f108,f113,f122,f129,f160,f182,f240,f282,f292,f352,f357,f375,f387,f396,f445,f1054,f1145])).
% 2.05/0.64  fof(f1145,plain,(
% 2.05/0.64    ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_13 | ~spl3_19 | spl3_21),
% 2.05/0.64    inference(avatar_contradiction_clause,[],[f1144])).
% 2.05/0.64  fof(f1144,plain,(
% 2.05/0.64    $false | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_13 | ~spl3_19 | spl3_21)),
% 2.05/0.64    inference(subsumption_resolution,[],[f485,f1088])).
% 2.05/0.64  fof(f1088,plain,(
% 2.05/0.64    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_13 | ~spl3_19)),
% 2.05/0.64    inference(forward_demodulation,[],[f1087,f1074])).
% 2.05/0.64  fof(f1074,plain,(
% 2.05/0.64    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 2.05/0.64    inference(subsumption_resolution,[],[f664,f117])).
% 2.05/0.64  fof(f117,plain,(
% 2.05/0.64    v2_tops_1(sK1,sK0) | ~spl3_3),
% 2.05/0.64    inference(avatar_component_clause,[],[f115])).
% 2.05/0.64  fof(f115,plain,(
% 2.05/0.64    spl3_3 <=> v2_tops_1(sK1,sK0)),
% 2.05/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.05/0.64  fof(f664,plain,(
% 2.05/0.64    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl3_1 | ~spl3_2)),
% 2.05/0.64    inference(resolution,[],[f194,f112])).
% 2.05/0.64  fof(f112,plain,(
% 2.05/0.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 2.05/0.64    inference(avatar_component_clause,[],[f110])).
% 2.05/0.64  fof(f110,plain,(
% 2.05/0.64    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.05/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.05/0.64  fof(f194,plain,(
% 2.05/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(X0,sK0) | k1_xboole_0 = k1_tops_1(sK0,X0)) ) | ~spl3_1),
% 2.05/0.64    inference(resolution,[],[f77,f107])).
% 2.05/0.64  fof(f107,plain,(
% 2.05/0.64    l1_pre_topc(sK0) | ~spl3_1),
% 2.05/0.64    inference(avatar_component_clause,[],[f105])).
% 2.05/0.64  fof(f105,plain,(
% 2.05/0.64    spl3_1 <=> l1_pre_topc(sK0)),
% 2.05/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.05/0.64  fof(f77,plain,(
% 2.05/0.64    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = k1_tops_1(X0,X1)) )),
% 2.05/0.64    inference(cnf_transformation,[],[f58])).
% 2.05/0.64  fof(f58,plain,(
% 2.05/0.64    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.64    inference(nnf_transformation,[],[f34])).
% 2.05/0.64  fof(f34,plain,(
% 2.05/0.64    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.64    inference(ennf_transformation,[],[f24])).
% 2.05/0.64  fof(f24,axiom,(
% 2.05/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 2.05/0.64  fof(f1087,plain,(
% 2.05/0.64    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_19)),
% 2.05/0.64    inference(forward_demodulation,[],[f224,f452])).
% 2.05/0.64  fof(f452,plain,(
% 2.05/0.64    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_1 | ~spl3_13 | ~spl3_19)),
% 2.05/0.64    inference(unit_resulting_resolution,[],[f107,f285,f444,f81])).
% 2.05/0.64  fof(f81,plain,(
% 2.05/0.64    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0)) )),
% 2.05/0.64    inference(cnf_transformation,[],[f60])).
% 2.05/0.64  fof(f60,plain,(
% 2.05/0.64    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.64    inference(nnf_transformation,[],[f36])).
% 2.05/0.64  fof(f36,plain,(
% 2.05/0.64    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.64    inference(ennf_transformation,[],[f18])).
% 2.05/0.64  fof(f18,axiom,(
% 2.05/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 2.05/0.64  fof(f444,plain,(
% 2.05/0.64    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_19),
% 2.05/0.64    inference(avatar_component_clause,[],[f442])).
% 2.05/0.64  fof(f442,plain,(
% 2.05/0.64    spl3_19 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.05/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 2.05/0.64  fof(f285,plain,(
% 2.05/0.64    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl3_13),
% 2.05/0.64    inference(avatar_component_clause,[],[f284])).
% 2.05/0.64  fof(f284,plain,(
% 2.05/0.64    spl3_13 <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 2.05/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.05/0.64  fof(f224,plain,(
% 2.05/0.64    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl3_1 | ~spl3_2)),
% 2.05/0.64    inference(unit_resulting_resolution,[],[f107,f112,f75])).
% 2.05/0.64  fof(f75,plain,(
% 2.05/0.64    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 2.05/0.64    inference(cnf_transformation,[],[f32])).
% 2.05/0.64  fof(f32,plain,(
% 2.05/0.64    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.64    inference(ennf_transformation,[],[f16])).
% 2.05/0.64  fof(f16,axiom,(
% 2.05/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 2.05/0.64  fof(f485,plain,(
% 2.05/0.64    k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) | spl3_21),
% 2.05/0.64    inference(avatar_component_clause,[],[f484])).
% 2.05/0.64  fof(f484,plain,(
% 2.05/0.64    spl3_21 <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))),
% 2.05/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 2.05/0.64  fof(f1054,plain,(
% 2.05/0.64    ~spl3_1 | ~spl3_2 | spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_12 | ~spl3_13 | ~spl3_14 | ~spl3_17 | ~spl3_19 | ~spl3_21),
% 2.05/0.64    inference(avatar_contradiction_clause,[],[f1053])).
% 2.05/0.64  fof(f1053,plain,(
% 2.05/0.64    $false | (~spl3_1 | ~spl3_2 | spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_12 | ~spl3_13 | ~spl3_14 | ~spl3_17 | ~spl3_19 | ~spl3_21)),
% 2.05/0.64    inference(subsumption_resolution,[],[f1052,f120])).
% 2.05/0.64  fof(f120,plain,(
% 2.05/0.64    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | spl3_4),
% 2.05/0.64    inference(avatar_component_clause,[],[f119])).
% 2.05/0.64  fof(f119,plain,(
% 2.05/0.64    spl3_4 <=> r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 2.05/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.05/0.64  fof(f1052,plain,(
% 2.05/0.64    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_12 | ~spl3_13 | ~spl3_14 | ~spl3_17 | ~spl3_19 | ~spl3_21)),
% 2.05/0.64    inference(forward_demodulation,[],[f1051,f470])).
% 2.05/0.64  fof(f470,plain,(
% 2.05/0.64    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_19)),
% 2.05/0.64    inference(forward_demodulation,[],[f469,f214])).
% 2.05/0.64  fof(f214,plain,(
% 2.05/0.64    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_1 | ~spl3_2)),
% 2.05/0.64    inference(unit_resulting_resolution,[],[f107,f112,f74])).
% 2.05/0.64  fof(f74,plain,(
% 2.05/0.64    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) )),
% 2.05/0.64    inference(cnf_transformation,[],[f31])).
% 2.05/0.64  fof(f31,plain,(
% 2.05/0.64    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.64    inference(ennf_transformation,[],[f22])).
% 2.05/0.64  fof(f22,axiom,(
% 2.05/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).
% 2.05/0.64  fof(f469,plain,(
% 2.05/0.64    k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_19)),
% 2.05/0.64    inference(forward_demodulation,[],[f468,f452])).
% 2.05/0.64  fof(f468,plain,(
% 2.05/0.64    k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_19)),
% 2.05/0.64    inference(forward_demodulation,[],[f451,f144])).
% 2.05/0.64  fof(f144,plain,(
% 2.05/0.64    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_2),
% 2.05/0.64    inference(unit_resulting_resolution,[],[f112,f88])).
% 2.05/0.64  fof(f88,plain,(
% 2.05/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.05/0.64    inference(cnf_transformation,[],[f39])).
% 2.05/0.64  fof(f39,plain,(
% 2.05/0.64    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/0.64    inference(ennf_transformation,[],[f9])).
% 2.05/0.64  fof(f9,axiom,(
% 2.05/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.05/0.64  fof(f451,plain,(
% 2.05/0.64    k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | (~spl3_1 | ~spl3_19)),
% 2.05/0.64    inference(unit_resulting_resolution,[],[f107,f444,f76])).
% 2.05/0.64  fof(f76,plain,(
% 2.05/0.64    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 2.05/0.64    inference(cnf_transformation,[],[f33])).
% 2.05/0.64  fof(f33,plain,(
% 2.05/0.64    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.64    inference(ennf_transformation,[],[f17])).
% 2.05/0.64  fof(f17,axiom,(
% 2.05/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).
% 2.05/0.64  fof(f1051,plain,(
% 2.05/0.64    r1_tarski(sK1,k9_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,sK1))) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_12 | ~spl3_14 | ~spl3_17 | ~spl3_21)),
% 2.05/0.64    inference(forward_demodulation,[],[f1050,f419])).
% 2.05/0.64  fof(f419,plain,(
% 2.05/0.64    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK1)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_pre_topc(sK0,sK1)))) ) | ~spl3_17),
% 2.05/0.64    inference(unit_resulting_resolution,[],[f356,f100])).
% 2.05/0.66  fof(f100,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 2.05/0.66    inference(definition_unfolding,[],[f94,f86])).
% 2.05/0.66  fof(f86,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f5])).
% 2.05/0.66  fof(f5,axiom,(
% 2.05/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.05/0.66  fof(f94,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f44])).
% 2.05/0.66  fof(f44,plain,(
% 2.05/0.66    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.05/0.66    inference(ennf_transformation,[],[f10])).
% 2.05/0.66  fof(f10,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.05/0.66  fof(f356,plain,(
% 2.05/0.66    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_17),
% 2.05/0.66    inference(avatar_component_clause,[],[f354])).
% 2.05/0.66  fof(f354,plain,(
% 2.05/0.66    spl3_17 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 2.05/0.66  fof(f1050,plain,(
% 2.05/0.66    r1_tarski(sK1,k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)))) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_12 | ~spl3_14 | ~spl3_21)),
% 2.05/0.66    inference(forward_demodulation,[],[f1032,f99])).
% 2.05/0.66  fof(f99,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.05/0.66    inference(definition_unfolding,[],[f85,f86,f86])).
% 2.05/0.66  fof(f85,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f1])).
% 2.05/0.66  fof(f1,axiom,(
% 2.05/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.05/0.66  fof(f1032,plain,(
% 2.05/0.66    r1_tarski(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_12 | ~spl3_14 | ~spl3_21)),
% 2.05/0.66    inference(backward_demodulation,[],[f337,f1022])).
% 2.05/0.66  fof(f1022,plain,(
% 2.05/0.66    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | (~spl3_1 | ~spl3_5 | ~spl3_12 | ~spl3_21)),
% 2.05/0.66    inference(forward_demodulation,[],[f1021,f486])).
% 2.05/0.66  fof(f486,plain,(
% 2.05/0.66    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) | ~spl3_21),
% 2.05/0.66    inference(avatar_component_clause,[],[f484])).
% 2.05/0.66  fof(f1021,plain,(
% 2.05/0.66    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))) | (~spl3_1 | ~spl3_5 | ~spl3_12)),
% 2.05/0.66    inference(forward_demodulation,[],[f1019,f308])).
% 2.05/0.66  fof(f308,plain,(
% 2.05/0.66    k2_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0)) | (~spl3_1 | ~spl3_5 | ~spl3_12)),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f107,f128,f281,f81])).
% 2.05/0.66  fof(f281,plain,(
% 2.05/0.66    m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_12),
% 2.05/0.66    inference(avatar_component_clause,[],[f279])).
% 2.05/0.66  fof(f279,plain,(
% 2.05/0.66    spl3_12 <=> m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.05/0.66  fof(f128,plain,(
% 2.05/0.66    v1_tops_1(sK2(sK0),sK0) | ~spl3_5),
% 2.05/0.66    inference(avatar_component_clause,[],[f126])).
% 2.05/0.66  fof(f126,plain,(
% 2.05/0.66    spl3_5 <=> v1_tops_1(sK2(sK0),sK0)),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.05/0.66  fof(f1019,plain,(
% 2.05/0.66    k2_pre_topc(sK0,sK2(sK0)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2(sK0)))) | (~spl3_1 | ~spl3_12)),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f107,f281,f185])).
% 2.05/0.66  fof(f185,plain,(
% 2.05/0.66    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k2_pre_topc(X1,X0) = k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0)))) )),
% 2.05/0.66    inference(resolution,[],[f90,f88])).
% 2.05/0.66  fof(f90,plain,(
% 2.05/0.66    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f43])).
% 2.05/0.66  fof(f43,plain,(
% 2.05/0.66    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.05/0.66    inference(flattening,[],[f42])).
% 2.05/0.66  fof(f42,plain,(
% 2.05/0.66    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.05/0.66    inference(ennf_transformation,[],[f14])).
% 2.05/0.66  fof(f14,axiom,(
% 2.05/0.66    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.05/0.66  fof(f337,plain,(
% 2.05/0.66    r1_tarski(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_xboole_0)))) | (~spl3_6 | ~spl3_14)),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f159,f291,f101])).
% 2.05/0.66  fof(f101,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.05/0.66    inference(definition_unfolding,[],[f97,f86])).
% 2.05/0.66  fof(f97,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f50])).
% 2.05/0.66  fof(f50,plain,(
% 2.05/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.05/0.66    inference(flattening,[],[f49])).
% 2.05/0.66  fof(f49,plain,(
% 2.05/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.05/0.66    inference(ennf_transformation,[],[f3])).
% 2.05/0.66  fof(f3,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 2.05/0.66  fof(f291,plain,(
% 2.05/0.66    r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) | ~spl3_14),
% 2.05/0.66    inference(avatar_component_clause,[],[f289])).
% 2.05/0.66  fof(f289,plain,(
% 2.05/0.66    spl3_14 <=> r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.05/0.66  fof(f159,plain,(
% 2.05/0.66    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl3_6),
% 2.05/0.66    inference(avatar_component_clause,[],[f157])).
% 2.05/0.66  fof(f157,plain,(
% 2.05/0.66    spl3_6 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.05/0.66  fof(f445,plain,(
% 2.05/0.66    spl3_19 | ~spl3_2),
% 2.05/0.66    inference(avatar_split_clause,[],[f138,f110,f442])).
% 2.05/0.66  fof(f138,plain,(
% 2.05/0.66    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f112,f87])).
% 2.05/0.66  fof(f87,plain,(
% 2.05/0.66    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f38])).
% 2.05/0.66  fof(f38,plain,(
% 2.05/0.66    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/0.66    inference(ennf_transformation,[],[f8])).
% 2.05/0.66  fof(f8,axiom,(
% 2.05/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.05/0.66  fof(f396,plain,(
% 2.05/0.66    ~spl3_4 | ~spl3_3),
% 2.05/0.66    inference(avatar_split_clause,[],[f391,f115,f119])).
% 2.05/0.66  fof(f391,plain,(
% 2.05/0.66    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~spl3_3),
% 2.05/0.66    inference(subsumption_resolution,[],[f68,f117])).
% 2.05/0.66  fof(f68,plain,(
% 2.05/0.66    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 2.05/0.66    inference(cnf_transformation,[],[f57])).
% 2.05/0.66  fof(f57,plain,(
% 2.05/0.66    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f56,f55])).
% 2.05/0.66  fof(f55,plain,(
% 2.05/0.66    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f56,plain,(
% 2.05/0.66    ? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f54,plain,(
% 2.05/0.66    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.05/0.66    inference(flattening,[],[f53])).
% 2.05/0.66  fof(f53,plain,(
% 2.05/0.66    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.05/0.66    inference(nnf_transformation,[],[f27])).
% 2.05/0.66  fof(f27,plain,(
% 2.05/0.66    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.05/0.66    inference(ennf_transformation,[],[f26])).
% 2.05/0.66  fof(f26,negated_conjecture,(
% 2.05/0.66    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 2.05/0.66    inference(negated_conjecture,[],[f25])).
% 2.05/0.66  fof(f25,conjecture,(
% 2.05/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).
% 2.05/0.66  fof(f387,plain,(
% 2.05/0.66    ~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_13),
% 2.05/0.66    inference(avatar_contradiction_clause,[],[f386])).
% 2.05/0.66  fof(f386,plain,(
% 2.05/0.66    $false | (~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_13)),
% 2.05/0.66    inference(subsumption_resolution,[],[f117,f321])).
% 2.05/0.66  fof(f321,plain,(
% 2.05/0.66    ~v2_tops_1(sK1,sK0) | (~spl3_1 | ~spl3_2 | spl3_13)),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f107,f112,f286,f79])).
% 2.05/0.66  fof(f79,plain,(
% 2.05/0.66    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f59])).
% 2.05/0.66  fof(f59,plain,(
% 2.05/0.66    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.66    inference(nnf_transformation,[],[f35])).
% 2.05/0.66  fof(f35,plain,(
% 2.05/0.66    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.66    inference(ennf_transformation,[],[f19])).
% 2.05/0.66  fof(f19,axiom,(
% 2.05/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).
% 2.05/0.66  fof(f286,plain,(
% 2.05/0.66    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl3_13),
% 2.05/0.66    inference(avatar_component_clause,[],[f284])).
% 2.05/0.66  fof(f375,plain,(
% 2.05/0.66    ~spl3_4 | ~spl3_7 | spl3_9 | ~spl3_16),
% 2.05/0.66    inference(avatar_contradiction_clause,[],[f374])).
% 2.05/0.66  fof(f374,plain,(
% 2.05/0.66    $false | (~spl3_4 | ~spl3_7 | spl3_9 | ~spl3_16)),
% 2.05/0.66    inference(subsumption_resolution,[],[f365,f257])).
% 2.05/0.66  fof(f257,plain,(
% 2.05/0.66    ~r1_xboole_0(k1_tops_1(sK0,sK1),sK1) | (~spl3_7 | spl3_9)),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f102,f181,f239,f96])).
% 2.05/0.66  fof(f96,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f48])).
% 2.05/0.66  fof(f48,plain,(
% 2.05/0.66    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.05/0.66    inference(flattening,[],[f47])).
% 2.05/0.66  fof(f47,plain,(
% 2.05/0.66    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.05/0.66    inference(ennf_transformation,[],[f7])).
% 2.05/0.66  fof(f7,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 2.05/0.66  fof(f239,plain,(
% 2.05/0.66    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl3_9),
% 2.05/0.66    inference(avatar_component_clause,[],[f237])).
% 2.05/0.66  fof(f237,plain,(
% 2.05/0.66    spl3_9 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.05/0.66  fof(f181,plain,(
% 2.05/0.66    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_7),
% 2.05/0.66    inference(avatar_component_clause,[],[f179])).
% 2.05/0.66  fof(f179,plain,(
% 2.05/0.66    spl3_7 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.05/0.66  fof(f102,plain,(
% 2.05/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.05/0.66    inference(equality_resolution,[],[f92])).
% 2.05/0.66  fof(f92,plain,(
% 2.05/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.05/0.66    inference(cnf_transformation,[],[f64])).
% 2.05/0.66  fof(f64,plain,(
% 2.05/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.05/0.66    inference(flattening,[],[f63])).
% 2.05/0.66  fof(f63,plain,(
% 2.05/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.05/0.66    inference(nnf_transformation,[],[f2])).
% 2.05/0.66  fof(f2,axiom,(
% 2.05/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.05/0.66  fof(f365,plain,(
% 2.05/0.66    r1_xboole_0(k1_tops_1(sK0,sK1),sK1) | (~spl3_4 | ~spl3_16)),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f102,f121,f351,f98])).
% 2.05/0.66  fof(f98,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X1,X3) | r1_xboole_0(X0,X2) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f52])).
% 2.05/0.66  fof(f52,plain,(
% 2.05/0.66    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 2.05/0.66    inference(flattening,[],[f51])).
% 2.05/0.66  fof(f51,plain,(
% 2.05/0.66    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 2.05/0.66    inference(ennf_transformation,[],[f6])).
% 2.05/0.66  fof(f6,axiom,(
% 2.05/0.66    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).
% 2.05/0.66  fof(f351,plain,(
% 2.05/0.66    r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl3_16),
% 2.05/0.66    inference(avatar_component_clause,[],[f349])).
% 2.05/0.66  fof(f349,plain,(
% 2.05/0.66    spl3_16 <=> r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 2.05/0.66  fof(f121,plain,(
% 2.05/0.66    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~spl3_4),
% 2.05/0.66    inference(avatar_component_clause,[],[f119])).
% 2.05/0.66  fof(f357,plain,(
% 2.05/0.66    spl3_17 | ~spl3_1 | ~spl3_2),
% 2.05/0.66    inference(avatar_split_clause,[],[f183,f110,f105,f354])).
% 2.05/0.66  fof(f183,plain,(
% 2.05/0.66    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_2)),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f107,f112,f90])).
% 2.05/0.66  fof(f352,plain,(
% 2.05/0.66    spl3_16 | ~spl3_1 | ~spl3_2),
% 2.05/0.66    inference(avatar_split_clause,[],[f174,f110,f105,f349])).
% 2.05/0.66  fof(f174,plain,(
% 2.05/0.66    r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl3_1 | ~spl3_2)),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f107,f112,f73])).
% 2.05/0.66  fof(f73,plain,(
% 2.05/0.66    ( ! [X0,X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f30])).
% 2.05/0.66  fof(f30,plain,(
% 2.05/0.66    ! [X0] : (! [X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.66    inference(ennf_transformation,[],[f23])).
% 2.05/0.66  fof(f23,axiom,(
% 2.05/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).
% 2.05/0.66  fof(f292,plain,(
% 2.05/0.66    spl3_14 | ~spl3_2),
% 2.05/0.66    inference(avatar_split_clause,[],[f217,f110,f289])).
% 2.05/0.66  fof(f217,plain,(
% 2.05/0.66    r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) | ~spl3_2),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f70,f69,f112,f89])).
% 2.05/0.66  fof(f89,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_tarski(X2,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f41])).
% 2.05/0.66  fof(f41,plain,(
% 2.05/0.66    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/0.66    inference(flattening,[],[f40])).
% 2.05/0.66  fof(f40,plain,(
% 2.05/0.66    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/0.66    inference(ennf_transformation,[],[f11])).
% 2.05/0.66  fof(f11,axiom,(
% 2.05/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 2.05/0.66  fof(f69,plain,(
% 2.05/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f4])).
% 2.05/0.66  fof(f4,axiom,(
% 2.05/0.66    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.05/0.66  fof(f70,plain,(
% 2.05/0.66    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f12])).
% 2.05/0.66  fof(f12,axiom,(
% 2.05/0.66    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.05/0.66  fof(f282,plain,(
% 2.05/0.66    spl3_12 | ~spl3_1),
% 2.05/0.66    inference(avatar_split_clause,[],[f130,f105,f279])).
% 2.05/0.66  fof(f130,plain,(
% 2.05/0.66    m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_1),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f107,f83])).
% 2.05/0.66  fof(f83,plain,(
% 2.05/0.66    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f62])).
% 2.05/0.66  fof(f62,plain,(
% 2.05/0.66    ! [X0] : ((v1_tops_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f61])).
% 2.05/0.66  fof(f61,plain,(
% 2.05/0.66    ! [X0] : (? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f37,plain,(
% 2.05/0.66    ! [X0] : (? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.66    inference(ennf_transformation,[],[f20])).
% 2.05/0.66  fof(f20,axiom,(
% 2.05/0.66    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_tops_1)).
% 2.05/0.67  fof(f240,plain,(
% 2.05/0.67    ~spl3_9 | ~spl3_1 | ~spl3_2 | spl3_3),
% 2.05/0.67    inference(avatar_split_clause,[],[f195,f115,f110,f105,f237])).
% 2.05/0.67  fof(f195,plain,(
% 2.05/0.67    k1_xboole_0 != k1_tops_1(sK0,sK1) | (~spl3_1 | ~spl3_2 | spl3_3)),
% 2.05/0.67    inference(unit_resulting_resolution,[],[f107,f116,f112,f78])).
% 2.05/0.67  fof(f78,plain,(
% 2.05/0.67    ( ! [X0,X1] : (k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.67    inference(cnf_transformation,[],[f58])).
% 2.05/0.67  fof(f116,plain,(
% 2.05/0.67    ~v2_tops_1(sK1,sK0) | spl3_3),
% 2.05/0.67    inference(avatar_component_clause,[],[f115])).
% 2.05/0.67  fof(f182,plain,(
% 2.05/0.67    spl3_7 | ~spl3_1 | ~spl3_2),
% 2.05/0.67    inference(avatar_split_clause,[],[f153,f110,f105,f179])).
% 2.05/0.67  fof(f153,plain,(
% 2.05/0.67    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_1 | ~spl3_2)),
% 2.05/0.67    inference(unit_resulting_resolution,[],[f107,f112,f72])).
% 2.05/0.67  fof(f72,plain,(
% 2.05/0.67    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 2.05/0.67    inference(cnf_transformation,[],[f29])).
% 2.05/0.67  fof(f29,plain,(
% 2.05/0.67    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.67    inference(ennf_transformation,[],[f21])).
% 2.05/0.67  fof(f21,axiom,(
% 2.05/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.05/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 2.05/0.67  fof(f160,plain,(
% 2.05/0.67    spl3_6 | ~spl3_1 | ~spl3_2),
% 2.05/0.67    inference(avatar_split_clause,[],[f150,f110,f105,f157])).
% 2.05/0.67  fof(f150,plain,(
% 2.05/0.67    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl3_1 | ~spl3_2)),
% 2.05/0.67    inference(unit_resulting_resolution,[],[f107,f112,f71])).
% 2.05/0.67  fof(f71,plain,(
% 2.05/0.67    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 2.05/0.67    inference(cnf_transformation,[],[f28])).
% 2.05/0.67  fof(f28,plain,(
% 2.05/0.67    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.67    inference(ennf_transformation,[],[f15])).
% 2.05/0.67  fof(f15,axiom,(
% 2.05/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 2.05/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 2.05/0.67  fof(f129,plain,(
% 2.05/0.67    spl3_5 | ~spl3_1),
% 2.05/0.67    inference(avatar_split_clause,[],[f123,f105,f126])).
% 2.05/0.67  fof(f123,plain,(
% 2.05/0.67    v1_tops_1(sK2(sK0),sK0) | ~spl3_1),
% 2.05/0.67    inference(unit_resulting_resolution,[],[f107,f84])).
% 2.05/0.67  fof(f84,plain,(
% 2.05/0.67    ( ! [X0] : (~l1_pre_topc(X0) | v1_tops_1(sK2(X0),X0)) )),
% 2.05/0.67    inference(cnf_transformation,[],[f62])).
% 2.05/0.67  fof(f122,plain,(
% 2.05/0.67    spl3_3 | spl3_4),
% 2.05/0.67    inference(avatar_split_clause,[],[f67,f119,f115])).
% 2.05/0.67  fof(f67,plain,(
% 2.05/0.67    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 2.05/0.67    inference(cnf_transformation,[],[f57])).
% 2.05/0.67  fof(f113,plain,(
% 2.05/0.67    spl3_2),
% 2.05/0.67    inference(avatar_split_clause,[],[f66,f110])).
% 2.05/0.67  fof(f66,plain,(
% 2.05/0.67    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.05/0.67    inference(cnf_transformation,[],[f57])).
% 2.05/0.67  fof(f108,plain,(
% 2.05/0.67    spl3_1),
% 2.05/0.67    inference(avatar_split_clause,[],[f65,f105])).
% 2.05/0.67  fof(f65,plain,(
% 2.05/0.67    l1_pre_topc(sK0)),
% 2.05/0.67    inference(cnf_transformation,[],[f57])).
% 2.05/0.67  % SZS output end Proof for theBenchmark
% 2.05/0.67  % (22125)------------------------------
% 2.05/0.67  % (22125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.67  % (22125)Termination reason: Refutation
% 2.05/0.67  
% 2.05/0.67  % (22125)Memory used [KB]: 11513
% 2.05/0.67  % (22125)Time elapsed: 0.213 s
% 2.05/0.67  % (22125)------------------------------
% 2.05/0.67  % (22125)------------------------------
% 2.05/0.67  % (22104)Success in time 0.308 s
%------------------------------------------------------------------------------
