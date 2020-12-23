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
% DateTime   : Thu Dec  3 13:14:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 238 expanded)
%              Number of leaves         :   27 ( 110 expanded)
%              Depth                    :    8
%              Number of atoms          :  348 (1064 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f632,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f79,f84,f89,f94,f114,f197,f202,f226,f243,f333,f619])).

fof(f619,plain,
    ( ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | spl3_24
    | ~ spl3_30 ),
    inference(avatar_contradiction_clause,[],[f600])).

fof(f600,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | spl3_24
    | ~ spl3_30 ),
    inference(unit_resulting_resolution,[],[f93,f88,f68,f83,f51,f242,f332,f301,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(X2,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

fof(f301,plain,
    ( ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f153,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f153,plain,
    ( ! [X0] : r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),u1_struct_0(sK0))
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f106,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f106,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl3_9
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f332,plain,
    ( v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl3_30
  <=> v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f242,plain,
    ( ~ v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | spl3_24 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl3_24
  <=> v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f83,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f68,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_3
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f88,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f93,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f333,plain,
    ( spl3_30
    | ~ spl3_6
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f328,f223,f81,f330])).

fof(f223,plain,
    ( spl3_21
  <=> v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f328,plain,
    ( v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ spl3_6
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f327,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f327,plain,
    ( v4_pre_topc(k1_setfam_1(k2_tarski(sK2,sK1)),sK0)
    | ~ spl3_6
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f225,f180])).

fof(f180,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f83,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f49,f44])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f225,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK2,sK1),sK0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f223])).

fof(f243,plain,
    ( ~ spl3_24
    | spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f237,f76,f56,f240])).

fof(f56,plain,
    ( spl3_1
  <=> v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f76,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f237,plain,
    ( ~ v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | spl3_1
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f58,f179])).

fof(f179,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f78,f54])).

fof(f78,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f58,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f226,plain,
    ( spl3_21
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f215,f199,f194,f91,f86,f81,f76,f223])).

fof(f194,plain,
    ( spl3_16
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f199,plain,
    ( spl3_17
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f215,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK2,sK1),sK0)
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f93,f88,f201,f196,f78,f83,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_1)).

fof(f196,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f194])).

fof(f201,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f199])).

fof(f202,plain,
    ( spl3_17
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f190,f91,f86,f76,f71,f61,f199])).

fof(f61,plain,
    ( spl3_2
  <=> v2_compts_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f71,plain,
    ( spl3_4
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f190,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f93,f88,f73,f63,f78,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v8_pre_topc(X0)
      | ~ v2_compts_1(X1,X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

fof(f63,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f73,plain,
    ( v8_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f197,plain,
    ( spl3_16
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f191,f91,f86,f81,f71,f66,f194])).

fof(f191,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f93,f88,f73,f68,f83,f39])).

fof(f114,plain,
    ( spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f102,f81,f104])).

fof(f102,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(resolution,[],[f46,f83])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f94,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f31,f91])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v2_compts_1(X2,X0)
                & v2_compts_1(X1,X0)
                & v8_pre_topc(X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v2_compts_1(X2,sK0)
              & v2_compts_1(X1,sK0)
              & v8_pre_topc(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v2_compts_1(X2,sK0)
            & v2_compts_1(X1,sK0)
            & v8_pre_topc(sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v2_compts_1(X2,sK0)
          & v2_compts_1(sK1,sK0)
          & v8_pre_topc(sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v2_compts_1(X2,sK0)
        & v2_compts_1(sK1,sK0)
        & v8_pre_topc(sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v2_compts_1(sK2,sK0)
      & v2_compts_1(sK1,sK0)
      & v8_pre_topc(sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_compts_1(X2,X0)
                    & v2_compts_1(X1,X0)
                    & v8_pre_topc(X0) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_compts_1(X2,X0)
                  & v2_compts_1(X1,X0)
                  & v8_pre_topc(X0) )
               => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).

fof(f89,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f32,f86])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f33,f81])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f34,f76])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f35,f71])).

fof(f35,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f37,f61])).

fof(f37,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f38,f56])).

fof(f38,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:22:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.40  % (26061)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.44  % (26049)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (26050)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (26062)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (26054)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (26053)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (26060)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (26064)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (26057)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (26056)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (26055)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (26048)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (26058)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (26054)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f632,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f79,f84,f89,f94,f114,f197,f202,f226,f243,f333,f619])).
% 0.20/0.49  fof(f619,plain,(
% 0.20/0.49    ~spl3_3 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_9 | spl3_24 | ~spl3_30),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f600])).
% 0.20/0.49  fof(f600,plain,(
% 0.20/0.49    $false | (~spl3_3 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_9 | spl3_24 | ~spl3_30)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f93,f88,f68,f83,f51,f242,f332,f301,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(X2,X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).
% 0.20/0.49  fof(f301,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_9),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f153,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.49    inference(nnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),u1_struct_0(sK0))) ) | ~spl3_9),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f106,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f48,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    spl3_9 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.49  fof(f332,plain,(
% 0.20/0.49    v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | ~spl3_30),
% 0.20/0.49    inference(avatar_component_clause,[],[f330])).
% 0.20/0.49  fof(f330,plain,(
% 0.20/0.49    spl3_30 <=> v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.49  fof(f242,plain,(
% 0.20/0.49    ~v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | spl3_24),
% 0.20/0.49    inference(avatar_component_clause,[],[f240])).
% 0.20/0.49  fof(f240,plain,(
% 0.20/0.49    spl3_24 <=> v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f42,f44])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    v2_compts_1(sK1,sK0) | ~spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    spl3_3 <=> v2_compts_1(sK1,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    l1_pre_topc(sK0) | ~spl3_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    spl3_7 <=> l1_pre_topc(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    v2_pre_topc(sK0) | ~spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    spl3_8 <=> v2_pre_topc(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f333,plain,(
% 0.20/0.49    spl3_30 | ~spl3_6 | ~spl3_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f328,f223,f81,f330])).
% 0.20/0.49  fof(f223,plain,(
% 0.20/0.49    spl3_21 <=> v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK2,sK1),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.49  fof(f328,plain,(
% 0.20/0.49    v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | (~spl3_6 | ~spl3_21)),
% 0.20/0.49    inference(forward_demodulation,[],[f327,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.49  fof(f327,plain,(
% 0.20/0.49    v4_pre_topc(k1_setfam_1(k2_tarski(sK2,sK1)),sK0) | (~spl3_6 | ~spl3_21)),
% 0.20/0.49    inference(forward_demodulation,[],[f225,f180])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))) ) | ~spl3_6),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f83,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f49,f44])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.49  fof(f225,plain,(
% 0.20/0.49    v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK2,sK1),sK0) | ~spl3_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f223])).
% 0.20/0.49  fof(f243,plain,(
% 0.20/0.49    ~spl3_24 | spl3_1 | ~spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f237,f76,f56,f240])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl3_1 <=> v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f237,plain,(
% 0.20/0.49    ~v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | (spl3_1 | ~spl3_5)),
% 0.20/0.49    inference(backward_demodulation,[],[f58,f179])).
% 0.20/0.49  fof(f179,plain,(
% 0.20/0.49    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))) ) | ~spl3_5),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f78,f54])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f76])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f56])).
% 0.20/0.49  fof(f226,plain,(
% 0.20/0.49    spl3_21 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_16 | ~spl3_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f215,f199,f194,f91,f86,f81,f76,f223])).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    spl3_16 <=> v4_pre_topc(sK1,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    spl3_17 <=> v4_pre_topc(sK2,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.49  fof(f215,plain,(
% 0.20/0.49    v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK2,sK1),sK0) | (~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_16 | ~spl3_17)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f93,f88,f201,f196,f78,f83,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_1)).
% 0.20/0.49  fof(f196,plain,(
% 0.20/0.49    v4_pre_topc(sK1,sK0) | ~spl3_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f194])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    v4_pre_topc(sK2,sK0) | ~spl3_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f199])).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    spl3_17 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_7 | ~spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f190,f91,f86,f76,f71,f61,f199])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    spl3_2 <=> v2_compts_1(sK2,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    spl3_4 <=> v8_pre_topc(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    v4_pre_topc(sK2,sK0) | (~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_7 | ~spl3_8)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f93,f88,f73,f63,f78,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v8_pre_topc(X0) | ~v2_compts_1(X1,X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    v2_compts_1(sK2,sK0) | ~spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f61])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    v8_pre_topc(sK0) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f71])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    spl3_16 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f191,f91,f86,f81,f71,f66,f194])).
% 0.20/0.49  fof(f191,plain,(
% 0.20/0.49    v4_pre_topc(sK1,sK0) | (~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f93,f88,f73,f68,f83,f39])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    spl3_9 | ~spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f102,f81,f104])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 0.20/0.49    inference(resolution,[],[f46,f83])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f31,f91])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    v2_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f28,f27,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.49    inference(negated_conjecture,[],[f12])).
% 0.20/0.49  fof(f12,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    spl3_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f32,f86])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f33,f81])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f34,f76])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f35,f71])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    v8_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f36,f66])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    v2_compts_1(sK1,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f37,f61])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    v2_compts_1(sK2,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ~spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f38,f56])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (26054)------------------------------
% 0.20/0.49  % (26054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (26054)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (26054)Memory used [KB]: 6524
% 0.20/0.49  % (26054)Time elapsed: 0.022 s
% 0.20/0.49  % (26054)------------------------------
% 0.20/0.49  % (26054)------------------------------
% 0.20/0.49  % (26047)Success in time 0.141 s
%------------------------------------------------------------------------------
