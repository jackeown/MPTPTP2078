%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:46 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 214 expanded)
%              Number of leaves         :   22 (  94 expanded)
%              Depth                    :    9
%              Number of atoms          :  316 (1018 expanded)
%              Number of equality atoms :    7 (  23 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f68,f73,f78,f83,f100,f114,f119,f141])).

fof(f141,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | spl3_9
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | spl3_9
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f133,f129])).

fof(f129,plain,
    ( v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f126,f89])).

fof(f89,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f77,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f40,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f77,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f126,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f47,f52,f113,f72,f77,f118,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f118,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_11
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f72,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f113,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_10
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f52,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f47,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f133,plain,
    ( ~ v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f47,f52,f62,f72,f41,f99,f94,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(X2,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f94,plain,
    ( ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f87,f89])).

fof(f87,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f77,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f99,plain,
    ( ~ v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_9
  <=> v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f62,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_4
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f119,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f102,f75,f65,f55,f50,f45,f116])).

fof(f55,plain,
    ( spl3_3
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f65,plain,
    ( spl3_5
  <=> v2_compts_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f102,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f47,f52,f57,f67,f77,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v8_pre_topc(X0)
      | ~ v2_compts_1(X1,X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

fof(f67,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f57,plain,
    ( v8_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f114,plain,
    ( spl3_10
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f101,f70,f60,f55,f50,f45,f111])).

fof(f101,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f47,f52,f57,f62,f72,f33])).

fof(f100,plain,
    ( ~ spl3_9
    | ~ spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f93,f80,f75,f97])).

fof(f80,plain,
    ( spl3_8
  <=> v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f93,plain,
    ( ~ v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ spl3_7
    | spl3_8 ),
    inference(backward_demodulation,[],[f82,f89])).

fof(f82,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f83,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f32,f80])).

fof(f32,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22,f21])).

fof(f21,plain,
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

fof(f22,plain,
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

fof(f23,plain,
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

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f78,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f28,f75])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f27,f70])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f30,f60])).

fof(f30,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f29,f55])).

fof(f29,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f26,f50])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f25,f45])).

fof(f25,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n011.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 13:31:12 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.43  % (14527)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.44  % (14513)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.23/0.44  % (14527)Refutation found. Thanks to Tanya!
% 0.23/0.44  % SZS status Theorem for theBenchmark
% 0.23/0.44  % SZS output start Proof for theBenchmark
% 0.23/0.44  fof(f142,plain,(
% 0.23/0.44    $false),
% 0.23/0.44    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f68,f73,f78,f83,f100,f114,f119,f141])).
% 0.23/0.44  fof(f141,plain,(
% 0.23/0.44    ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | spl3_9 | ~spl3_10 | ~spl3_11),
% 0.23/0.44    inference(avatar_contradiction_clause,[],[f140])).
% 0.23/0.44  fof(f140,plain,(
% 0.23/0.44    $false | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | spl3_9 | ~spl3_10 | ~spl3_11)),
% 0.23/0.44    inference(subsumption_resolution,[],[f133,f129])).
% 0.23/0.44  fof(f129,plain,(
% 0.23/0.44    v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7 | ~spl3_10 | ~spl3_11)),
% 0.23/0.44    inference(forward_demodulation,[],[f126,f89])).
% 0.23/0.44  fof(f89,plain,(
% 0.23/0.44    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))) ) | ~spl3_7),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f77,f43])).
% 0.23/0.44  fof(f43,plain,(
% 0.23/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.23/0.44    inference(definition_unfolding,[],[f40,f38])).
% 0.23/0.44  fof(f38,plain,(
% 0.23/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.23/0.44    inference(cnf_transformation,[],[f5])).
% 0.23/0.44  fof(f5,axiom,(
% 0.23/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.23/0.44  fof(f40,plain,(
% 0.23/0.44    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.23/0.44    inference(cnf_transformation,[],[f20])).
% 0.23/0.44  fof(f20,plain,(
% 0.23/0.44    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.23/0.44    inference(ennf_transformation,[],[f4])).
% 0.23/0.44  fof(f4,axiom,(
% 0.23/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.23/0.44  fof(f77,plain,(
% 0.23/0.44    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 0.23/0.44    inference(avatar_component_clause,[],[f75])).
% 0.23/0.44  fof(f75,plain,(
% 0.23/0.44    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.23/0.44  fof(f126,plain,(
% 0.23/0.44    v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7 | ~spl3_10 | ~spl3_11)),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f47,f52,f113,f72,f77,f118,f34])).
% 0.23/0.44  fof(f34,plain,(
% 0.23/0.44    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f16])).
% 0.23/0.44  fof(f16,plain,(
% 0.23/0.44    ! [X0] : (! [X1] : (! [X2] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.44    inference(flattening,[],[f15])).
% 0.23/0.44  fof(f15,plain,(
% 0.23/0.44    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.44    inference(ennf_transformation,[],[f6])).
% 0.23/0.44  fof(f6,axiom,(
% 0.23/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_1)).
% 0.23/0.44  fof(f118,plain,(
% 0.23/0.44    v4_pre_topc(sK2,sK0) | ~spl3_11),
% 0.23/0.44    inference(avatar_component_clause,[],[f116])).
% 0.23/0.44  fof(f116,plain,(
% 0.23/0.44    spl3_11 <=> v4_pre_topc(sK2,sK0)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.23/0.44  fof(f72,plain,(
% 0.23/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.23/0.44    inference(avatar_component_clause,[],[f70])).
% 0.23/0.44  fof(f70,plain,(
% 0.23/0.44    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.23/0.44  fof(f113,plain,(
% 0.23/0.44    v4_pre_topc(sK1,sK0) | ~spl3_10),
% 0.23/0.44    inference(avatar_component_clause,[],[f111])).
% 0.23/0.44  fof(f111,plain,(
% 0.23/0.44    spl3_10 <=> v4_pre_topc(sK1,sK0)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.23/0.44  fof(f52,plain,(
% 0.23/0.44    l1_pre_topc(sK0) | ~spl3_2),
% 0.23/0.44    inference(avatar_component_clause,[],[f50])).
% 0.23/0.44  fof(f50,plain,(
% 0.23/0.44    spl3_2 <=> l1_pre_topc(sK0)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.44  fof(f47,plain,(
% 0.23/0.44    v2_pre_topc(sK0) | ~spl3_1),
% 0.23/0.44    inference(avatar_component_clause,[],[f45])).
% 0.23/0.44  fof(f45,plain,(
% 0.23/0.44    spl3_1 <=> v2_pre_topc(sK0)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.44  fof(f133,plain,(
% 0.23/0.44    ~v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | spl3_9)),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f47,f52,f62,f72,f41,f99,f94,f35])).
% 0.23/0.44  fof(f35,plain,(
% 0.23/0.44    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(X2,X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f18])).
% 0.23/0.44  fof(f18,plain,(
% 0.23/0.44    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.44    inference(flattening,[],[f17])).
% 0.23/0.44  fof(f17,plain,(
% 0.23/0.44    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.44    inference(ennf_transformation,[],[f8])).
% 0.23/0.44  fof(f8,axiom,(
% 0.23/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).
% 0.23/0.44  fof(f94,plain,(
% 0.23/0.44    ( ! [X0] : (m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_7),
% 0.23/0.44    inference(backward_demodulation,[],[f87,f89])).
% 0.23/0.44  fof(f87,plain,(
% 0.23/0.44    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_7),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f77,f39])).
% 0.23/0.44  fof(f39,plain,(
% 0.23/0.44    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.23/0.44    inference(cnf_transformation,[],[f19])).
% 0.23/0.44  fof(f19,plain,(
% 0.23/0.44    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.23/0.44    inference(ennf_transformation,[],[f3])).
% 0.23/0.44  fof(f3,axiom,(
% 0.23/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.23/0.44  fof(f99,plain,(
% 0.23/0.44    ~v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | spl3_9),
% 0.23/0.44    inference(avatar_component_clause,[],[f97])).
% 0.23/0.44  fof(f97,plain,(
% 0.23/0.44    spl3_9 <=> v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.23/0.44  fof(f41,plain,(
% 0.23/0.44    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.23/0.44    inference(definition_unfolding,[],[f36,f38])).
% 0.23/0.44  fof(f36,plain,(
% 0.23/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f2])).
% 0.23/0.44  fof(f2,axiom,(
% 0.23/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.23/0.44  fof(f62,plain,(
% 0.23/0.44    v2_compts_1(sK1,sK0) | ~spl3_4),
% 0.23/0.44    inference(avatar_component_clause,[],[f60])).
% 0.23/0.44  fof(f60,plain,(
% 0.23/0.44    spl3_4 <=> v2_compts_1(sK1,sK0)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.23/0.44  fof(f119,plain,(
% 0.23/0.44    spl3_11 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_7),
% 0.23/0.44    inference(avatar_split_clause,[],[f102,f75,f65,f55,f50,f45,f116])).
% 0.23/0.44  fof(f55,plain,(
% 0.23/0.44    spl3_3 <=> v8_pre_topc(sK0)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.23/0.44  fof(f65,plain,(
% 0.23/0.44    spl3_5 <=> v2_compts_1(sK2,sK0)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.23/0.44  fof(f102,plain,(
% 0.23/0.44    v4_pre_topc(sK2,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_7)),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f47,f52,f57,f67,f77,f33])).
% 0.23/0.44  fof(f33,plain,(
% 0.23/0.44    ( ! [X0,X1] : (~v8_pre_topc(X0) | ~v2_compts_1(X1,X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f14])).
% 0.23/0.44  fof(f14,plain,(
% 0.23/0.44    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.44    inference(flattening,[],[f13])).
% 0.23/0.44  fof(f13,plain,(
% 0.23/0.44    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.44    inference(ennf_transformation,[],[f7])).
% 0.23/0.44  fof(f7,axiom,(
% 0.23/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).
% 0.23/0.44  fof(f67,plain,(
% 0.23/0.44    v2_compts_1(sK2,sK0) | ~spl3_5),
% 0.23/0.44    inference(avatar_component_clause,[],[f65])).
% 0.23/0.44  fof(f57,plain,(
% 0.23/0.44    v8_pre_topc(sK0) | ~spl3_3),
% 0.23/0.44    inference(avatar_component_clause,[],[f55])).
% 0.23/0.44  fof(f114,plain,(
% 0.23/0.44    spl3_10 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6),
% 0.23/0.44    inference(avatar_split_clause,[],[f101,f70,f60,f55,f50,f45,f111])).
% 0.23/0.44  fof(f101,plain,(
% 0.23/0.44    v4_pre_topc(sK1,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f47,f52,f57,f62,f72,f33])).
% 0.23/0.44  fof(f100,plain,(
% 0.23/0.44    ~spl3_9 | ~spl3_7 | spl3_8),
% 0.23/0.44    inference(avatar_split_clause,[],[f93,f80,f75,f97])).
% 0.23/0.44  fof(f80,plain,(
% 0.23/0.44    spl3_8 <=> v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.23/0.44  fof(f93,plain,(
% 0.23/0.44    ~v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | (~spl3_7 | spl3_8)),
% 0.23/0.44    inference(backward_demodulation,[],[f82,f89])).
% 0.23/0.44  fof(f82,plain,(
% 0.23/0.44    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_8),
% 0.23/0.44    inference(avatar_component_clause,[],[f80])).
% 0.23/0.44  fof(f83,plain,(
% 0.23/0.44    ~spl3_8),
% 0.23/0.44    inference(avatar_split_clause,[],[f32,f80])).
% 0.23/0.44  fof(f32,plain,(
% 0.23/0.44    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.23/0.44    inference(cnf_transformation,[],[f24])).
% 0.23/0.44  fof(f24,plain,(
% 0.23/0.44    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.23/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22,f21])).
% 0.23/0.44  fof(f21,plain,(
% 0.23/0.44    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.23/0.44    introduced(choice_axiom,[])).
% 0.23/0.44  fof(f22,plain,(
% 0.23/0.44    ? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.44    introduced(choice_axiom,[])).
% 0.23/0.44  fof(f23,plain,(
% 0.23/0.44    ? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.44    introduced(choice_axiom,[])).
% 0.23/0.44  fof(f12,plain,(
% 0.23/0.44    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.44    inference(flattening,[],[f11])).
% 0.23/0.44  fof(f11,plain,(
% 0.23/0.44    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.23/0.44    inference(ennf_transformation,[],[f10])).
% 0.23/0.44  fof(f10,negated_conjecture,(
% 0.23/0.44    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.23/0.44    inference(negated_conjecture,[],[f9])).
% 0.23/0.44  fof(f9,conjecture,(
% 0.23/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).
% 0.23/0.44  fof(f78,plain,(
% 0.23/0.44    spl3_7),
% 0.23/0.44    inference(avatar_split_clause,[],[f28,f75])).
% 0.23/0.44  fof(f28,plain,(
% 0.23/0.44    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.44    inference(cnf_transformation,[],[f24])).
% 0.23/0.44  fof(f73,plain,(
% 0.23/0.44    spl3_6),
% 0.23/0.44    inference(avatar_split_clause,[],[f27,f70])).
% 0.23/0.44  fof(f27,plain,(
% 0.23/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.44    inference(cnf_transformation,[],[f24])).
% 0.23/0.44  fof(f68,plain,(
% 0.23/0.44    spl3_5),
% 0.23/0.44    inference(avatar_split_clause,[],[f31,f65])).
% 0.23/0.44  fof(f31,plain,(
% 0.23/0.44    v2_compts_1(sK2,sK0)),
% 0.23/0.44    inference(cnf_transformation,[],[f24])).
% 0.23/0.44  fof(f63,plain,(
% 0.23/0.44    spl3_4),
% 0.23/0.44    inference(avatar_split_clause,[],[f30,f60])).
% 0.23/0.44  fof(f30,plain,(
% 0.23/0.44    v2_compts_1(sK1,sK0)),
% 0.23/0.44    inference(cnf_transformation,[],[f24])).
% 0.23/0.44  fof(f58,plain,(
% 0.23/0.44    spl3_3),
% 0.23/0.44    inference(avatar_split_clause,[],[f29,f55])).
% 0.23/0.44  fof(f29,plain,(
% 0.23/0.44    v8_pre_topc(sK0)),
% 0.23/0.44    inference(cnf_transformation,[],[f24])).
% 0.23/0.44  fof(f53,plain,(
% 0.23/0.44    spl3_2),
% 0.23/0.44    inference(avatar_split_clause,[],[f26,f50])).
% 0.23/0.44  fof(f26,plain,(
% 0.23/0.44    l1_pre_topc(sK0)),
% 0.23/0.44    inference(cnf_transformation,[],[f24])).
% 0.23/0.44  fof(f48,plain,(
% 0.23/0.44    spl3_1),
% 0.23/0.44    inference(avatar_split_clause,[],[f25,f45])).
% 0.23/0.44  fof(f25,plain,(
% 0.23/0.44    v2_pre_topc(sK0)),
% 0.23/0.44    inference(cnf_transformation,[],[f24])).
% 0.23/0.44  % SZS output end Proof for theBenchmark
% 0.23/0.44  % (14527)------------------------------
% 0.23/0.44  % (14527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.44  % (14527)Termination reason: Refutation
% 0.23/0.44  
% 0.23/0.44  % (14527)Memory used [KB]: 10746
% 0.23/0.44  % (14527)Time elapsed: 0.039 s
% 0.23/0.44  % (14527)------------------------------
% 0.23/0.44  % (14527)------------------------------
% 0.23/0.45  % (14511)Success in time 0.073 s
%------------------------------------------------------------------------------
