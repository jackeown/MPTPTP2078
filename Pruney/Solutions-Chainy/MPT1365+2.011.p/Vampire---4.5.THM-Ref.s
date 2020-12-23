%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 210 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  269 (1016 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (28570)Refutation not found, incomplete strategy% (28570)------------------------------
% (28570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28570)Termination reason: Refutation not found, incomplete strategy

% (28570)Memory used [KB]: 6140
% (28570)Time elapsed: 0.055 s
% (28570)------------------------------
% (28570)------------------------------
fof(f141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f88,f90,f92,f96,f104,f110,f112,f114,f125,f135,f140])).

fof(f140,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl3_11 ),
    inference(resolution,[],[f124,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f30,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f124,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_11
  <=> r1_tarski(k3_xboole_0(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f135,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f121,f23])).

fof(f23,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_compts_1)).

fof(f121,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl3_10
  <=> v2_compts_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f125,plain,
    ( ~ spl3_10
    | ~ spl3_11
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f115,f66,f123,f120])).

fof(f66,plain,
    ( spl3_3
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
        | ~ v2_compts_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f115,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ v2_compts_1(sK2,sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f67,f20])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
        | ~ v2_compts_1(X0,sK0) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f114,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f81,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f81,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f112,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f75,f20])).

fof(f75,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f110,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f84,f53])).

fof(f53,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f21,f26,f27,f22,f49])).

fof(f49,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_compts_1(sK1,sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f28,f25])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_compts_1(X1,X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
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
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

fof(f22,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f21,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f84,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_8
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f104,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f78,f52])).

fof(f52,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(global_subsumption,[],[f21,f26,f27,f23,f48])).

fof(f48,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_compts_1(sK2,sK0)
    | v4_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f28,f20])).

fof(f78,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_6
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f96,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f87,f27])).

fof(f87,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f92,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f72,f26])).

fof(f72,plain,
    ( ~ v2_pre_topc(sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f90,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | spl3_2 ),
    inference(resolution,[],[f64,f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f20,f43])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f32,f39])).

fof(f39,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2) ),
    inference(resolution,[],[f33,f20])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f64,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_2
  <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f88,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | spl3_1 ),
    inference(avatar_split_clause,[],[f69,f60,f86,f83,f80,f77,f74,f71])).

fof(f60,plain,
    ( spl3_1
  <=> v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f69,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | spl3_1 ),
    inference(resolution,[],[f61,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tops_1)).

fof(f61,plain,
    ( ~ v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f68,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f58,f66,f63,f60])).

fof(f58,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
      | ~ v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) ) ),
    inference(global_subsumption,[],[f26,f27,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
      | ~ v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f29,f42])).

fof(f42,plain,(
    ~ v2_compts_1(k3_xboole_0(sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f24,f39])).

fof(f24,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (28573)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.47  % (28565)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.48  % (28573)Refutation not found, incomplete strategy% (28573)------------------------------
% 0.21/0.48  % (28573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (28573)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (28573)Memory used [KB]: 10490
% 0.21/0.48  % (28573)Time elapsed: 0.075 s
% 0.21/0.48  % (28573)------------------------------
% 0.21/0.48  % (28573)------------------------------
% 0.21/0.48  % (28575)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (28570)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (28574)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.49  % (28575)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  % (28570)Refutation not found, incomplete strategy% (28570)------------------------------
% 0.21/0.49  % (28570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (28570)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (28570)Memory used [KB]: 6140
% 0.21/0.49  % (28570)Time elapsed: 0.055 s
% 0.21/0.49  % (28570)------------------------------
% 0.21/0.49  % (28570)------------------------------
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f68,f88,f90,f92,f96,f104,f110,f112,f114,f125,f135,f140])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl3_11),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f139])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    $false | spl3_11),
% 0.21/0.49    inference(resolution,[],[f124,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.21/0.49    inference(superposition,[],[f30,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl3_11 <=> r1_tarski(k3_xboole_0(sK1,sK2),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    spl3_10),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f133])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    $false | spl3_10),
% 0.21/0.49    inference(resolution,[],[f121,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    v2_compts_1(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_compts_1)).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ~v2_compts_1(sK2,sK0) | spl3_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl3_10 <=> v2_compts_1(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ~spl3_10 | ~spl3_11 | ~spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f115,f66,f123,f120])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl3_3 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~v2_compts_1(X0,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~v2_compts_1(sK2,sK0) | ~spl3_3),
% 0.21/0.49    inference(resolution,[],[f67,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~v2_compts_1(X0,sK0)) ) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl3_7),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f113])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    $false | spl3_7),
% 0.21/0.49    inference(resolution,[],[f81,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl3_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl3_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    $false | spl3_5),
% 0.21/0.49    inference(resolution,[],[f75,f20])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl3_8),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    $false | spl3_8),
% 0.21/0.49    inference(resolution,[],[f84,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    v4_pre_topc(sK1,sK0)),
% 0.21/0.49    inference(global_subsumption,[],[f21,f26,f27,f22,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_compts_1(sK1,sK0) | v4_pre_topc(sK1,sK0)),
% 0.21/0.49    inference(resolution,[],[f28,f25])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_compts_1(X1,X0) | v4_pre_topc(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    v2_compts_1(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    v8_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ~v4_pre_topc(sK1,sK0) | spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl3_8 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl3_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f103])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    $false | spl3_6),
% 0.21/0.49    inference(resolution,[],[f78,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    v4_pre_topc(sK2,sK0)),
% 0.21/0.49    inference(global_subsumption,[],[f21,f26,f27,f23,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_compts_1(sK2,sK0) | v4_pre_topc(sK2,sK0)),
% 0.21/0.49    inference(resolution,[],[f28,f20])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ~v4_pre_topc(sK2,sK0) | spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl3_6 <=> v4_pre_topc(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl3_9),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    $false | spl3_9),
% 0.21/0.49    inference(resolution,[],[f87,f27])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl3_9 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    $false | spl3_4),
% 0.21/0.49    inference(resolution,[],[f72,f26])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl3_4 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl3_2),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    $false | spl3_2),
% 0.21/0.49    inference(resolution,[],[f64,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.49    inference(global_subsumption,[],[f20,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.49    inference(superposition,[],[f32,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2)) )),
% 0.21/0.49    inference(resolution,[],[f33,f20])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl3_2 <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_9 | spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f69,f60,f86,f83,f80,f77,f74,f71])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl3_1 <=> v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | spl3_1),
% 0.21/0.49    inference(resolution,[],[f61,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k3_xboole_0(X1,X2),X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tops_1)).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ~v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f60])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_2 | spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f58,f66,f63,f60])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X0,sK0) | ~r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)) )),
% 0.21/0.49    inference(global_subsumption,[],[f26,f27,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X0,sK0) | ~r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f29,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ~v2_compts_1(k3_xboole_0(sK1,sK2),sK0)),
% 0.21/0.49    inference(backward_demodulation,[],[f24,f39])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X2,X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (28575)------------------------------
% 0.21/0.49  % (28575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (28575)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (28575)Memory used [KB]: 10618
% 0.21/0.49  % (28575)Time elapsed: 0.086 s
% 0.21/0.49  % (28575)------------------------------
% 0.21/0.49  % (28575)------------------------------
% 0.21/0.49  % (28562)Success in time 0.137 s
%------------------------------------------------------------------------------
