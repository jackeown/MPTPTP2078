%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:50 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 475 expanded)
%              Number of leaves         :   23 ( 146 expanded)
%              Depth                    :   19
%              Number of atoms          :  466 (2633 expanded)
%              Number of equality atoms :   94 ( 209 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f775,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f464,f493,f774])).

fof(f774,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f773])).

fof(f773,plain,
    ( $false
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f772,f56])).

fof(f56,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ v3_tex_2(sK3,sK2)
    & v2_tex_2(sK3,sK2)
    & v1_tops_1(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tex_2(X1,X0)
            & v2_tex_2(X1,X0)
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v3_tex_2(X1,sK2)
          & v2_tex_2(X1,sK2)
          & v1_tops_1(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ~ v3_tex_2(X1,sK2)
        & v2_tex_2(X1,sK2)
        & v1_tops_1(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ~ v3_tex_2(sK3,sK2)
      & v2_tex_2(sK3,sK2)
      & v1_tops_1(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v2_tex_2(X1,X0)
                & v1_tops_1(X1,X0) )
             => v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

fof(f772,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f771,f135])).

fof(f135,plain,(
    ~ sP0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f133,f57])).

fof(f57,plain,(
    ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f133,plain,
    ( ~ sP0(sK3,sK2)
    | v3_tex_2(sK3,sK2) ),
    inference(resolution,[],[f132,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v3_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f132,plain,(
    sP1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f128,f53])).

fof(f53,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f128,plain,
    ( sP1(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f69,f54])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f21,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f771,plain,
    ( sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f740,f91])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f740,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ spl6_6 ),
    inference(superposition,[],[f159,f706])).

fof(f706,plain,
    ( sK3 = sK4(sK3,sK2)
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f446,f459])).

fof(f459,plain,
    ( sK3 = k1_setfam_1(k2_tarski(sK4(sK3,sK2),u1_struct_0(sK2)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl6_6
  <=> sK3 = k1_setfam_1(k2_tarski(sK4(sK3,sK2),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f446,plain,(
    sK4(sK3,sK2) = k1_setfam_1(k2_tarski(sK4(sK3,sK2),u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f441,f178])).

fof(f178,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f165,f177])).

fof(f177,plain,(
    ! [X1] : k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f173,f168])).

fof(f168,plain,(
    ! [X1] : k1_xboole_0 = k3_subset_1(X1,X1) ),
    inference(forward_demodulation,[],[f166,f98])).

fof(f98,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f86,f91])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f166,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k3_subset_1(X1,X1) ),
    inference(resolution,[],[f78,f93])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f60,f58])).

fof(f58,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f173,plain,(
    ! [X1] : k3_subset_1(X1,k3_subset_1(X1,X1)) = X1 ),
    inference(resolution,[],[f79,f93])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f165,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f78,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f441,plain,(
    k1_setfam_1(k2_tarski(sK4(sK3,sK2),u1_struct_0(sK2))) = k4_xboole_0(sK4(sK3,sK2),k1_xboole_0) ),
    inference(superposition,[],[f89,f439])).

fof(f439,plain,(
    k1_xboole_0 = k4_xboole_0(sK4(sK3,sK2),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f437,f135])).

fof(f437,plain,
    ( sP0(sK3,sK2)
    | k1_xboole_0 = k4_xboole_0(sK4(sK3,sK2),u1_struct_0(sK2)) ),
    inference(resolution,[],[f342,f56])).

fof(f342,plain,(
    ! [X10,X9] :
      ( ~ v2_tex_2(X9,X10)
      | sP0(X9,X10)
      | k1_xboole_0 = k4_xboole_0(sK4(X9,X10),u1_struct_0(X10)) ) ),
    inference(resolution,[],[f189,f86])).

fof(f189,plain,(
    ! [X10,X9] :
      ( r1_tarski(sK4(X9,X10),u1_struct_0(X10))
      | ~ v2_tex_2(X9,X10)
      | sP0(X9,X10) ) ),
    inference(resolution,[],[f65,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK4(X0,X1) != X0
          & r1_tarski(X0,sK4(X0,X1))
          & v2_tex_2(sK4(X0,X1),X1)
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ v2_tex_2(X0,X1) )
      & ( ( ! [X3] :
              ( X0 = X3
              | ~ r1_tarski(X0,X3)
              | ~ v2_tex_2(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & v2_tex_2(X0,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK4(X0,X1) != X0
        & r1_tarski(X0,sK4(X0,X1))
        & v2_tex_2(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( X0 != X2
            & r1_tarski(X0,X2)
            & v2_tex_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ v2_tex_2(X0,X1) )
      & ( ( ! [X3] :
              ( X0 = X3
              | ~ r1_tarski(X0,X3)
              | ~ v2_tex_2(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & v2_tex_2(X0,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ v2_tex_2(X1,X0) )
      & ( ( ! [X2] :
              ( X1 = X2
              | ~ r1_tarski(X1,X2)
              | ~ v2_tex_2(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v2_tex_2(X1,X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ v2_tex_2(X1,X0) )
      & ( ( ! [X2] :
              ( X1 = X2
              | ~ r1_tarski(X1,X2)
              | ~ v2_tex_2(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v2_tex_2(X1,X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f89,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f77,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4(X0,X1),X0)
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(subsumption_resolution,[],[f157,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,sK4(X0,X1))
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK4(X0,X1))
      | ~ r1_tarski(sK4(X0,X1),X0)
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(extensionality_resolution,[],[f82,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X0
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f493,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f492])).

fof(f492,plain,
    ( $false
    | spl6_7 ),
    inference(subsumption_resolution,[],[f491,f56])).

fof(f491,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | spl6_7 ),
    inference(subsumption_resolution,[],[f490,f135])).

fof(f490,plain,
    ( sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | spl6_7 ),
    inference(resolution,[],[f463,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK4(X0,X1),X1)
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f463,plain,
    ( ~ v2_tex_2(sK4(sK3,sK2),sK2)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f461])).

fof(f461,plain,
    ( spl6_7
  <=> v2_tex_2(sK4(sK3,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f464,plain,
    ( spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f455,f461,f457])).

fof(f455,plain,
    ( ~ v2_tex_2(sK4(sK3,sK2),sK2)
    | sK3 = k1_setfam_1(k2_tarski(sK4(sK3,sK2),u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f448,f377])).

fof(f377,plain,(
    r1_tarski(sK3,sK4(sK3,sK2)) ),
    inference(trivial_inequality_removal,[],[f376])).

fof(f376,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK3,sK4(sK3,sK2)) ),
    inference(superposition,[],[f85,f372])).

fof(f372,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f370,f135])).

fof(f370,plain,
    ( sP0(sK3,sK2)
    | k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2)) ),
    inference(resolution,[],[f154,f56])).

fof(f154,plain,(
    ! [X2,X3] :
      ( ~ v2_tex_2(X2,X3)
      | sP0(X2,X3)
      | k1_xboole_0 = k4_xboole_0(X2,sK4(X2,X3)) ) ),
    inference(resolution,[],[f67,f86])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f448,plain,
    ( ~ v2_tex_2(sK4(sK3,sK2),sK2)
    | sK3 = k1_setfam_1(k2_tarski(sK4(sK3,sK2),u1_struct_0(sK2)))
    | ~ r1_tarski(sK3,sK4(sK3,sK2)) ),
    inference(resolution,[],[f444,f404])).

fof(f404,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ v2_tex_2(X0,sK2)
      | sK3 = k1_setfam_1(k2_tarski(X0,u1_struct_0(sK2)))
      | ~ r1_tarski(sK3,X0) ) ),
    inference(resolution,[],[f329,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f329,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(sK3,X7)
      | ~ v2_tex_2(X7,sK2)
      | sK3 = k1_setfam_1(k2_tarski(X7,u1_struct_0(sK2))) ) ),
    inference(forward_demodulation,[],[f328,f193])).

fof(f193,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(resolution,[],[f90,f93])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f87,f76])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f328,plain,(
    ! [X7] :
      ( sK3 = k9_subset_1(u1_struct_0(sK2),X7,u1_struct_0(sK2))
      | ~ r1_tarski(sK3,X7)
      | ~ v2_tex_2(X7,sK2)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(forward_demodulation,[],[f327,f206])).

fof(f206,plain,(
    u1_struct_0(sK2) = k2_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f205,f53])).

% (6461)Termination reason: Refutation not found, incomplete strategy

% (6461)Memory used [KB]: 1791
% (6461)Time elapsed: 0.149 s
% (6461)------------------------------
% (6461)------------------------------
fof(f205,plain,
    ( u1_struct_0(sK2) = k2_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f203,f55])).

fof(f55,plain,(
    v1_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f203,plain,
    ( ~ v1_tops_1(sK3,sK2)
    | u1_struct_0(sK2) = k2_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f70,f54])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f327,plain,(
    ! [X7] :
      ( ~ r1_tarski(sK3,X7)
      | sK3 = k9_subset_1(u1_struct_0(sK2),X7,k2_pre_topc(sK2,sK3))
      | ~ v2_tex_2(X7,sK2)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f326,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f326,plain,(
    ! [X7] :
      ( ~ r1_tarski(sK3,X7)
      | sK3 = k9_subset_1(u1_struct_0(sK2),X7,k2_pre_topc(sK2,sK3))
      | ~ v2_tex_2(X7,sK2)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f325,f52])).

fof(f52,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f325,plain,(
    ! [X7] :
      ( ~ r1_tarski(sK3,X7)
      | sK3 = k9_subset_1(u1_struct_0(sK2),X7,k2_pre_topc(sK2,sK3))
      | ~ v2_tex_2(X7,sK2)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f320,f53])).

fof(f320,plain,(
    ! [X7] :
      ( ~ r1_tarski(sK3,X7)
      | sK3 = k9_subset_1(u1_struct_0(sK2),X7,k2_pre_topc(sK2,sK3))
      | ~ v2_tex_2(X7,sK2)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f72,f54])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X3,X1)
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1)))
                & r1_tarski(sK5(X0,X1),X1)
                & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1)))
        & r1_tarski(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

fof(f444,plain,(
    r1_tarski(sK4(sK3,sK2),u1_struct_0(sK2)) ),
    inference(trivial_inequality_removal,[],[f443])).

fof(f443,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK4(sK3,sK2),u1_struct_0(sK2)) ),
    inference(superposition,[],[f85,f439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:46:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.16/0.52  % (6436)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.16/0.53  % (6454)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.16/0.53  % (6442)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.16/0.53  % (6433)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.16/0.53  % (6437)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.31/0.53  % (6445)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.31/0.54  % (6459)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.31/0.54  % (6435)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.31/0.54  % (6434)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.31/0.54  % (6457)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.31/0.54  % (6438)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.54  % (6432)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.31/0.55  % (6433)Refutation not found, incomplete strategy% (6433)------------------------------
% 1.31/0.55  % (6433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (6449)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.31/0.55  % (6442)Refutation not found, incomplete strategy% (6442)------------------------------
% 1.31/0.55  % (6442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (6442)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (6442)Memory used [KB]: 10746
% 1.31/0.55  % (6442)Time elapsed: 0.126 s
% 1.31/0.55  % (6442)------------------------------
% 1.31/0.55  % (6442)------------------------------
% 1.31/0.55  % (6448)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.31/0.55  % (6441)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.31/0.55  % (6461)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.31/0.55  % (6451)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.31/0.55  % (6448)Refutation not found, incomplete strategy% (6448)------------------------------
% 1.31/0.55  % (6448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (6453)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.31/0.55  % (6452)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.31/0.55  % (6455)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.31/0.55  % (6440)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.31/0.55  % (6458)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.31/0.55  % (6443)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.31/0.55  % (6450)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.31/0.56  % (6456)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.31/0.56  % (6460)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.31/0.56  % (6444)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.31/0.56  % (6447)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.31/0.56  % (6461)Refutation not found, incomplete strategy% (6461)------------------------------
% 1.31/0.56  % (6461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (6433)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (6433)Memory used [KB]: 1791
% 1.31/0.56  % (6433)Time elapsed: 0.130 s
% 1.31/0.56  % (6433)------------------------------
% 1.31/0.56  % (6433)------------------------------
% 1.31/0.56  % (6446)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.31/0.56  % (6458)Refutation not found, incomplete strategy% (6458)------------------------------
% 1.31/0.56  % (6458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (6458)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (6458)Memory used [KB]: 6396
% 1.31/0.56  % (6458)Time elapsed: 0.143 s
% 1.31/0.56  % (6458)------------------------------
% 1.31/0.56  % (6458)------------------------------
% 1.31/0.57  % (6446)Refutation not found, incomplete strategy% (6446)------------------------------
% 1.31/0.57  % (6446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.57  % (6446)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.57  
% 1.31/0.57  % (6446)Memory used [KB]: 1791
% 1.31/0.57  % (6446)Time elapsed: 0.152 s
% 1.31/0.57  % (6446)------------------------------
% 1.31/0.57  % (6446)------------------------------
% 1.31/0.57  % (6439)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.31/0.57  % (6448)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.57  
% 1.31/0.57  % (6448)Memory used [KB]: 10746
% 1.31/0.57  % (6448)Time elapsed: 0.130 s
% 1.31/0.57  % (6448)------------------------------
% 1.31/0.57  % (6448)------------------------------
% 1.31/0.57  % (6460)Refutation not found, incomplete strategy% (6460)------------------------------
% 1.31/0.57  % (6460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.57  % (6460)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.57  
% 1.31/0.57  % (6460)Memory used [KB]: 10746
% 1.31/0.57  % (6460)Time elapsed: 0.150 s
% 1.31/0.57  % (6460)------------------------------
% 1.31/0.57  % (6460)------------------------------
% 1.31/0.57  % (6438)Refutation found. Thanks to Tanya!
% 1.31/0.57  % SZS status Theorem for theBenchmark
% 1.31/0.57  % SZS output start Proof for theBenchmark
% 1.31/0.57  fof(f775,plain,(
% 1.31/0.57    $false),
% 1.31/0.57    inference(avatar_sat_refutation,[],[f464,f493,f774])).
% 1.31/0.57  fof(f774,plain,(
% 1.31/0.57    ~spl6_6),
% 1.31/0.57    inference(avatar_contradiction_clause,[],[f773])).
% 1.31/0.57  fof(f773,plain,(
% 1.31/0.57    $false | ~spl6_6),
% 1.31/0.57    inference(subsumption_resolution,[],[f772,f56])).
% 1.31/0.57  fof(f56,plain,(
% 1.31/0.57    v2_tex_2(sK3,sK2)),
% 1.31/0.57    inference(cnf_transformation,[],[f35])).
% 1.31/0.57  fof(f35,plain,(
% 1.31/0.57    (~v3_tex_2(sK3,sK2) & v2_tex_2(sK3,sK2) & v1_tops_1(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.31/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f34,f33])).
% 1.31/0.57  fof(f33,plain,(
% 1.31/0.57    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v3_tex_2(X1,sK2) & v2_tex_2(X1,sK2) & v1_tops_1(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.31/0.57    introduced(choice_axiom,[])).
% 1.31/0.57  fof(f34,plain,(
% 1.31/0.57    ? [X1] : (~v3_tex_2(X1,sK2) & v2_tex_2(X1,sK2) & v1_tops_1(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => (~v3_tex_2(sK3,sK2) & v2_tex_2(sK3,sK2) & v1_tops_1(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.31/0.57    introduced(choice_axiom,[])).
% 1.31/0.57  fof(f19,plain,(
% 1.31/0.57    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.31/0.57    inference(flattening,[],[f18])).
% 1.31/0.57  fof(f18,plain,(
% 1.31/0.57    ? [X0] : (? [X1] : ((~v3_tex_2(X1,X0) & (v2_tex_2(X1,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.31/0.57    inference(ennf_transformation,[],[f17])).
% 1.31/0.57  fof(f17,negated_conjecture,(
% 1.31/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 1.31/0.57    inference(negated_conjecture,[],[f16])).
% 1.31/0.57  fof(f16,conjecture,(
% 1.31/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
% 1.31/0.57  fof(f772,plain,(
% 1.31/0.57    ~v2_tex_2(sK3,sK2) | ~spl6_6),
% 1.31/0.57    inference(subsumption_resolution,[],[f771,f135])).
% 1.31/0.57  fof(f135,plain,(
% 1.31/0.57    ~sP0(sK3,sK2)),
% 1.31/0.57    inference(subsumption_resolution,[],[f133,f57])).
% 1.31/0.57  fof(f57,plain,(
% 1.31/0.57    ~v3_tex_2(sK3,sK2)),
% 1.31/0.57    inference(cnf_transformation,[],[f35])).
% 1.31/0.57  fof(f133,plain,(
% 1.31/0.57    ~sP0(sK3,sK2) | v3_tex_2(sK3,sK2)),
% 1.31/0.57    inference(resolution,[],[f132,f62])).
% 1.31/0.57  fof(f62,plain,(
% 1.31/0.57    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v3_tex_2(X1,X0)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f36])).
% 1.31/0.57  fof(f36,plain,(
% 1.31/0.57    ! [X0,X1] : (((v3_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v3_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 1.31/0.57    inference(nnf_transformation,[],[f31])).
% 1.31/0.57  fof(f31,plain,(
% 1.31/0.57    ! [X0,X1] : ((v3_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 1.31/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.31/0.57  fof(f132,plain,(
% 1.31/0.57    sP1(sK2,sK3)),
% 1.31/0.57    inference(subsumption_resolution,[],[f128,f53])).
% 1.31/0.57  fof(f53,plain,(
% 1.31/0.57    l1_pre_topc(sK2)),
% 1.31/0.57    inference(cnf_transformation,[],[f35])).
% 1.31/0.57  fof(f128,plain,(
% 1.31/0.57    sP1(sK2,sK3) | ~l1_pre_topc(sK2)),
% 1.31/0.57    inference(resolution,[],[f69,f54])).
% 1.31/0.57  fof(f54,plain,(
% 1.31/0.57    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.31/0.57    inference(cnf_transformation,[],[f35])).
% 1.31/0.57  fof(f69,plain,(
% 1.31/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f32])).
% 1.31/0.57  fof(f32,plain,(
% 1.31/0.57    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.57    inference(definition_folding,[],[f21,f31,f30])).
% 1.31/0.57  fof(f30,plain,(
% 1.31/0.57    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)))),
% 1.31/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.31/0.57  fof(f21,plain,(
% 1.31/0.57    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.57    inference(flattening,[],[f20])).
% 1.31/0.57  fof(f20,plain,(
% 1.31/0.57    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.57    inference(ennf_transformation,[],[f14])).
% 1.31/0.57  fof(f14,axiom,(
% 1.31/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 1.31/0.57  fof(f771,plain,(
% 1.31/0.57    sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | ~spl6_6),
% 1.31/0.57    inference(subsumption_resolution,[],[f740,f91])).
% 1.31/0.57  fof(f91,plain,(
% 1.31/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.31/0.57    inference(equality_resolution,[],[f81])).
% 1.31/0.57  fof(f81,plain,(
% 1.31/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.31/0.57    inference(cnf_transformation,[],[f48])).
% 1.31/0.57  fof(f48,plain,(
% 1.31/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.57    inference(flattening,[],[f47])).
% 1.31/0.57  fof(f47,plain,(
% 1.31/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.57    inference(nnf_transformation,[],[f1])).
% 1.31/0.57  fof(f1,axiom,(
% 1.31/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.31/0.57  fof(f740,plain,(
% 1.31/0.57    ~r1_tarski(sK3,sK3) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | ~spl6_6),
% 1.31/0.57    inference(superposition,[],[f159,f706])).
% 1.31/0.57  fof(f706,plain,(
% 1.31/0.57    sK3 = sK4(sK3,sK2) | ~spl6_6),
% 1.31/0.57    inference(forward_demodulation,[],[f446,f459])).
% 1.31/0.57  fof(f459,plain,(
% 1.31/0.57    sK3 = k1_setfam_1(k2_tarski(sK4(sK3,sK2),u1_struct_0(sK2))) | ~spl6_6),
% 1.31/0.57    inference(avatar_component_clause,[],[f457])).
% 1.31/0.57  fof(f457,plain,(
% 1.31/0.57    spl6_6 <=> sK3 = k1_setfam_1(k2_tarski(sK4(sK3,sK2),u1_struct_0(sK2)))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.31/0.57  fof(f446,plain,(
% 1.31/0.57    sK4(sK3,sK2) = k1_setfam_1(k2_tarski(sK4(sK3,sK2),u1_struct_0(sK2)))),
% 1.31/0.57    inference(forward_demodulation,[],[f441,f178])).
% 1.31/0.57  fof(f178,plain,(
% 1.31/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.31/0.57    inference(backward_demodulation,[],[f165,f177])).
% 1.31/0.57  fof(f177,plain,(
% 1.31/0.57    ( ! [X1] : (k3_subset_1(X1,k1_xboole_0) = X1) )),
% 1.31/0.57    inference(forward_demodulation,[],[f173,f168])).
% 1.31/0.57  fof(f168,plain,(
% 1.31/0.57    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,X1)) )),
% 1.31/0.57    inference(forward_demodulation,[],[f166,f98])).
% 1.31/0.57  fof(f98,plain,(
% 1.31/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.31/0.57    inference(resolution,[],[f86,f91])).
% 1.31/0.57  fof(f86,plain,(
% 1.31/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.31/0.57    inference(cnf_transformation,[],[f50])).
% 1.31/0.57  fof(f50,plain,(
% 1.31/0.57    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.31/0.57    inference(nnf_transformation,[],[f2])).
% 1.31/0.57  fof(f2,axiom,(
% 1.31/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.31/0.57  fof(f166,plain,(
% 1.31/0.57    ( ! [X1] : (k4_xboole_0(X1,X1) = k3_subset_1(X1,X1)) )),
% 1.31/0.57    inference(resolution,[],[f78,f93])).
% 1.31/0.57  fof(f93,plain,(
% 1.31/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.31/0.57    inference(forward_demodulation,[],[f60,f58])).
% 1.31/0.57  fof(f58,plain,(
% 1.31/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.31/0.57    inference(cnf_transformation,[],[f4])).
% 1.31/0.57  fof(f4,axiom,(
% 1.31/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.31/0.57  fof(f60,plain,(
% 1.31/0.57    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.31/0.57    inference(cnf_transformation,[],[f6])).
% 1.31/0.57  fof(f6,axiom,(
% 1.31/0.57    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.31/0.57  fof(f78,plain,(
% 1.31/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f25])).
% 1.31/0.57  fof(f25,plain,(
% 1.31/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.31/0.57    inference(ennf_transformation,[],[f5])).
% 1.31/0.57  fof(f5,axiom,(
% 1.31/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.31/0.57  fof(f173,plain,(
% 1.31/0.57    ( ! [X1] : (k3_subset_1(X1,k3_subset_1(X1,X1)) = X1) )),
% 1.31/0.57    inference(resolution,[],[f79,f93])).
% 1.31/0.57  fof(f79,plain,(
% 1.31/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.31/0.57    inference(cnf_transformation,[],[f26])).
% 1.31/0.57  fof(f26,plain,(
% 1.31/0.57    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.31/0.57    inference(ennf_transformation,[],[f7])).
% 1.31/0.57  fof(f7,axiom,(
% 1.31/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.31/0.57  fof(f165,plain,(
% 1.31/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.31/0.57    inference(resolution,[],[f78,f59])).
% 1.31/0.57  fof(f59,plain,(
% 1.31/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.31/0.57    inference(cnf_transformation,[],[f9])).
% 1.31/0.57  fof(f9,axiom,(
% 1.31/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.31/0.57  fof(f441,plain,(
% 1.31/0.57    k1_setfam_1(k2_tarski(sK4(sK3,sK2),u1_struct_0(sK2))) = k4_xboole_0(sK4(sK3,sK2),k1_xboole_0)),
% 1.31/0.57    inference(superposition,[],[f89,f439])).
% 1.31/0.58  fof(f439,plain,(
% 1.31/0.58    k1_xboole_0 = k4_xboole_0(sK4(sK3,sK2),u1_struct_0(sK2))),
% 1.31/0.58    inference(subsumption_resolution,[],[f437,f135])).
% 1.31/0.58  fof(f437,plain,(
% 1.31/0.58    sP0(sK3,sK2) | k1_xboole_0 = k4_xboole_0(sK4(sK3,sK2),u1_struct_0(sK2))),
% 1.31/0.58    inference(resolution,[],[f342,f56])).
% 1.31/0.58  fof(f342,plain,(
% 1.31/0.58    ( ! [X10,X9] : (~v2_tex_2(X9,X10) | sP0(X9,X10) | k1_xboole_0 = k4_xboole_0(sK4(X9,X10),u1_struct_0(X10))) )),
% 1.31/0.58    inference(resolution,[],[f189,f86])).
% 1.31/0.58  fof(f189,plain,(
% 1.31/0.58    ( ! [X10,X9] : (r1_tarski(sK4(X9,X10),u1_struct_0(X10)) | ~v2_tex_2(X9,X10) | sP0(X9,X10)) )),
% 1.31/0.58    inference(resolution,[],[f65,f83])).
% 1.31/0.58  fof(f83,plain,(
% 1.31/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.31/0.58    inference(cnf_transformation,[],[f49])).
% 1.31/0.58  fof(f49,plain,(
% 1.31/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.31/0.58    inference(nnf_transformation,[],[f11])).
% 1.31/0.58  fof(f11,axiom,(
% 1.31/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.31/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.31/0.58  fof(f65,plain,(
% 1.31/0.58    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.31/0.58    inference(cnf_transformation,[],[f41])).
% 1.31/0.58  fof(f41,plain,(
% 1.31/0.58    ! [X0,X1] : ((sP0(X0,X1) | (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 1.31/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).
% 1.31/0.58  fof(f40,plain,(
% 1.31/0.58    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.31/0.58    introduced(choice_axiom,[])).
% 1.31/0.58  fof(f39,plain,(
% 1.31/0.58    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 1.31/0.58    inference(rectify,[],[f38])).
% 1.31/0.58  fof(f38,plain,(
% 1.31/0.58    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 1.31/0.58    inference(flattening,[],[f37])).
% 1.31/0.58  fof(f37,plain,(
% 1.31/0.58    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 1.31/0.58    inference(nnf_transformation,[],[f30])).
% 1.31/0.58  fof(f89,plain,(
% 1.31/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.31/0.58    inference(definition_unfolding,[],[f77,f76])).
% 1.31/0.58  fof(f76,plain,(
% 1.31/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.31/0.58    inference(cnf_transformation,[],[f10])).
% 1.31/0.58  fof(f10,axiom,(
% 1.31/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.31/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.31/0.58  fof(f77,plain,(
% 1.31/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.31/0.58    inference(cnf_transformation,[],[f3])).
% 1.31/0.58  fof(f3,axiom,(
% 1.31/0.58    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.31/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.31/0.58  fof(f159,plain,(
% 1.31/0.58    ( ! [X0,X1] : (~r1_tarski(sK4(X0,X1),X0) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.31/0.58    inference(subsumption_resolution,[],[f157,f67])).
% 1.31/0.58  fof(f67,plain,(
% 1.31/0.58    ( ! [X0,X1] : (r1_tarski(X0,sK4(X0,X1)) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.31/0.58    inference(cnf_transformation,[],[f41])).
% 1.31/0.58  fof(f157,plain,(
% 1.31/0.58    ( ! [X0,X1] : (~r1_tarski(X0,sK4(X0,X1)) | ~r1_tarski(sK4(X0,X1),X0) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.31/0.58    inference(extensionality_resolution,[],[f82,f68])).
% 1.31/0.58  fof(f68,plain,(
% 1.31/0.58    ( ! [X0,X1] : (sK4(X0,X1) != X0 | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.31/0.58    inference(cnf_transformation,[],[f41])).
% 1.31/0.58  fof(f82,plain,(
% 1.31/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.31/0.58    inference(cnf_transformation,[],[f48])).
% 1.31/0.58  fof(f493,plain,(
% 1.31/0.58    spl6_7),
% 1.31/0.58    inference(avatar_contradiction_clause,[],[f492])).
% 1.31/0.58  fof(f492,plain,(
% 1.31/0.58    $false | spl6_7),
% 1.31/0.58    inference(subsumption_resolution,[],[f491,f56])).
% 1.31/0.58  fof(f491,plain,(
% 1.31/0.58    ~v2_tex_2(sK3,sK2) | spl6_7),
% 1.31/0.58    inference(subsumption_resolution,[],[f490,f135])).
% 1.31/0.58  fof(f490,plain,(
% 1.31/0.58    sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | spl6_7),
% 1.31/0.58    inference(resolution,[],[f463,f66])).
% 1.31/0.58  fof(f66,plain,(
% 1.31/0.58    ( ! [X0,X1] : (v2_tex_2(sK4(X0,X1),X1) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.31/0.58    inference(cnf_transformation,[],[f41])).
% 1.31/0.58  fof(f463,plain,(
% 1.31/0.58    ~v2_tex_2(sK4(sK3,sK2),sK2) | spl6_7),
% 1.31/0.58    inference(avatar_component_clause,[],[f461])).
% 1.31/0.58  fof(f461,plain,(
% 1.31/0.58    spl6_7 <=> v2_tex_2(sK4(sK3,sK2),sK2)),
% 1.31/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.31/0.58  fof(f464,plain,(
% 1.31/0.58    spl6_6 | ~spl6_7),
% 1.31/0.58    inference(avatar_split_clause,[],[f455,f461,f457])).
% 1.31/0.58  fof(f455,plain,(
% 1.31/0.58    ~v2_tex_2(sK4(sK3,sK2),sK2) | sK3 = k1_setfam_1(k2_tarski(sK4(sK3,sK2),u1_struct_0(sK2)))),
% 1.31/0.58    inference(subsumption_resolution,[],[f448,f377])).
% 1.31/0.58  fof(f377,plain,(
% 1.31/0.58    r1_tarski(sK3,sK4(sK3,sK2))),
% 1.31/0.58    inference(trivial_inequality_removal,[],[f376])).
% 1.31/0.58  fof(f376,plain,(
% 1.31/0.58    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK3,sK4(sK3,sK2))),
% 1.31/0.58    inference(superposition,[],[f85,f372])).
% 1.31/0.58  fof(f372,plain,(
% 1.31/0.58    k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2))),
% 1.31/0.58    inference(subsumption_resolution,[],[f370,f135])).
% 1.31/0.58  fof(f370,plain,(
% 1.31/0.58    sP0(sK3,sK2) | k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2))),
% 1.31/0.58    inference(resolution,[],[f154,f56])).
% 1.31/0.58  fof(f154,plain,(
% 1.31/0.58    ( ! [X2,X3] : (~v2_tex_2(X2,X3) | sP0(X2,X3) | k1_xboole_0 = k4_xboole_0(X2,sK4(X2,X3))) )),
% 1.31/0.58    inference(resolution,[],[f67,f86])).
% 1.31/0.58  fof(f85,plain,(
% 1.31/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.31/0.58    inference(cnf_transformation,[],[f50])).
% 1.31/0.58  fof(f448,plain,(
% 1.31/0.58    ~v2_tex_2(sK4(sK3,sK2),sK2) | sK3 = k1_setfam_1(k2_tarski(sK4(sK3,sK2),u1_struct_0(sK2))) | ~r1_tarski(sK3,sK4(sK3,sK2))),
% 1.31/0.58    inference(resolution,[],[f444,f404])).
% 1.31/0.58  fof(f404,plain,(
% 1.31/0.58    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~v2_tex_2(X0,sK2) | sK3 = k1_setfam_1(k2_tarski(X0,u1_struct_0(sK2))) | ~r1_tarski(sK3,X0)) )),
% 1.31/0.58    inference(resolution,[],[f329,f84])).
% 1.31/0.58  fof(f84,plain,(
% 1.31/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.31/0.58    inference(cnf_transformation,[],[f49])).
% 1.31/0.58  fof(f329,plain,(
% 1.31/0.58    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(sK3,X7) | ~v2_tex_2(X7,sK2) | sK3 = k1_setfam_1(k2_tarski(X7,u1_struct_0(sK2)))) )),
% 1.31/0.58    inference(forward_demodulation,[],[f328,f193])).
% 1.31/0.58  fof(f193,plain,(
% 1.31/0.58    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.31/0.58    inference(resolution,[],[f90,f93])).
% 1.31/0.58  fof(f90,plain,(
% 1.31/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 1.31/0.58    inference(definition_unfolding,[],[f87,f76])).
% 1.31/0.58  fof(f87,plain,(
% 1.31/0.58    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.31/0.58    inference(cnf_transformation,[],[f27])).
% 1.31/0.58  fof(f27,plain,(
% 1.31/0.58    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.31/0.58    inference(ennf_transformation,[],[f8])).
% 1.31/0.58  fof(f8,axiom,(
% 1.31/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.31/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.31/0.58  fof(f328,plain,(
% 1.31/0.58    ( ! [X7] : (sK3 = k9_subset_1(u1_struct_0(sK2),X7,u1_struct_0(sK2)) | ~r1_tarski(sK3,X7) | ~v2_tex_2(X7,sK2) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.31/0.58    inference(forward_demodulation,[],[f327,f206])).
% 1.31/0.58  fof(f206,plain,(
% 1.31/0.58    u1_struct_0(sK2) = k2_pre_topc(sK2,sK3)),
% 1.31/0.58    inference(subsumption_resolution,[],[f205,f53])).
% 1.31/0.58  % (6461)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.58  
% 1.31/0.58  % (6461)Memory used [KB]: 1791
% 1.31/0.58  % (6461)Time elapsed: 0.149 s
% 1.31/0.58  % (6461)------------------------------
% 1.31/0.58  % (6461)------------------------------
% 1.31/0.58  fof(f205,plain,(
% 1.31/0.58    u1_struct_0(sK2) = k2_pre_topc(sK2,sK3) | ~l1_pre_topc(sK2)),
% 1.31/0.58    inference(subsumption_resolution,[],[f203,f55])).
% 1.31/0.58  fof(f55,plain,(
% 1.31/0.58    v1_tops_1(sK3,sK2)),
% 1.31/0.58    inference(cnf_transformation,[],[f35])).
% 1.31/0.58  fof(f203,plain,(
% 1.31/0.58    ~v1_tops_1(sK3,sK2) | u1_struct_0(sK2) = k2_pre_topc(sK2,sK3) | ~l1_pre_topc(sK2)),
% 1.31/0.58    inference(resolution,[],[f70,f54])).
% 1.31/0.58  fof(f70,plain,(
% 1.31/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.31/0.58    inference(cnf_transformation,[],[f42])).
% 1.31/0.58  fof(f42,plain,(
% 1.31/0.58    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.58    inference(nnf_transformation,[],[f22])).
% 1.31/0.58  fof(f22,plain,(
% 1.31/0.58    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.58    inference(ennf_transformation,[],[f13])).
% 1.31/0.58  fof(f13,axiom,(
% 1.31/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.31/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 1.31/0.58  fof(f327,plain,(
% 1.31/0.58    ( ! [X7] : (~r1_tarski(sK3,X7) | sK3 = k9_subset_1(u1_struct_0(sK2),X7,k2_pre_topc(sK2,sK3)) | ~v2_tex_2(X7,sK2) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.31/0.58    inference(subsumption_resolution,[],[f326,f51])).
% 1.31/0.58  fof(f51,plain,(
% 1.31/0.58    ~v2_struct_0(sK2)),
% 1.31/0.58    inference(cnf_transformation,[],[f35])).
% 1.31/0.58  fof(f326,plain,(
% 1.31/0.58    ( ! [X7] : (~r1_tarski(sK3,X7) | sK3 = k9_subset_1(u1_struct_0(sK2),X7,k2_pre_topc(sK2,sK3)) | ~v2_tex_2(X7,sK2) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)) )),
% 1.31/0.58    inference(subsumption_resolution,[],[f325,f52])).
% 1.31/0.58  fof(f52,plain,(
% 1.31/0.58    v2_pre_topc(sK2)),
% 1.31/0.58    inference(cnf_transformation,[],[f35])).
% 1.31/0.58  fof(f325,plain,(
% 1.31/0.58    ( ! [X7] : (~r1_tarski(sK3,X7) | sK3 = k9_subset_1(u1_struct_0(sK2),X7,k2_pre_topc(sK2,sK3)) | ~v2_tex_2(X7,sK2) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.31/0.58    inference(subsumption_resolution,[],[f320,f53])).
% 1.31/0.58  fof(f320,plain,(
% 1.31/0.58    ( ! [X7] : (~r1_tarski(sK3,X7) | sK3 = k9_subset_1(u1_struct_0(sK2),X7,k2_pre_topc(sK2,sK3)) | ~v2_tex_2(X7,sK2) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.31/0.58    inference(resolution,[],[f72,f54])).
% 1.31/0.58  fof(f72,plain,(
% 1.31/0.58    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X3,X1) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.31/0.58    inference(cnf_transformation,[],[f46])).
% 1.31/0.58  fof(f46,plain,(
% 1.31/0.58    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1))) & r1_tarski(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.31/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).
% 1.31/0.58  fof(f45,plain,(
% 1.31/0.58    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1))) & r1_tarski(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.31/0.58    introduced(choice_axiom,[])).
% 1.31/0.58  fof(f44,plain,(
% 1.31/0.58    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.31/0.58    inference(rectify,[],[f43])).
% 1.31/0.58  fof(f43,plain,(
% 1.31/0.58    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.31/0.58    inference(nnf_transformation,[],[f24])).
% 1.31/0.58  fof(f24,plain,(
% 1.31/0.58    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.31/0.58    inference(flattening,[],[f23])).
% 1.31/0.58  fof(f23,plain,(
% 1.31/0.58    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.31/0.58    inference(ennf_transformation,[],[f15])).
% 1.31/0.58  fof(f15,axiom,(
% 1.31/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 1.31/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).
% 1.31/0.58  fof(f444,plain,(
% 1.31/0.58    r1_tarski(sK4(sK3,sK2),u1_struct_0(sK2))),
% 1.31/0.58    inference(trivial_inequality_removal,[],[f443])).
% 1.31/0.58  fof(f443,plain,(
% 1.31/0.58    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK4(sK3,sK2),u1_struct_0(sK2))),
% 1.31/0.58    inference(superposition,[],[f85,f439])).
% 1.31/0.58  % SZS output end Proof for theBenchmark
% 1.31/0.58  % (6438)------------------------------
% 1.31/0.58  % (6438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.58  % (6438)Termination reason: Refutation
% 1.31/0.58  
% 1.31/0.58  % (6438)Memory used [KB]: 11129
% 1.31/0.58  % (6438)Time elapsed: 0.145 s
% 1.31/0.58  % (6438)------------------------------
% 1.31/0.58  % (6438)------------------------------
% 1.31/0.58  % (6431)Success in time 0.209 s
%------------------------------------------------------------------------------
