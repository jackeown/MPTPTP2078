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
% DateTime   : Thu Dec  3 13:21:51 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 415 expanded)
%              Number of leaves         :   18 ( 129 expanded)
%              Depth                    :   22
%              Number of atoms          :  411 (2452 expanded)
%              Number of equality atoms :   72 ( 151 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f524,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f309,f523])).

fof(f523,plain,(
    ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f521,f45])).

fof(f45,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ v3_tex_2(sK3,sK2)
    & v2_tex_2(sK3,sK2)
    & v1_tops_1(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f25,f24])).

fof(f24,plain,
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

fof(f25,plain,
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

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v2_tex_2(X1,X0)
                & v1_tops_1(X1,X0) )
             => v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f521,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f502,f90])).

fof(f90,plain,(
    ~ sP0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f88,f46])).

fof(f46,plain,(
    ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,
    ( ~ sP0(sK3,sK2)
    | v3_tex_2(sK3,sK2) ),
    inference(resolution,[],[f87,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v3_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f87,plain,(
    sP1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f84,f42])).

fof(f42,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f84,plain,
    ( sP1(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f58,f43])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f16,f22,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f502,plain,
    ( sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ spl6_8 ),
    inference(trivial_inequality_removal,[],[f498])).

fof(f498,plain,
    ( sK3 != sK3
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ spl6_8 ),
    inference(superposition,[],[f57,f421])).

fof(f421,plain,
    ( sK3 = sK4(sK3,sK2)
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f195,f403])).

fof(f403,plain,
    ( sK3 = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2))
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f402,f104])).

fof(f104,plain,(
    r1_tarski(sK3,sK4(sK3,sK2)) ),
    inference(trivial_inequality_removal,[],[f103])).

fof(f103,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK3,sK4(sK3,sK2)) ),
    inference(superposition,[],[f68,f102])).

fof(f102,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f100,f90])).

fof(f100,plain,
    ( sP0(sK3,sK2)
    | k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2)) ),
    inference(resolution,[],[f95,f45])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X0,X1)
      | sP0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,sK4(X0,X1)) ) ),
    inference(resolution,[],[f56,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,sK4(X0,X1))
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f402,plain,
    ( sK3 = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2))
    | ~ r1_tarski(sK3,sK4(sK3,sK2))
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f398,f303])).

fof(f303,plain,
    ( v2_tex_2(sK4(sK3,sK2),sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl6_8
  <=> v2_tex_2(sK4(sK3,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f398,plain,
    ( ~ v2_tex_2(sK4(sK3,sK2),sK2)
    | sK3 = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2))
    | ~ r1_tarski(sK3,sK4(sK3,sK2)) ),
    inference(resolution,[],[f223,f194])).

fof(f194,plain,(
    r1_tarski(sK4(sK3,sK2),u1_struct_0(sK2)) ),
    inference(trivial_inequality_removal,[],[f193])).

fof(f193,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK4(sK3,sK2),u1_struct_0(sK2)) ),
    inference(superposition,[],[f68,f191])).

fof(f191,plain,(
    k1_xboole_0 = k4_xboole_0(sK4(sK3,sK2),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f189,f90])).

fof(f189,plain,
    ( sP0(sK3,sK2)
    | k1_xboole_0 = k4_xboole_0(sK4(sK3,sK2),u1_struct_0(sK2)) ),
    inference(resolution,[],[f99,f45])).

fof(f99,plain,(
    ! [X2,X3] :
      ( ~ v2_tex_2(X2,X3)
      | sP0(X2,X3)
      | k1_xboole_0 = k4_xboole_0(sK4(X2,X3),u1_struct_0(X3)) ) ),
    inference(resolution,[],[f97,f69])).

fof(f97,plain,(
    ! [X2,X3] :
      ( r1_tarski(sK4(X2,X3),u1_struct_0(X3))
      | ~ v2_tex_2(X2,X3)
      | sP0(X2,X3) ) ),
    inference(resolution,[],[f54,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f223,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ v2_tex_2(X0,sK2)
      | sK3 = k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2))
      | ~ r1_tarski(sK3,X0) ) ),
    inference(resolution,[],[f209,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f209,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(sK3,X5)
      | ~ v2_tex_2(X5,sK2)
      | sK3 = k9_subset_1(u1_struct_0(sK2),X5,u1_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f208,f118])).

fof(f118,plain,(
    u1_struct_0(sK2) = k2_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f117,f42])).

fof(f117,plain,
    ( u1_struct_0(sK2) = k2_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f113,f44])).

fof(f44,plain,(
    v1_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f113,plain,
    ( ~ v1_tops_1(sK3,sK2)
    | u1_struct_0(sK2) = k2_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f59,f43])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f208,plain,(
    ! [X5] :
      ( ~ r1_tarski(sK3,X5)
      | sK3 = k9_subset_1(u1_struct_0(sK2),X5,k2_pre_topc(sK2,sK3))
      | ~ v2_tex_2(X5,sK2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f207,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f207,plain,(
    ! [X5] :
      ( ~ r1_tarski(sK3,X5)
      | sK3 = k9_subset_1(u1_struct_0(sK2),X5,k2_pre_topc(sK2,sK3))
      | ~ v2_tex_2(X5,sK2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f206,f41])).

fof(f41,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f206,plain,(
    ! [X5] :
      ( ~ r1_tarski(sK3,X5)
      | sK3 = k9_subset_1(u1_struct_0(sK2),X5,k2_pre_topc(sK2,sK3))
      | ~ v2_tex_2(X5,sK2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f202,f42])).

fof(f202,plain,(
    ! [X5] :
      ( ~ r1_tarski(sK3,X5)
      | sK3 = k9_subset_1(u1_struct_0(sK2),X5,k2_pre_topc(sK2,sK3))
      | ~ v2_tex_2(X5,sK2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f61,f43])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X3,X1)
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1)))
        & r1_tarski(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f195,plain,(
    sK4(sK3,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f192,f48])).

fof(f48,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f192,plain,(
    k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2)) = k4_xboole_0(sK4(sK3,sK2),k1_xboole_0) ),
    inference(superposition,[],[f106,f191])).

fof(f106,plain,(
    ! [X2,X1] : k9_subset_1(X1,X2,X1) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(resolution,[],[f71,f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f49,f47])).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f70,f65])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X0
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f309,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | spl6_8 ),
    inference(subsumption_resolution,[],[f307,f45])).

fof(f307,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f306,f90])).

fof(f306,plain,
    ( sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | spl6_8 ),
    inference(resolution,[],[f304,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK4(X0,X1),X1)
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f304,plain,
    ( ~ v2_tex_2(sK4(sK3,sK2),sK2)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 11:48:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.52  % (31775)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (31767)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (31774)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (31755)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (31759)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (31758)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.35/0.55  % (31763)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.35/0.55  % (31757)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.35/0.55  % (31756)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.35/0.55  % (31753)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.35/0.55  % (31773)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.35/0.55  % (31763)Refutation not found, incomplete strategy% (31763)------------------------------
% 1.35/0.55  % (31763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (31780)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.35/0.55  % (31763)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (31763)Memory used [KB]: 10746
% 1.35/0.55  % (31763)Time elapsed: 0.127 s
% 1.35/0.55  % (31763)------------------------------
% 1.35/0.55  % (31763)------------------------------
% 1.35/0.55  % (31754)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.35/0.56  % (31768)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.35/0.56  % (31784)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.35/0.56  % (31772)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.35/0.56  % (31772)Refutation not found, incomplete strategy% (31772)------------------------------
% 1.35/0.56  % (31772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (31772)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (31772)Memory used [KB]: 1791
% 1.35/0.56  % (31772)Time elapsed: 0.140 s
% 1.35/0.56  % (31772)------------------------------
% 1.35/0.56  % (31772)------------------------------
% 1.35/0.56  % (31786)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.35/0.56  % (31760)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.35/0.56  % (31786)Refutation not found, incomplete strategy% (31786)------------------------------
% 1.35/0.56  % (31786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (31786)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (31786)Memory used [KB]: 1791
% 1.35/0.56  % (31786)Time elapsed: 0.149 s
% 1.35/0.56  % (31786)------------------------------
% 1.35/0.56  % (31786)------------------------------
% 1.35/0.56  % (31765)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.35/0.56  % (31771)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.35/0.56  % (31759)Refutation found. Thanks to Tanya!
% 1.35/0.56  % SZS status Theorem for theBenchmark
% 1.35/0.56  % SZS output start Proof for theBenchmark
% 1.35/0.56  fof(f524,plain,(
% 1.35/0.56    $false),
% 1.35/0.56    inference(avatar_sat_refutation,[],[f309,f523])).
% 1.35/0.56  fof(f523,plain,(
% 1.35/0.56    ~spl6_8),
% 1.35/0.56    inference(avatar_contradiction_clause,[],[f522])).
% 1.35/0.56  fof(f522,plain,(
% 1.35/0.56    $false | ~spl6_8),
% 1.35/0.56    inference(subsumption_resolution,[],[f521,f45])).
% 1.35/0.56  fof(f45,plain,(
% 1.35/0.56    v2_tex_2(sK3,sK2)),
% 1.35/0.56    inference(cnf_transformation,[],[f26])).
% 1.35/0.56  fof(f26,plain,(
% 1.35/0.56    (~v3_tex_2(sK3,sK2) & v2_tex_2(sK3,sK2) & v1_tops_1(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.35/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f25,f24])).
% 1.35/0.56  fof(f24,plain,(
% 1.35/0.56    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v3_tex_2(X1,sK2) & v2_tex_2(X1,sK2) & v1_tops_1(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.35/0.56    introduced(choice_axiom,[])).
% 1.35/0.56  fof(f25,plain,(
% 1.35/0.56    ? [X1] : (~v3_tex_2(X1,sK2) & v2_tex_2(X1,sK2) & v1_tops_1(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => (~v3_tex_2(sK3,sK2) & v2_tex_2(sK3,sK2) & v1_tops_1(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.35/0.56    introduced(choice_axiom,[])).
% 1.35/0.56  fof(f14,plain,(
% 1.35/0.56    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.35/0.56    inference(flattening,[],[f13])).
% 1.35/0.56  fof(f13,plain,(
% 1.35/0.56    ? [X0] : (? [X1] : ((~v3_tex_2(X1,X0) & (v2_tex_2(X1,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f12])).
% 1.35/0.56  fof(f12,negated_conjecture,(
% 1.35/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 1.35/0.56    inference(negated_conjecture,[],[f11])).
% 1.35/0.56  fof(f11,conjecture,(
% 1.35/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
% 1.35/0.56  fof(f521,plain,(
% 1.35/0.56    ~v2_tex_2(sK3,sK2) | ~spl6_8),
% 1.35/0.56    inference(subsumption_resolution,[],[f502,f90])).
% 1.35/0.56  fof(f90,plain,(
% 1.35/0.56    ~sP0(sK3,sK2)),
% 1.35/0.56    inference(subsumption_resolution,[],[f88,f46])).
% 1.35/0.56  fof(f46,plain,(
% 1.35/0.56    ~v3_tex_2(sK3,sK2)),
% 1.35/0.56    inference(cnf_transformation,[],[f26])).
% 1.35/0.56  fof(f88,plain,(
% 1.35/0.56    ~sP0(sK3,sK2) | v3_tex_2(sK3,sK2)),
% 1.35/0.56    inference(resolution,[],[f87,f51])).
% 1.35/0.56  fof(f51,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v3_tex_2(X1,X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f27])).
% 1.35/0.56  fof(f27,plain,(
% 1.35/0.56    ! [X0,X1] : (((v3_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v3_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 1.35/0.56    inference(nnf_transformation,[],[f22])).
% 1.35/0.56  fof(f22,plain,(
% 1.35/0.56    ! [X0,X1] : ((v3_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 1.35/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.35/0.56  fof(f87,plain,(
% 1.35/0.56    sP1(sK2,sK3)),
% 1.35/0.56    inference(subsumption_resolution,[],[f84,f42])).
% 1.35/0.56  fof(f42,plain,(
% 1.35/0.56    l1_pre_topc(sK2)),
% 1.35/0.56    inference(cnf_transformation,[],[f26])).
% 1.35/0.56  fof(f84,plain,(
% 1.35/0.56    sP1(sK2,sK3) | ~l1_pre_topc(sK2)),
% 1.35/0.56    inference(resolution,[],[f58,f43])).
% 1.35/0.56  fof(f43,plain,(
% 1.35/0.56    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.35/0.56    inference(cnf_transformation,[],[f26])).
% 1.35/0.56  fof(f58,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f23])).
% 1.35/0.56  fof(f23,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.35/0.56    inference(definition_folding,[],[f16,f22,f21])).
% 1.35/0.56  fof(f21,plain,(
% 1.35/0.56    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)))),
% 1.35/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.35/0.56  fof(f16,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.35/0.56    inference(flattening,[],[f15])).
% 1.35/0.56  fof(f15,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.35/0.56    inference(ennf_transformation,[],[f9])).
% 1.35/0.56  fof(f9,axiom,(
% 1.35/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 1.35/0.56  fof(f502,plain,(
% 1.35/0.56    sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | ~spl6_8),
% 1.35/0.56    inference(trivial_inequality_removal,[],[f498])).
% 1.35/0.56  fof(f498,plain,(
% 1.35/0.56    sK3 != sK3 | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | ~spl6_8),
% 1.35/0.56    inference(superposition,[],[f57,f421])).
% 1.35/0.56  fof(f421,plain,(
% 1.35/0.56    sK3 = sK4(sK3,sK2) | ~spl6_8),
% 1.35/0.56    inference(backward_demodulation,[],[f195,f403])).
% 1.35/0.56  fof(f403,plain,(
% 1.35/0.56    sK3 = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2)) | ~spl6_8),
% 1.35/0.56    inference(subsumption_resolution,[],[f402,f104])).
% 1.35/0.56  fof(f104,plain,(
% 1.35/0.56    r1_tarski(sK3,sK4(sK3,sK2))),
% 1.35/0.56    inference(trivial_inequality_removal,[],[f103])).
% 1.35/0.56  fof(f103,plain,(
% 1.35/0.56    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK3,sK4(sK3,sK2))),
% 1.35/0.56    inference(superposition,[],[f68,f102])).
% 1.35/0.56  fof(f102,plain,(
% 1.35/0.56    k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2))),
% 1.35/0.56    inference(subsumption_resolution,[],[f100,f90])).
% 1.35/0.56  fof(f100,plain,(
% 1.35/0.56    sP0(sK3,sK2) | k1_xboole_0 = k4_xboole_0(sK3,sK4(sK3,sK2))),
% 1.35/0.56    inference(resolution,[],[f95,f45])).
% 1.35/0.56  fof(f95,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~v2_tex_2(X0,X1) | sP0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,sK4(X0,X1))) )),
% 1.35/0.56    inference(resolution,[],[f56,f69])).
% 1.35/0.56  fof(f69,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.35/0.56    inference(cnf_transformation,[],[f39])).
% 1.35/0.56  fof(f39,plain,(
% 1.35/0.56    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.35/0.56    inference(nnf_transformation,[],[f1])).
% 1.35/0.56  fof(f1,axiom,(
% 1.35/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.35/0.56  fof(f56,plain,(
% 1.35/0.56    ( ! [X0,X1] : (r1_tarski(X0,sK4(X0,X1)) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f32])).
% 1.35/0.56  fof(f32,plain,(
% 1.35/0.56    ! [X0,X1] : ((sP0(X0,X1) | (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 1.35/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 1.35/0.56  fof(f31,plain,(
% 1.35/0.56    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.35/0.56    introduced(choice_axiom,[])).
% 1.35/0.56  fof(f30,plain,(
% 1.35/0.56    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 1.35/0.56    inference(rectify,[],[f29])).
% 1.35/0.56  fof(f29,plain,(
% 1.35/0.56    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 1.35/0.56    inference(flattening,[],[f28])).
% 1.35/0.56  fof(f28,plain,(
% 1.35/0.56    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 1.35/0.56    inference(nnf_transformation,[],[f21])).
% 1.35/0.56  fof(f68,plain,(
% 1.35/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f39])).
% 1.35/0.56  fof(f402,plain,(
% 1.35/0.56    sK3 = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2)) | ~r1_tarski(sK3,sK4(sK3,sK2)) | ~spl6_8),
% 1.35/0.56    inference(subsumption_resolution,[],[f398,f303])).
% 1.35/0.56  fof(f303,plain,(
% 1.35/0.56    v2_tex_2(sK4(sK3,sK2),sK2) | ~spl6_8),
% 1.35/0.56    inference(avatar_component_clause,[],[f302])).
% 1.35/0.56  fof(f302,plain,(
% 1.35/0.56    spl6_8 <=> v2_tex_2(sK4(sK3,sK2),sK2)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.35/0.56  fof(f398,plain,(
% 1.35/0.56    ~v2_tex_2(sK4(sK3,sK2),sK2) | sK3 = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2)) | ~r1_tarski(sK3,sK4(sK3,sK2))),
% 1.35/0.56    inference(resolution,[],[f223,f194])).
% 1.35/0.56  fof(f194,plain,(
% 1.35/0.56    r1_tarski(sK4(sK3,sK2),u1_struct_0(sK2))),
% 1.35/0.56    inference(trivial_inequality_removal,[],[f193])).
% 1.35/0.56  fof(f193,plain,(
% 1.35/0.56    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK4(sK3,sK2),u1_struct_0(sK2))),
% 1.35/0.56    inference(superposition,[],[f68,f191])).
% 1.35/0.56  fof(f191,plain,(
% 1.35/0.56    k1_xboole_0 = k4_xboole_0(sK4(sK3,sK2),u1_struct_0(sK2))),
% 1.35/0.56    inference(subsumption_resolution,[],[f189,f90])).
% 1.35/0.56  fof(f189,plain,(
% 1.35/0.56    sP0(sK3,sK2) | k1_xboole_0 = k4_xboole_0(sK4(sK3,sK2),u1_struct_0(sK2))),
% 1.35/0.56    inference(resolution,[],[f99,f45])).
% 1.35/0.56  fof(f99,plain,(
% 1.35/0.56    ( ! [X2,X3] : (~v2_tex_2(X2,X3) | sP0(X2,X3) | k1_xboole_0 = k4_xboole_0(sK4(X2,X3),u1_struct_0(X3))) )),
% 1.35/0.56    inference(resolution,[],[f97,f69])).
% 1.35/0.56  fof(f97,plain,(
% 1.35/0.56    ( ! [X2,X3] : (r1_tarski(sK4(X2,X3),u1_struct_0(X3)) | ~v2_tex_2(X2,X3) | sP0(X2,X3)) )),
% 1.35/0.56    inference(resolution,[],[f54,f66])).
% 1.35/0.56  fof(f66,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f38])).
% 1.35/0.56  fof(f38,plain,(
% 1.35/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.35/0.56    inference(nnf_transformation,[],[f7])).
% 1.35/0.56  fof(f7,axiom,(
% 1.35/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.35/0.56  fof(f54,plain,(
% 1.35/0.56    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f32])).
% 1.35/0.56  fof(f223,plain,(
% 1.35/0.56    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~v2_tex_2(X0,sK2) | sK3 = k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)) | ~r1_tarski(sK3,X0)) )),
% 1.35/0.56    inference(resolution,[],[f209,f67])).
% 1.35/0.56  fof(f67,plain,(
% 1.35/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f38])).
% 1.35/0.56  fof(f209,plain,(
% 1.35/0.56    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(sK3,X5) | ~v2_tex_2(X5,sK2) | sK3 = k9_subset_1(u1_struct_0(sK2),X5,u1_struct_0(sK2))) )),
% 1.35/0.56    inference(forward_demodulation,[],[f208,f118])).
% 1.35/0.56  fof(f118,plain,(
% 1.35/0.56    u1_struct_0(sK2) = k2_pre_topc(sK2,sK3)),
% 1.35/0.56    inference(subsumption_resolution,[],[f117,f42])).
% 1.35/0.56  fof(f117,plain,(
% 1.35/0.56    u1_struct_0(sK2) = k2_pre_topc(sK2,sK3) | ~l1_pre_topc(sK2)),
% 1.35/0.56    inference(subsumption_resolution,[],[f113,f44])).
% 1.35/0.56  fof(f44,plain,(
% 1.35/0.56    v1_tops_1(sK3,sK2)),
% 1.35/0.56    inference(cnf_transformation,[],[f26])).
% 1.35/0.56  fof(f113,plain,(
% 1.35/0.56    ~v1_tops_1(sK3,sK2) | u1_struct_0(sK2) = k2_pre_topc(sK2,sK3) | ~l1_pre_topc(sK2)),
% 1.35/0.56    inference(resolution,[],[f59,f43])).
% 1.35/0.56  fof(f59,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f33])).
% 1.35/0.56  fof(f33,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.35/0.56    inference(nnf_transformation,[],[f17])).
% 1.35/0.56  fof(f17,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.35/0.56    inference(ennf_transformation,[],[f8])).
% 1.35/0.56  fof(f8,axiom,(
% 1.35/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 1.35/0.56  fof(f208,plain,(
% 1.35/0.56    ( ! [X5] : (~r1_tarski(sK3,X5) | sK3 = k9_subset_1(u1_struct_0(sK2),X5,k2_pre_topc(sK2,sK3)) | ~v2_tex_2(X5,sK2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.35/0.56    inference(subsumption_resolution,[],[f207,f40])).
% 1.35/0.56  fof(f40,plain,(
% 1.35/0.56    ~v2_struct_0(sK2)),
% 1.35/0.56    inference(cnf_transformation,[],[f26])).
% 1.35/0.56  fof(f207,plain,(
% 1.35/0.56    ( ! [X5] : (~r1_tarski(sK3,X5) | sK3 = k9_subset_1(u1_struct_0(sK2),X5,k2_pre_topc(sK2,sK3)) | ~v2_tex_2(X5,sK2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)) )),
% 1.35/0.56    inference(subsumption_resolution,[],[f206,f41])).
% 1.35/0.56  fof(f41,plain,(
% 1.35/0.56    v2_pre_topc(sK2)),
% 1.35/0.56    inference(cnf_transformation,[],[f26])).
% 1.35/0.56  fof(f206,plain,(
% 1.35/0.56    ( ! [X5] : (~r1_tarski(sK3,X5) | sK3 = k9_subset_1(u1_struct_0(sK2),X5,k2_pre_topc(sK2,sK3)) | ~v2_tex_2(X5,sK2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.35/0.56    inference(subsumption_resolution,[],[f202,f42])).
% 1.35/0.56  fof(f202,plain,(
% 1.35/0.56    ( ! [X5] : (~r1_tarski(sK3,X5) | sK3 = k9_subset_1(u1_struct_0(sK2),X5,k2_pre_topc(sK2,sK3)) | ~v2_tex_2(X5,sK2) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.35/0.56    inference(resolution,[],[f61,f43])).
% 1.35/0.56  fof(f61,plain,(
% 1.35/0.56    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X3,X1) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f37])).
% 1.35/0.56  fof(f37,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1))) & r1_tarski(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 1.35/0.56  fof(f36,plain,(
% 1.35/0.56    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1))) & r1_tarski(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.35/0.56    introduced(choice_axiom,[])).
% 1.35/0.56  fof(f35,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.56    inference(rectify,[],[f34])).
% 1.35/0.56  fof(f34,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.56    inference(nnf_transformation,[],[f19])).
% 1.35/0.56  fof(f19,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.56    inference(flattening,[],[f18])).
% 1.35/0.56  fof(f18,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f10])).
% 1.35/0.56  fof(f10,axiom,(
% 1.35/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).
% 1.35/0.56  fof(f195,plain,(
% 1.35/0.56    sK4(sK3,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2))),
% 1.35/0.56    inference(forward_demodulation,[],[f192,f48])).
% 1.35/0.56  fof(f48,plain,(
% 1.35/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.35/0.56    inference(cnf_transformation,[],[f2])).
% 1.35/0.56  fof(f2,axiom,(
% 1.35/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.35/0.56  fof(f192,plain,(
% 1.35/0.56    k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2)) = k4_xboole_0(sK4(sK3,sK2),k1_xboole_0)),
% 1.35/0.56    inference(superposition,[],[f106,f191])).
% 1.35/0.56  fof(f106,plain,(
% 1.35/0.56    ( ! [X2,X1] : (k9_subset_1(X1,X2,X1) = k4_xboole_0(X2,k4_xboole_0(X2,X1))) )),
% 1.35/0.56    inference(resolution,[],[f71,f72])).
% 1.35/0.56  fof(f72,plain,(
% 1.35/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.35/0.56    inference(forward_demodulation,[],[f49,f47])).
% 1.35/0.56  fof(f47,plain,(
% 1.35/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.35/0.56    inference(cnf_transformation,[],[f4])).
% 1.35/0.56  fof(f4,axiom,(
% 1.35/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.35/0.56  fof(f49,plain,(
% 1.35/0.56    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.35/0.56    inference(cnf_transformation,[],[f5])).
% 1.35/0.56  fof(f5,axiom,(
% 1.35/0.56    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.35/0.56  fof(f71,plain,(
% 1.35/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 1.35/0.56    inference(definition_unfolding,[],[f70,f65])).
% 1.35/0.56  fof(f65,plain,(
% 1.35/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f3])).
% 1.35/0.56  fof(f3,axiom,(
% 1.35/0.56    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.35/0.56  fof(f70,plain,(
% 1.35/0.56    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.35/0.56    inference(cnf_transformation,[],[f20])).
% 1.35/0.56  fof(f20,plain,(
% 1.35/0.56    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f6])).
% 1.35/0.56  fof(f6,axiom,(
% 1.35/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.35/0.56  fof(f57,plain,(
% 1.35/0.56    ( ! [X0,X1] : (sK4(X0,X1) != X0 | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f32])).
% 1.35/0.56  fof(f309,plain,(
% 1.35/0.56    spl6_8),
% 1.35/0.56    inference(avatar_contradiction_clause,[],[f308])).
% 1.35/0.56  fof(f308,plain,(
% 1.35/0.56    $false | spl6_8),
% 1.35/0.56    inference(subsumption_resolution,[],[f307,f45])).
% 1.35/0.56  fof(f307,plain,(
% 1.35/0.56    ~v2_tex_2(sK3,sK2) | spl6_8),
% 1.35/0.56    inference(subsumption_resolution,[],[f306,f90])).
% 1.35/0.56  fof(f306,plain,(
% 1.35/0.56    sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | spl6_8),
% 1.35/0.56    inference(resolution,[],[f304,f55])).
% 1.35/0.56  fof(f55,plain,(
% 1.35/0.56    ( ! [X0,X1] : (v2_tex_2(sK4(X0,X1),X1) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f32])).
% 1.35/0.56  fof(f304,plain,(
% 1.35/0.56    ~v2_tex_2(sK4(sK3,sK2),sK2) | spl6_8),
% 1.35/0.56    inference(avatar_component_clause,[],[f302])).
% 1.35/0.56  % SZS output end Proof for theBenchmark
% 1.35/0.56  % (31759)------------------------------
% 1.35/0.56  % (31759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (31759)Termination reason: Refutation
% 1.35/0.56  
% 1.35/0.56  % (31759)Memory used [KB]: 11129
% 1.35/0.56  % (31759)Time elapsed: 0.087 s
% 1.35/0.56  % (31759)------------------------------
% 1.35/0.56  % (31759)------------------------------
% 1.35/0.56  % (31766)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.35/0.57  % (31751)Success in time 0.192 s
%------------------------------------------------------------------------------
