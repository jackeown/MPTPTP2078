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
% DateTime   : Thu Dec  3 13:21:15 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 219 expanded)
%              Number of leaves         :   18 (  66 expanded)
%              Depth                    :   16
%              Number of atoms          :  250 ( 911 expanded)
%              Number of equality atoms :   42 (  75 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(subsumption_resolution,[],[f195,f112])).

fof(f112,plain,(
    ~ sP0(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f111,f76])).

fof(f76,plain,(
    ~ v2_tex_2(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f48,f73])).

fof(f73,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f52,f46])).

fof(f46,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & v1_xboole_0(X1) )
   => ( ~ v2_tex_2(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f48,plain,(
    ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f111,plain,
    ( ~ sP0(k1_xboole_0,sK2)
    | v2_tex_2(k1_xboole_0,sK2) ),
    inference(resolution,[],[f109,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f109,plain,(
    sP1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f108,f50])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f108,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | sP1(sK2,X0) ) ),
    inference(forward_demodulation,[],[f107,f81])).

fof(f81,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f53,f72])).

fof(f72,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f54,f45])).

fof(f45,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f107,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0) ) ),
    inference(resolution,[],[f63,f45])).

% (5802)Termination reason: Refutation not found, incomplete strategy

% (5802)Memory used [KB]: 10746
% (5802)Time elapsed: 0.146 s
% (5802)------------------------------
% (5802)------------------------------
fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f26,f33,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
              & v4_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

fof(f195,plain,(
    sP0(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f192,f113])).

fof(f113,plain,(
    k1_xboole_0 = sK4(k1_xboole_0,sK2) ),
    inference(resolution,[],[f112,f82])).

fof(f82,plain,(
    ! [X0] :
      ( sP0(k1_xboole_0,X0)
      | k1_xboole_0 = sK4(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f61,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK4(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
              | ~ v4_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(sK4(X0,X1),X0)
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ( k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4
              & v4_pre_topc(sK5(X0,X1,X4),X1)
              & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f42,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
              | ~ v4_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
            | ~ v4_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(sK4(X0,X1),X0)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
          & v4_pre_topc(X5,X1)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4
        & v4_pre_topc(sK5(X0,X1,X4),X1)
        & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
                | ~ v4_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & r1_tarski(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
                & v4_pre_topc(X5,X1)
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                | ~ v4_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                & v4_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f192,plain,
    ( k1_xboole_0 != sK4(k1_xboole_0,sK2)
    | sP0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f191,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f64,f66])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f191,plain,(
    ! [X0] :
      ( sK4(X0,sK2) != k3_xboole_0(X0,k2_struct_0(sK2))
      | sP0(X0,sK2) ) ),
    inference(forward_demodulation,[],[f190,f122])).

fof(f122,plain,(
    ! [X2,X3] : k3_xboole_0(X3,X2) = k9_subset_1(X2,X3,X2) ),
    inference(resolution,[],[f69,f71])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f51,f49])).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f190,plain,(
    ! [X0] :
      ( sP0(X0,sK2)
      | sK4(X0,sK2) != k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f189,f44])).

fof(f44,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f189,plain,(
    ! [X0] :
      ( sP0(X0,sK2)
      | sK4(X0,sK2) != k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2))
      | ~ v2_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f188,f45])).

fof(f188,plain,(
    ! [X0] :
      ( sP0(X0,sK2)
      | sK4(X0,sK2) != k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f187,f71])).

fof(f187,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))
      | sP0(X0,sK2)
      | sK4(X0,sK2) != k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(superposition,[],[f172,f81])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,k2_struct_0(X0)) != sK4(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f62,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

% (5797)Refutation not found, incomplete strategy% (5797)------------------------------
% (5797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5797)Termination reason: Refutation not found, incomplete strategy

% (5797)Memory used [KB]: 6268
% (5797)Time elapsed: 0.157 s
% (5797)------------------------------
% (5797)------------------------------
fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ v4_pre_topc(X3,X1)
      | k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
      | sP0(X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:39:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.27/0.54  % (5795)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.54  % (5815)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.55  % (5807)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.27/0.55  % (5802)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.56  % (5794)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.45/0.56  % (5799)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.45/0.56  % (5803)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.57  % (5792)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.45/0.57  % (5810)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.57  % (5807)Refutation not found, incomplete strategy% (5807)------------------------------
% 1.45/0.57  % (5807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (5807)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  % (5796)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.45/0.57  
% 1.45/0.57  % (5807)Memory used [KB]: 6268
% 1.45/0.57  % (5807)Time elapsed: 0.080 s
% 1.45/0.57  % (5807)------------------------------
% 1.45/0.57  % (5807)------------------------------
% 1.45/0.57  % (5802)Refutation not found, incomplete strategy% (5802)------------------------------
% 1.45/0.57  % (5802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (5799)Refutation found. Thanks to Tanya!
% 1.45/0.57  % SZS status Theorem for theBenchmark
% 1.45/0.58  % (5797)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.45/0.58  % SZS output start Proof for theBenchmark
% 1.45/0.58  fof(f196,plain,(
% 1.45/0.58    $false),
% 1.45/0.58    inference(subsumption_resolution,[],[f195,f112])).
% 1.45/0.58  fof(f112,plain,(
% 1.45/0.58    ~sP0(k1_xboole_0,sK2)),
% 1.45/0.58    inference(subsumption_resolution,[],[f111,f76])).
% 1.45/0.58  fof(f76,plain,(
% 1.45/0.58    ~v2_tex_2(k1_xboole_0,sK2)),
% 1.45/0.58    inference(backward_demodulation,[],[f48,f73])).
% 1.45/0.58  fof(f73,plain,(
% 1.45/0.58    k1_xboole_0 = sK3),
% 1.45/0.58    inference(resolution,[],[f52,f46])).
% 1.45/0.58  fof(f46,plain,(
% 1.45/0.58    v1_xboole_0(sK3)),
% 1.45/0.58    inference(cnf_transformation,[],[f37])).
% 1.45/0.58  fof(f37,plain,(
% 1.45/0.58    (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 1.45/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f36,f35])).
% 1.45/0.58  fof(f35,plain,(
% 1.45/0.58    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f36,plain,(
% 1.45/0.58    ? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) => (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f21,plain,(
% 1.45/0.58    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.45/0.58    inference(flattening,[],[f20])).
% 1.45/0.58  fof(f20,plain,(
% 1.45/0.58    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.45/0.58    inference(ennf_transformation,[],[f18])).
% 1.45/0.58  fof(f18,plain,(
% 1.45/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.45/0.58    inference(pure_predicate_removal,[],[f17])).
% 1.45/0.58  fof(f17,negated_conjecture,(
% 1.45/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.45/0.58    inference(negated_conjecture,[],[f16])).
% 1.45/0.58  fof(f16,conjecture,(
% 1.45/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 1.45/0.58  fof(f52,plain,(
% 1.45/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.45/0.58    inference(cnf_transformation,[],[f22])).
% 1.45/0.58  fof(f22,plain,(
% 1.45/0.58    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.45/0.58    inference(ennf_transformation,[],[f1])).
% 1.45/0.58  fof(f1,axiom,(
% 1.45/0.58    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.45/0.58  fof(f48,plain,(
% 1.45/0.58    ~v2_tex_2(sK3,sK2)),
% 1.45/0.58    inference(cnf_transformation,[],[f37])).
% 1.45/0.58  fof(f111,plain,(
% 1.45/0.58    ~sP0(k1_xboole_0,sK2) | v2_tex_2(k1_xboole_0,sK2)),
% 1.45/0.58    inference(resolution,[],[f109,f56])).
% 1.45/0.58  fof(f56,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v2_tex_2(X1,X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f38])).
% 1.45/0.58  fof(f38,plain,(
% 1.45/0.58    ! [X0,X1] : (((v2_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 1.45/0.58    inference(nnf_transformation,[],[f33])).
% 1.45/0.58  fof(f33,plain,(
% 1.45/0.58    ! [X0,X1] : ((v2_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 1.45/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.45/0.58  fof(f109,plain,(
% 1.45/0.58    sP1(sK2,k1_xboole_0)),
% 1.45/0.58    inference(resolution,[],[f108,f50])).
% 1.45/0.58  fof(f50,plain,(
% 1.45/0.58    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.45/0.58    inference(cnf_transformation,[],[f9])).
% 1.45/0.58  fof(f9,axiom,(
% 1.45/0.58    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.45/0.58  fof(f108,plain,(
% 1.45/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | sP1(sK2,X0)) )),
% 1.45/0.58    inference(forward_demodulation,[],[f107,f81])).
% 1.45/0.58  fof(f81,plain,(
% 1.45/0.58    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 1.45/0.58    inference(resolution,[],[f53,f72])).
% 1.45/0.58  fof(f72,plain,(
% 1.45/0.58    l1_struct_0(sK2)),
% 1.45/0.58    inference(resolution,[],[f54,f45])).
% 1.45/0.58  fof(f45,plain,(
% 1.45/0.58    l1_pre_topc(sK2)),
% 1.45/0.58    inference(cnf_transformation,[],[f37])).
% 1.45/0.58  fof(f54,plain,(
% 1.45/0.58    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f24])).
% 1.45/0.58  fof(f24,plain,(
% 1.45/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.45/0.58    inference(ennf_transformation,[],[f13])).
% 1.45/0.58  fof(f13,axiom,(
% 1.45/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.45/0.58  fof(f53,plain,(
% 1.45/0.58    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f23])).
% 1.45/0.58  fof(f23,plain,(
% 1.45/0.58    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.45/0.58    inference(ennf_transformation,[],[f12])).
% 1.45/0.58  fof(f12,axiom,(
% 1.45/0.58    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.45/0.58  fof(f107,plain,(
% 1.45/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0)) )),
% 1.45/0.58    inference(resolution,[],[f63,f45])).
% 1.45/0.58  % (5802)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.58  
% 1.45/0.58  % (5802)Memory used [KB]: 10746
% 1.45/0.58  % (5802)Time elapsed: 0.146 s
% 1.45/0.58  % (5802)------------------------------
% 1.45/0.58  % (5802)------------------------------
% 1.45/0.58  fof(f63,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f34])).
% 1.45/0.58  fof(f34,plain,(
% 1.45/0.58    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.45/0.58    inference(definition_folding,[],[f26,f33,f32])).
% 1.45/0.58  fof(f32,plain,(
% 1.45/0.58    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.45/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.45/0.58  fof(f26,plain,(
% 1.45/0.58    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.45/0.58    inference(flattening,[],[f25])).
% 1.45/0.58  fof(f25,plain,(
% 1.45/0.58    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.45/0.58    inference(ennf_transformation,[],[f15])).
% 1.45/0.58  fof(f15,axiom,(
% 1.45/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).
% 1.45/0.58  fof(f195,plain,(
% 1.45/0.58    sP0(k1_xboole_0,sK2)),
% 1.45/0.58    inference(subsumption_resolution,[],[f192,f113])).
% 1.45/0.58  fof(f113,plain,(
% 1.45/0.58    k1_xboole_0 = sK4(k1_xboole_0,sK2)),
% 1.45/0.58    inference(resolution,[],[f112,f82])).
% 1.45/0.58  fof(f82,plain,(
% 1.45/0.58    ( ! [X0] : (sP0(k1_xboole_0,X0) | k1_xboole_0 = sK4(k1_xboole_0,X0)) )),
% 1.45/0.58    inference(resolution,[],[f61,f64])).
% 1.45/0.58  fof(f64,plain,(
% 1.45/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.45/0.58    inference(cnf_transformation,[],[f27])).
% 1.45/0.58  fof(f27,plain,(
% 1.45/0.58    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.45/0.58    inference(ennf_transformation,[],[f3])).
% 1.45/0.58  fof(f3,axiom,(
% 1.45/0.58    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.45/0.58  fof(f61,plain,(
% 1.45/0.58    ( ! [X0,X1] : (r1_tarski(sK4(X0,X1),X0) | sP0(X0,X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f43])).
% 1.45/0.58  fof(f43,plain,(
% 1.45/0.58    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4 & v4_pre_topc(sK5(X0,X1,X4),X1) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 1.45/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f42,f41])).
% 1.45/0.58  fof(f41,plain,(
% 1.45/0.58    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f42,plain,(
% 1.45/0.58    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v4_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4 & v4_pre_topc(sK5(X0,X1,X4),X1) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f40,plain,(
% 1.45/0.58    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v4_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 1.45/0.58    inference(rectify,[],[f39])).
% 1.45/0.58  fof(f39,plain,(
% 1.45/0.58    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 1.45/0.58    inference(nnf_transformation,[],[f32])).
% 1.45/0.58  fof(f192,plain,(
% 1.45/0.58    k1_xboole_0 != sK4(k1_xboole_0,sK2) | sP0(k1_xboole_0,sK2)),
% 1.45/0.58    inference(superposition,[],[f191,f78])).
% 1.45/0.58  fof(f78,plain,(
% 1.45/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.45/0.58    inference(resolution,[],[f64,f66])).
% 1.45/0.58  fof(f66,plain,(
% 1.45/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f2])).
% 1.45/0.58  fof(f2,axiom,(
% 1.45/0.58    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.45/0.58  fof(f191,plain,(
% 1.45/0.58    ( ! [X0] : (sK4(X0,sK2) != k3_xboole_0(X0,k2_struct_0(sK2)) | sP0(X0,sK2)) )),
% 1.45/0.58    inference(forward_demodulation,[],[f190,f122])).
% 1.45/0.58  fof(f122,plain,(
% 1.45/0.58    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = k9_subset_1(X2,X3,X2)) )),
% 1.45/0.58    inference(resolution,[],[f69,f71])).
% 1.45/0.58  fof(f71,plain,(
% 1.45/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.45/0.58    inference(forward_demodulation,[],[f51,f49])).
% 1.45/0.58  fof(f49,plain,(
% 1.45/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.45/0.58    inference(cnf_transformation,[],[f6])).
% 1.45/0.58  fof(f6,axiom,(
% 1.45/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.45/0.58  fof(f51,plain,(
% 1.45/0.58    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.45/0.58    inference(cnf_transformation,[],[f7])).
% 1.45/0.58  fof(f7,axiom,(
% 1.45/0.58    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.45/0.58  fof(f69,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f30])).
% 1.45/0.58  fof(f30,plain,(
% 1.45/0.58    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.45/0.58    inference(ennf_transformation,[],[f8])).
% 1.45/0.58  fof(f8,axiom,(
% 1.45/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.45/0.58  fof(f190,plain,(
% 1.45/0.58    ( ! [X0] : (sP0(X0,sK2) | sK4(X0,sK2) != k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2))) )),
% 1.45/0.58    inference(subsumption_resolution,[],[f189,f44])).
% 1.45/0.58  fof(f44,plain,(
% 1.45/0.58    v2_pre_topc(sK2)),
% 1.45/0.58    inference(cnf_transformation,[],[f37])).
% 1.45/0.58  fof(f189,plain,(
% 1.45/0.58    ( ! [X0] : (sP0(X0,sK2) | sK4(X0,sK2) != k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)) | ~v2_pre_topc(sK2)) )),
% 1.45/0.58    inference(subsumption_resolution,[],[f188,f45])).
% 1.45/0.58  fof(f188,plain,(
% 1.45/0.58    ( ! [X0] : (sP0(X0,sK2) | sK4(X0,sK2) != k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)) )),
% 1.45/0.58    inference(subsumption_resolution,[],[f187,f71])).
% 1.45/0.58  fof(f187,plain,(
% 1.45/0.58    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) | sP0(X0,sK2) | sK4(X0,sK2) != k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)) )),
% 1.45/0.58    inference(superposition,[],[f172,f81])).
% 1.45/0.58  fof(f172,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | sP0(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,k2_struct_0(X0)) != sK4(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.45/0.58    inference(resolution,[],[f62,f65])).
% 1.45/0.58  fof(f65,plain,(
% 1.45/0.58    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f29])).
% 1.45/0.58  fof(f29,plain,(
% 1.45/0.58    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.45/0.58    inference(flattening,[],[f28])).
% 1.45/0.58  fof(f28,plain,(
% 1.45/0.58    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.45/0.58    inference(ennf_transformation,[],[f14])).
% 1.45/0.58  fof(f14,axiom,(
% 1.45/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).
% 1.45/0.58  % (5797)Refutation not found, incomplete strategy% (5797)------------------------------
% 1.45/0.58  % (5797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (5797)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.58  
% 1.45/0.58  % (5797)Memory used [KB]: 6268
% 1.45/0.58  % (5797)Time elapsed: 0.157 s
% 1.45/0.58  % (5797)------------------------------
% 1.45/0.58  % (5797)------------------------------
% 1.45/0.58  fof(f62,plain,(
% 1.45/0.58    ( ! [X0,X3,X1] : (~v4_pre_topc(X3,X1) | k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | sP0(X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 1.45/0.58    inference(cnf_transformation,[],[f43])).
% 1.45/0.58  % SZS output end Proof for theBenchmark
% 1.45/0.58  % (5799)------------------------------
% 1.45/0.58  % (5799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (5799)Termination reason: Refutation
% 1.45/0.58  
% 1.45/0.58  % (5799)Memory used [KB]: 6396
% 1.45/0.58  % (5799)Time elapsed: 0.093 s
% 1.45/0.58  % (5799)------------------------------
% 1.45/0.58  % (5799)------------------------------
% 1.45/0.58  % (5791)Success in time 0.216 s
%------------------------------------------------------------------------------
