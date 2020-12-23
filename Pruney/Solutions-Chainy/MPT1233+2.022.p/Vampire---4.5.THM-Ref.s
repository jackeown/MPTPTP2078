%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 204 expanded)
%              Number of leaves         :   23 (  61 expanded)
%              Depth                    :   16
%              Number of atoms          :  170 ( 361 expanded)
%              Number of equality atoms :   74 ( 181 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(subsumption_resolution,[],[f110,f79])).

fof(f79,plain,(
    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f42,f78])).

fof(f78,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f49,f76])).

fof(f76,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f50,f41])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f42,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f110,plain,(
    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f109,f102])).

fof(f102,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f100,f73])).

fof(f73,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f47,f72])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f58,f71])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f62,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f63,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f100,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f75,f45])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f59,f72])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f109,plain,(
    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f108,f91])).

fof(f91,plain,(
    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f90,f41])).

fof(f90,plain,
    ( k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f88,f86])).

fof(f86,plain,(
    v4_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f85,f40])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f84,f41])).

fof(f84,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v4_pre_topc(k1_xboole_0,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f82,f43])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v4_pre_topc(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f54,f45])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f88,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k1_xboole_0,X0)
      | k1_xboole_0 = k2_pre_topc(X0,k1_xboole_0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f52,f45])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f108,plain,(
    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f99,f104])).

fof(f104,plain,(
    ! [X1] : k1_xboole_0 = k3_subset_1(X1,X1) ),
    inference(forward_demodulation,[],[f103,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f103,plain,(
    ! [X1] : k3_subset_1(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f101,f74])).

fof(f74,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f55,f71])).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f101,plain,(
    ! [X1] : k3_subset_1(X1,X1) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(resolution,[],[f75,f77])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f48,f44])).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f99,plain,(
    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f97,f41])).

fof(f97,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | k1_tops_1(X1,u1_struct_0(X1)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    inference(resolution,[],[f51,f77])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:05:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.41  % (18700)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.41  % (18700)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f111,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(subsumption_resolution,[],[f110,f79])).
% 0.21/0.41  fof(f79,plain,(
% 0.21/0.41    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))),
% 0.21/0.41    inference(backward_demodulation,[],[f42,f78])).
% 0.21/0.41  fof(f78,plain,(
% 0.21/0.41    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.41    inference(resolution,[],[f49,f76])).
% 0.21/0.41  fof(f76,plain,(
% 0.21/0.41    l1_struct_0(sK0)),
% 0.21/0.41    inference(resolution,[],[f50,f41])).
% 0.21/0.41  fof(f41,plain,(
% 0.21/0.41    l1_pre_topc(sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f39])).
% 0.21/0.41  fof(f39,plain,(
% 0.21/0.41    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f38])).
% 0.21/0.41  fof(f38,plain,(
% 0.21/0.41    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.41    inference(flattening,[],[f26])).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.41    inference(ennf_transformation,[],[f24])).
% 0.21/0.41  fof(f24,negated_conjecture,(
% 0.21/0.41    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.21/0.41    inference(negated_conjecture,[],[f23])).
% 0.21/0.41  fof(f23,conjecture,(
% 0.21/0.41    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 0.21/0.41  fof(f50,plain,(
% 0.21/0.41    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f29])).
% 0.21/0.41  fof(f29,plain,(
% 0.21/0.41    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f20])).
% 0.21/0.41  fof(f20,axiom,(
% 0.21/0.41    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.41  fof(f49,plain,(
% 0.21/0.41    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f28])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f19])).
% 0.21/0.41  fof(f19,axiom,(
% 0.21/0.41    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.41  fof(f42,plain,(
% 0.21/0.41    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.21/0.41    inference(cnf_transformation,[],[f39])).
% 0.21/0.41  fof(f110,plain,(
% 0.21/0.41    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 0.21/0.41    inference(forward_demodulation,[],[f109,f102])).
% 0.21/0.41  fof(f102,plain,(
% 0.21/0.41    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.41    inference(forward_demodulation,[],[f100,f73])).
% 0.21/0.41  fof(f73,plain,(
% 0.21/0.41    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0) )),
% 0.21/0.41    inference(definition_unfolding,[],[f47,f72])).
% 0.21/0.41  fof(f72,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.21/0.41    inference(definition_unfolding,[],[f58,f71])).
% 0.21/0.41  fof(f71,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.41    inference(definition_unfolding,[],[f56,f70])).
% 0.21/0.41  fof(f70,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.41    inference(definition_unfolding,[],[f57,f69])).
% 0.21/0.41  fof(f69,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.41    inference(definition_unfolding,[],[f60,f68])).
% 0.21/0.41  fof(f68,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.41    inference(definition_unfolding,[],[f62,f67])).
% 0.21/0.41  fof(f67,plain,(
% 0.21/0.41    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.41    inference(definition_unfolding,[],[f63,f66])).
% 0.21/0.41  fof(f66,plain,(
% 0.21/0.41    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.41    inference(definition_unfolding,[],[f64,f65])).
% 0.21/0.41  fof(f65,plain,(
% 0.21/0.41    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f11,axiom,(
% 0.21/0.41    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.41  fof(f64,plain,(
% 0.21/0.41    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,axiom,(
% 0.21/0.41    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.41  fof(f63,plain,(
% 0.21/0.41    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,axiom,(
% 0.21/0.41    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.41  fof(f62,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,axiom,(
% 0.21/0.41    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.41  fof(f60,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f7])).
% 0.21/0.41  fof(f7,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.41  fof(f57,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,axiom,(
% 0.21/0.41    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.41  fof(f56,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f16])).
% 0.21/0.41  fof(f16,axiom,(
% 0.21/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.41  fof(f58,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.41  fof(f47,plain,(
% 0.21/0.41    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.41    inference(cnf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.41  fof(f100,plain,(
% 0.21/0.41    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.21/0.41    inference(resolution,[],[f75,f45])).
% 0.21/0.41  fof(f45,plain,(
% 0.21/0.41    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  fof(f15,axiom,(
% 0.21/0.41    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.41  fof(f75,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.21/0.41    inference(definition_unfolding,[],[f59,f72])).
% 0.21/0.41  fof(f59,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f35])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.41    inference(ennf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,axiom,(
% 0.21/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.41  fof(f109,plain,(
% 0.21/0.41    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),
% 0.21/0.41    inference(forward_demodulation,[],[f108,f91])).
% 0.21/0.41  fof(f91,plain,(
% 0.21/0.41    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 0.21/0.41    inference(subsumption_resolution,[],[f90,f41])).
% 0.21/0.41  fof(f90,plain,(
% 0.21/0.41    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | ~l1_pre_topc(sK0)),
% 0.21/0.41    inference(resolution,[],[f88,f86])).
% 0.21/0.41  fof(f86,plain,(
% 0.21/0.41    v4_pre_topc(k1_xboole_0,sK0)),
% 0.21/0.41    inference(subsumption_resolution,[],[f85,f40])).
% 0.21/0.41  fof(f40,plain,(
% 0.21/0.41    v2_pre_topc(sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f39])).
% 0.21/0.41  fof(f85,plain,(
% 0.21/0.41    v4_pre_topc(k1_xboole_0,sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.41    inference(resolution,[],[f84,f41])).
% 0.21/0.41  fof(f84,plain,(
% 0.21/0.41    ( ! [X0] : (~l1_pre_topc(X0) | v4_pre_topc(k1_xboole_0,X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.41    inference(subsumption_resolution,[],[f82,f43])).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    v1_xboole_0(k1_xboole_0)),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    v1_xboole_0(k1_xboole_0)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.41  fof(f82,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | v4_pre_topc(k1_xboole_0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.41    inference(resolution,[],[f54,f45])).
% 0.21/0.41  fof(f54,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f34])).
% 0.21/0.41  fof(f34,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.41    inference(flattening,[],[f33])).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.41    inference(ennf_transformation,[],[f18])).
% 0.21/0.41  fof(f18,axiom,(
% 0.21/0.41    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.21/0.41  fof(f88,plain,(
% 0.21/0.41    ( ! [X0] : (~v4_pre_topc(k1_xboole_0,X0) | k1_xboole_0 = k2_pre_topc(X0,k1_xboole_0) | ~l1_pre_topc(X0)) )),
% 0.21/0.41    inference(resolution,[],[f52,f45])).
% 0.21/0.41  fof(f52,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f32])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.41    inference(flattening,[],[f31])).
% 0.21/0.41  fof(f31,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f21])).
% 0.21/0.41  fof(f21,axiom,(
% 0.21/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.41  fof(f108,plain,(
% 0.21/0.41    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0))),
% 0.21/0.41    inference(backward_demodulation,[],[f99,f104])).
% 0.21/0.41  fof(f104,plain,(
% 0.21/0.41    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,X1)) )),
% 0.21/0.41    inference(forward_demodulation,[],[f103,f46])).
% 0.21/0.41  fof(f46,plain,(
% 0.21/0.41    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.41  fof(f103,plain,(
% 0.21/0.41    ( ! [X1] : (k3_subset_1(X1,X1) = k5_xboole_0(X1,X1)) )),
% 0.21/0.41    inference(forward_demodulation,[],[f101,f74])).
% 0.21/0.41  fof(f74,plain,(
% 0.21/0.41    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.21/0.41    inference(definition_unfolding,[],[f55,f71])).
% 0.21/0.41  fof(f55,plain,(
% 0.21/0.41    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.41    inference(cnf_transformation,[],[f25])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.41    inference(rectify,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.41  fof(f101,plain,(
% 0.21/0.41    ( ! [X1] : (k3_subset_1(X1,X1) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) )),
% 0.21/0.41    inference(resolution,[],[f75,f77])).
% 0.21/0.41  fof(f77,plain,(
% 0.21/0.41    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.41    inference(forward_demodulation,[],[f48,f44])).
% 0.21/0.41  fof(f44,plain,(
% 0.21/0.41    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,axiom,(
% 0.21/0.41    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.41  fof(f48,plain,(
% 0.21/0.41    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f14])).
% 0.21/0.41  fof(f14,axiom,(
% 0.21/0.41    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.41  fof(f99,plain,(
% 0.21/0.41    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.21/0.41    inference(resolution,[],[f97,f41])).
% 0.21/0.41  fof(f97,plain,(
% 0.21/0.41    ( ! [X1] : (~l1_pre_topc(X1) | k1_tops_1(X1,u1_struct_0(X1)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),u1_struct_0(X1))))) )),
% 0.21/0.41    inference(resolution,[],[f51,f77])).
% 0.21/0.41  fof(f51,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f30])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f22])).
% 0.21/0.41  fof(f22,axiom,(
% 0.21/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (18700)------------------------------
% 0.21/0.41  % (18700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (18700)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (18700)Memory used [KB]: 1663
% 0.21/0.41  % (18700)Time elapsed: 0.007 s
% 0.21/0.41  % (18700)------------------------------
% 0.21/0.41  % (18700)------------------------------
% 0.21/0.42  % (18687)Success in time 0.061 s
%------------------------------------------------------------------------------
