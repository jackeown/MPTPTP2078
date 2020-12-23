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
% DateTime   : Thu Dec  3 13:10:58 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 335 expanded)
%              Number of leaves         :   24 (  96 expanded)
%              Depth                    :   18
%              Number of atoms          :  168 ( 536 expanded)
%              Number of equality atoms :   74 ( 263 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f227,plain,(
    $false ),
    inference(global_subsumption,[],[f212,f226])).

fof(f226,plain,(
    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f225,f207])).

fof(f207,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f206,f53])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f206,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f203,f88])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f52,f86])).

% (29696)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f86,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f64,f85])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f75,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f77,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f78,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f79,f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f75,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

% (29702)Refutation not found, incomplete strategy% (29702)------------------------------
% (29702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29702)Termination reason: Refutation not found, incomplete strategy

% (29702)Memory used [KB]: 10618
% (29702)Time elapsed: 0.115 s
% (29702)------------------------------
% (29702)------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f65,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f203,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f51,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f67,f87])).

fof(f87,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f66,f86])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f225,plain,(
    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f224,f154])).

fof(f154,plain,(
    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f47,f144,f51,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
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

fof(f144,plain,(
    v4_pre_topc(k1_xboole_0,sK0) ),
    inference(unit_resulting_resolution,[],[f46,f47,f49,f51,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f224,plain,(
    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f174,f213])).

fof(f213,plain,(
    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f140,f209])).

fof(f209,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(backward_demodulation,[],[f128,f207])).

fof(f128,plain,(
    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f126,f110])).

fof(f110,plain,(
    k1_xboole_0 = k1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f49,f93,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f93,plain,(
    v1_xboole_0(k1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f91,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

fof(f91,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f47,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f126,plain,(
    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f91,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

fof(f140,plain,(
    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f51,f135])).

fof(f135,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f68,f128])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f174,plain,(
    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f47,f90,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f90,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f54,f50])).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f212,plain,(
    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f48,f209])).

fof(f48,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:39:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.17/0.52  % (29686)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.17/0.52  % (29689)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.17/0.52  % (29693)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.17/0.53  % (29709)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.17/0.53  % (29700)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.17/0.53  % (29701)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.17/0.53  % (29693)Refutation not found, incomplete strategy% (29693)------------------------------
% 1.17/0.53  % (29693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.53  % (29709)Refutation found. Thanks to Tanya!
% 1.17/0.53  % SZS status Theorem for theBenchmark
% 1.30/0.53  % (29692)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.30/0.54  % (29685)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.54  % (29693)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (29693)Memory used [KB]: 10618
% 1.30/0.54  % (29693)Time elapsed: 0.106 s
% 1.30/0.54  % (29693)------------------------------
% 1.30/0.54  % (29693)------------------------------
% 1.30/0.54  % (29685)Refutation not found, incomplete strategy% (29685)------------------------------
% 1.30/0.54  % (29685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (29685)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (29685)Memory used [KB]: 1663
% 1.30/0.54  % (29685)Time elapsed: 0.112 s
% 1.30/0.54  % (29685)------------------------------
% 1.30/0.54  % (29685)------------------------------
% 1.30/0.54  % (29702)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.30/0.54  % SZS output start Proof for theBenchmark
% 1.30/0.54  fof(f227,plain,(
% 1.30/0.54    $false),
% 1.30/0.54    inference(global_subsumption,[],[f212,f226])).
% 1.30/0.54  fof(f226,plain,(
% 1.30/0.54    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 1.30/0.54    inference(forward_demodulation,[],[f225,f207])).
% 1.30/0.54  fof(f207,plain,(
% 1.30/0.54    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.30/0.54    inference(forward_demodulation,[],[f206,f53])).
% 1.30/0.54  fof(f53,plain,(
% 1.30/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.30/0.54    inference(cnf_transformation,[],[f6])).
% 1.30/0.54  fof(f6,axiom,(
% 1.30/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.30/0.54  fof(f206,plain,(
% 1.30/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.30/0.54    inference(forward_demodulation,[],[f203,f88])).
% 1.30/0.54  fof(f88,plain,(
% 1.30/0.54    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 1.30/0.54    inference(definition_unfolding,[],[f52,f86])).
% 1.30/0.54  % (29696)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.30/0.54  fof(f86,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.30/0.54    inference(definition_unfolding,[],[f64,f85])).
% 1.30/0.54  fof(f85,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f65,f84])).
% 1.30/0.54  fof(f84,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f75,f83])).
% 1.30/0.54  fof(f83,plain,(
% 1.30/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f77,f82])).
% 1.30/0.54  fof(f82,plain,(
% 1.30/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f78,f81])).
% 1.30/0.54  fof(f81,plain,(
% 1.30/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f79,f80])).
% 1.30/0.54  fof(f80,plain,(
% 1.30/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f13])).
% 1.30/0.54  fof(f13,axiom,(
% 1.30/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.30/0.54  fof(f79,plain,(
% 1.30/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f12])).
% 1.30/0.54  fof(f12,axiom,(
% 1.30/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.30/0.54  fof(f78,plain,(
% 1.30/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f11])).
% 1.30/0.54  fof(f11,axiom,(
% 1.30/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.30/0.54  fof(f77,plain,(
% 1.30/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f10])).
% 1.30/0.54  fof(f10,axiom,(
% 1.30/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.30/0.54  fof(f75,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f9])).
% 1.30/0.54  % (29702)Refutation not found, incomplete strategy% (29702)------------------------------
% 1.30/0.54  % (29702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (29702)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (29702)Memory used [KB]: 10618
% 1.30/0.54  % (29702)Time elapsed: 0.115 s
% 1.30/0.54  % (29702)------------------------------
% 1.30/0.54  % (29702)------------------------------
% 1.30/0.54  fof(f9,axiom,(
% 1.30/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.30/0.54  fof(f65,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f8])).
% 1.30/0.54  fof(f8,axiom,(
% 1.30/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.30/0.54  fof(f64,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f19])).
% 1.30/0.54  fof(f19,axiom,(
% 1.30/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.30/0.54  fof(f52,plain,(
% 1.30/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f5])).
% 1.30/0.54  fof(f5,axiom,(
% 1.30/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.30/0.54  fof(f203,plain,(
% 1.30/0.54    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)))) )),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f51,f89])).
% 1.30/0.54  fof(f89,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.30/0.54    inference(definition_unfolding,[],[f67,f87])).
% 1.30/0.54  fof(f87,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.30/0.54    inference(definition_unfolding,[],[f66,f86])).
% 1.30/0.54  fof(f66,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f4])).
% 1.30/0.54  fof(f4,axiom,(
% 1.30/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.30/0.54  fof(f67,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f40])).
% 1.30/0.54  fof(f40,plain,(
% 1.30/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f15])).
% 1.30/0.54  fof(f15,axiom,(
% 1.30/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.30/0.54  fof(f51,plain,(
% 1.30/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f18])).
% 1.30/0.54  fof(f18,axiom,(
% 1.30/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.30/0.54  fof(f225,plain,(
% 1.30/0.54    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 1.30/0.54    inference(forward_demodulation,[],[f224,f154])).
% 1.30/0.54  fof(f154,plain,(
% 1.30/0.54    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f47,f144,f51,f60])).
% 1.30/0.54  fof(f60,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.30/0.54    inference(cnf_transformation,[],[f37])).
% 1.30/0.54  fof(f37,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.30/0.54    inference(flattening,[],[f36])).
% 1.30/0.54  fof(f36,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f26])).
% 1.30/0.54  fof(f26,axiom,(
% 1.30/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.30/0.54  fof(f144,plain,(
% 1.30/0.54    v4_pre_topc(k1_xboole_0,sK0)),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f46,f47,f49,f51,f61])).
% 1.30/0.54  fof(f61,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f39])).
% 1.30/0.54  fof(f39,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.30/0.54    inference(flattening,[],[f38])).
% 1.30/0.54  fof(f38,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f22])).
% 1.30/0.54  fof(f22,axiom,(
% 1.30/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 1.30/0.54  fof(f49,plain,(
% 1.30/0.54    v1_xboole_0(k1_xboole_0)),
% 1.30/0.54    inference(cnf_transformation,[],[f3])).
% 1.30/0.54  fof(f3,axiom,(
% 1.30/0.54    v1_xboole_0(k1_xboole_0)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.30/0.54  fof(f46,plain,(
% 1.30/0.54    v2_pre_topc(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f31])).
% 1.30/0.54  fof(f31,plain,(
% 1.30/0.54    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.30/0.54    inference(flattening,[],[f30])).
% 1.30/0.54  fof(f30,plain,(
% 1.30/0.54    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f29])).
% 1.30/0.54  fof(f29,negated_conjecture,(
% 1.30/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 1.30/0.54    inference(negated_conjecture,[],[f28])).
% 1.30/0.54  fof(f28,conjecture,(
% 1.30/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 1.30/0.54  fof(f47,plain,(
% 1.30/0.54    l1_pre_topc(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f31])).
% 1.30/0.54  fof(f224,plain,(
% 1.30/0.54    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0))),
% 1.30/0.54    inference(backward_demodulation,[],[f174,f213])).
% 1.30/0.54  fof(f213,plain,(
% 1.30/0.54    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.30/0.54    inference(backward_demodulation,[],[f140,f209])).
% 1.30/0.54  fof(f209,plain,(
% 1.30/0.54    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 1.30/0.54    inference(backward_demodulation,[],[f128,f207])).
% 1.30/0.54  fof(f128,plain,(
% 1.30/0.54    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),
% 1.30/0.54    inference(forward_demodulation,[],[f126,f110])).
% 1.30/0.54  fof(f110,plain,(
% 1.30/0.54    k1_xboole_0 = k1_struct_0(sK0)),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f49,f93,f74])).
% 1.30/0.54  fof(f74,plain,(
% 1.30/0.54    ( ! [X0,X1] : (X0 = X1 | ~v1_xboole_0(X0) | ~v1_xboole_0(X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f43])).
% 1.30/0.54  fof(f43,plain,(
% 1.30/0.54    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f7])).
% 1.30/0.54  fof(f7,axiom,(
% 1.30/0.54    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 1.30/0.54  fof(f93,plain,(
% 1.30/0.54    v1_xboole_0(k1_struct_0(sK0))),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f91,f55])).
% 1.30/0.54  fof(f55,plain,(
% 1.30/0.54    ( ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f32])).
% 1.30/0.54  fof(f32,plain,(
% 1.30/0.54    ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f24])).
% 1.30/0.54  fof(f24,axiom,(
% 1.30/0.54    ! [X0] : (l1_struct_0(X0) => v1_xboole_0(k1_struct_0(X0)))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).
% 1.30/0.54  fof(f91,plain,(
% 1.30/0.54    l1_struct_0(sK0)),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f47,f57])).
% 1.30/0.54  fof(f57,plain,(
% 1.30/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f34])).
% 1.30/0.54  fof(f34,plain,(
% 1.30/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f23])).
% 1.30/0.54  fof(f23,axiom,(
% 1.30/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.30/0.54  fof(f126,plain,(
% 1.30/0.54    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0))),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f91,f56])).
% 1.30/0.54  fof(f56,plain,(
% 1.30/0.54    ( ! [X0] : (k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f33])).
% 1.30/0.54  fof(f33,plain,(
% 1.30/0.54    ! [X0] : (k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) | ~l1_struct_0(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f25])).
% 1.30/0.54  fof(f25,axiom,(
% 1.30/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).
% 1.30/0.54  fof(f140,plain,(
% 1.30/0.54    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f51,f135])).
% 1.30/0.54  fof(f135,plain,(
% 1.30/0.54    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.30/0.54    inference(superposition,[],[f68,f128])).
% 1.30/0.54  fof(f68,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f41])).
% 1.30/0.54  fof(f41,plain,(
% 1.30/0.54    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f17])).
% 1.30/0.54  fof(f17,axiom,(
% 1.30/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.30/0.54  fof(f174,plain,(
% 1.30/0.54    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f47,f90,f58])).
% 1.30/0.54  fof(f58,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f35])).
% 1.30/0.54  fof(f35,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f27])).
% 1.30/0.54  fof(f27,axiom,(
% 1.30/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 1.30/0.54  fof(f90,plain,(
% 1.30/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.30/0.54    inference(forward_demodulation,[],[f54,f50])).
% 1.30/0.54  fof(f50,plain,(
% 1.30/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.30/0.54    inference(cnf_transformation,[],[f14])).
% 1.30/0.54  fof(f14,axiom,(
% 1.30/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.30/0.54  fof(f54,plain,(
% 1.30/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f16])).
% 1.30/0.54  fof(f16,axiom,(
% 1.30/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.30/0.54  fof(f212,plain,(
% 1.30/0.54    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))),
% 1.30/0.54    inference(backward_demodulation,[],[f48,f209])).
% 1.30/0.54  fof(f48,plain,(
% 1.30/0.54    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))),
% 1.30/0.54    inference(cnf_transformation,[],[f31])).
% 1.30/0.54  % SZS output end Proof for theBenchmark
% 1.30/0.54  % (29709)------------------------------
% 1.30/0.54  % (29709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (29709)Termination reason: Refutation
% 1.30/0.54  
% 1.30/0.54  % (29709)Memory used [KB]: 6396
% 1.30/0.54  % (29709)Time elapsed: 0.110 s
% 1.30/0.54  % (29709)------------------------------
% 1.30/0.54  % (29709)------------------------------
% 1.30/0.54  % (29687)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.54  % (29689)Refutation not found, incomplete strategy% (29689)------------------------------
% 1.30/0.54  % (29689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (29689)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (29689)Memory used [KB]: 6268
% 1.30/0.54  % (29689)Time elapsed: 0.114 s
% 1.30/0.54  % (29689)------------------------------
% 1.30/0.54  % (29689)------------------------------
% 1.30/0.54  % (29684)Success in time 0.175 s
%------------------------------------------------------------------------------
