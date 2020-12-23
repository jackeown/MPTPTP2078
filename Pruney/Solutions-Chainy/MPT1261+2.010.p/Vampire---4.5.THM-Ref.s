%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:48 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  177 (44521 expanded)
%              Number of leaves         :   24 (13390 expanded)
%              Depth                    :   36
%              Number of atoms          :  343 (127060 expanded)
%              Number of equality atoms :  155 (51298 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1736,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1735,f1123])).

fof(f1123,plain,(
    sK1 != k2_pre_topc(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f50,f49,f51,f1074,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f1074,plain,(
    ~ v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1072,f483])).

fof(f483,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f288,f479])).

fof(f479,plain,(
    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f356,f426])).

fof(f426,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f348,f99])).

fof(f99,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f50,f51,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f348,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(backward_demodulation,[],[f102,f337])).

fof(f337,plain,(
    ! [X0] : k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(sK1,sK1,X0) ),
    inference(unit_resulting_resolution,[],[f315,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f77,f79])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f67,f64])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f315,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f237,f221])).

fof(f221,plain,(
    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
    inference(superposition,[],[f102,f81])).

fof(f81,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f55,f79])).

fof(f55,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f237,plain,(
    ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f225,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f225,plain,(
    ! [X1] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X1),sK1) ),
    inference(superposition,[],[f83,f102])).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f62,f79])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f102,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f51,f87])).

fof(f356,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k7_subset_1(sK1,sK1,X0)) ),
    inference(backward_demodulation,[],[f244,f348])).

fof(f244,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
    inference(backward_demodulation,[],[f224,f243])).

fof(f243,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) ),
    inference(forward_demodulation,[],[f238,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f238,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)) ),
    inference(unit_resulting_resolution,[],[f225,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f68,f64])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f224,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) ),
    inference(superposition,[],[f84,f102])).

fof(f84,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f66,f64,f79,f79])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f288,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f287,f63])).

fof(f287,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) ),
    inference(resolution,[],[f256,f85])).

fof(f256,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f93,f51])).

fof(f93,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | r1_tarski(k2_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f50,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f1072,plain,
    ( k2_tops_1(sK0,sK1) != k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f368,f1070])).

fof(f1070,plain,(
    k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1067,f271])).

fof(f271,plain,(
    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f265,f250])).

fof(f250,plain,(
    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f247,f63])).

fof(f247,plain,(
    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)) ),
    inference(unit_resulting_resolution,[],[f241,f85])).

fof(f241,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f225,f99])).

fof(f265,plain,(
    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f246,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f69,f79])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f246,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f241,f76])).

fof(f1067,plain,(
    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f359,f250])).

fof(f359,plain,(
    ! [X0] : k3_subset_1(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(sK1,sK1,X0) ),
    inference(backward_demodulation,[],[f318,f348])).

fof(f318,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k3_subset_1(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    inference(forward_demodulation,[],[f307,f317])).

fof(f317,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(sK1,X0)) = k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
    inference(forward_demodulation,[],[f316,f244])).

fof(f316,plain,(
    ! [X0] : k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
    inference(forward_demodulation,[],[f308,f243])).

fof(f308,plain,(
    ! [X0] : k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) = k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f237,f86])).

fof(f307,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k3_subset_1(sK1,k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f237,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f368,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f53,f348])).

fof(f53,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).

fof(f43,plain,
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

fof(f44,plain,
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f1735,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f1734,f1541])).

fof(f1541,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f81,f1530])).

fof(f1530,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(superposition,[],[f1523,f63])).

fof(f1523,plain,(
    ! [X1] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X1)) ),
    inference(forward_demodulation,[],[f1515,f1497])).

fof(f1497,plain,(
    k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1487,f623])).

fof(f623,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f622,f81])).

fof(f622,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f619,f521])).

fof(f521,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f491,f497])).

fof(f497,plain,(
    k5_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f496,f491])).

fof(f496,plain,(
    k5_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))) ),
    inference(backward_demodulation,[],[f486,f495])).

fof(f495,plain,(
    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)) = k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)))) ),
    inference(forward_demodulation,[],[f492,f63])).

fof(f492,plain,(
    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)) = k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f487,f85])).

fof(f487,plain,(
    r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k1_xboole_0) ),
    inference(superposition,[],[f83,f481])).

fof(f481,plain,(
    k5_xboole_0(sK1,sK1) = k1_setfam_1(k2_tarski(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f477,f63])).

fof(f477,plain,(
    k5_xboole_0(sK1,sK1) = k1_setfam_1(k2_tarski(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f356,f427])).

fof(f427,plain,(
    sK1 = k7_subset_1(sK1,sK1,k1_xboole_0) ),
    inference(superposition,[],[f348,f221])).

fof(f486,plain,(
    k5_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))))) ),
    inference(superposition,[],[f84,f481])).

fof(f491,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f54,f487,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f619,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))))) ),
    inference(superposition,[],[f84,f520])).

fof(f520,plain,(
    k1_setfam_1(k2_tarski(k1_xboole_0,sK1)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f481,f497])).

fof(f1487,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k7_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f535,f82])).

fof(f82,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f61,f64])).

fof(f61,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f535,plain,(
    ! [X0] : k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) ),
    inference(unit_resulting_resolution,[],[f525,f87])).

fof(f525,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f524,f521])).

fof(f524,plain,(
    m1_subset_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f489,f497])).

fof(f489,plain,(
    m1_subset_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f487,f76])).

fof(f1515,plain,(
    ! [X1] : k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k7_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1499,f1503])).

fof(f1503,plain,(
    ! [X0] : k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f54,f1492,f74])).

fof(f1492,plain,(
    ! [X1] : r1_tarski(k7_subset_1(k1_xboole_0,k1_xboole_0,X1),k1_xboole_0) ),
    inference(superposition,[],[f83,f535])).

fof(f1499,plain,(
    ! [X1] : k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k7_subset_1(k1_xboole_0,k1_xboole_0,k7_subset_1(k1_xboole_0,k1_xboole_0,X1)) ),
    inference(forward_demodulation,[],[f1489,f535])).

fof(f1489,plain,(
    ! [X1] : k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k7_subset_1(k1_xboole_0,k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1)))) ),
    inference(superposition,[],[f535,f84])).

fof(f1734,plain,(
    k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1112,f1733])).

fof(f1733,plain,(
    k1_xboole_0 = k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f1727,f1564])).

fof(f1564,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f1563,f82])).

fof(f1563,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) ),
    inference(forward_demodulation,[],[f1557,f1541])).

fof(f1557,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_xboole_0)))) ),
    inference(superposition,[],[f84,f1530])).

fof(f1727,plain,(
    k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f1101,f1078])).

fof(f1078,plain,(
    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f479,f1075])).

fof(f1075,plain,(
    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1073,f1074])).

fof(f1073,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f367,f1070])).

fof(f367,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f52,f348])).

fof(f52,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f1101,plain,(
    ! [X0] : k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1)))) = k7_subset_1(sK1,k2_tops_1(sK0,sK1),X0) ),
    inference(backward_demodulation,[],[f830,f1099])).

fof(f1099,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k7_subset_1(sK1,k2_tops_1(sK0,sK1),X0) ),
    inference(backward_demodulation,[],[f129,f1085])).

fof(f1085,plain,(
    ! [X0] : k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X0))) = k7_subset_1(sK1,k2_tops_1(sK0,sK1),X0) ),
    inference(backward_demodulation,[],[f802,f1075])).

fof(f802,plain,(
    ! [X0] : k7_subset_1(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),X0) = k5_xboole_0(k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),k1_setfam_1(k2_tarski(k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),X0))) ),
    inference(unit_resulting_resolution,[],[f785,f87])).

fof(f785,plain,(
    m1_subset_1(k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f784,f76])).

fof(f784,plain,(
    r1_tarski(k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1) ),
    inference(superposition,[],[f83,f250])).

fof(f129,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X0))) ),
    inference(unit_resulting_resolution,[],[f97,f87])).

fof(f97,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f50,f51,f71])).

fof(f71,plain,(
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

fof(f830,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1)))) ),
    inference(superposition,[],[f129,f63])).

fof(f1112,plain,(
    k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)) ),
    inference(backward_demodulation,[],[f140,f1099])).

fof(f140,plain,(
    k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)) ),
    inference(forward_demodulation,[],[f139,f98])).

fof(f98,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f50,f51,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f139,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)) ),
    inference(forward_demodulation,[],[f127,f129])).

fof(f127,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)))) ),
    inference(unit_resulting_resolution,[],[f51,f97,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f78,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f65,f79])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:58:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (31089)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (31097)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (31082)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (31100)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (31096)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (31080)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (31079)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (31088)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (31076)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (31077)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (31084)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (31094)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (31074)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.56  % (31087)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (31099)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.42/0.56  % (31084)Refutation not found, incomplete strategy% (31084)------------------------------
% 1.42/0.56  % (31084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (31086)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.42/0.56  % (31093)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.42/0.56  % (31083)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.42/0.56  % (31095)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.42/0.56  % (31084)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (31084)Memory used [KB]: 10746
% 1.42/0.56  % (31084)Time elapsed: 0.139 s
% 1.42/0.56  % (31084)------------------------------
% 1.42/0.56  % (31084)------------------------------
% 1.42/0.56  % (31103)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.42/0.57  % (31092)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.42/0.57  % (31101)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.42/0.57  % (31102)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.42/0.57  % (31102)Refutation not found, incomplete strategy% (31102)------------------------------
% 1.42/0.57  % (31102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (31102)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (31102)Memory used [KB]: 10746
% 1.42/0.57  % (31102)Time elapsed: 0.146 s
% 1.42/0.57  % (31102)------------------------------
% 1.42/0.57  % (31102)------------------------------
% 1.42/0.57  % (31090)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.42/0.57  % (31075)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.42/0.57  % (31078)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.42/0.57  % (31090)Refutation not found, incomplete strategy% (31090)------------------------------
% 1.42/0.57  % (31090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (31090)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (31090)Memory used [KB]: 10618
% 1.42/0.57  % (31090)Time elapsed: 0.141 s
% 1.42/0.57  % (31090)------------------------------
% 1.42/0.57  % (31090)------------------------------
% 1.42/0.57  % (31091)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.42/0.57  % (31085)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.57/0.59  % (31081)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.57/0.59  % (31098)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.10/0.68  % (31085)Refutation found. Thanks to Tanya!
% 2.10/0.68  % SZS status Theorem for theBenchmark
% 2.10/0.68  % (31113)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.10/0.69  % (31117)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.10/0.69  % (31118)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.10/0.70  % SZS output start Proof for theBenchmark
% 2.10/0.70  fof(f1736,plain,(
% 2.10/0.70    $false),
% 2.10/0.70    inference(subsumption_resolution,[],[f1735,f1123])).
% 2.10/0.70  fof(f1123,plain,(
% 2.10/0.70    sK1 != k2_pre_topc(sK0,sK1)),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f50,f49,f51,f1074,f59])).
% 2.10/0.70  fof(f59,plain,(
% 2.10/0.70    ( ! [X0,X1] : (~v2_pre_topc(X0) | k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f30])).
% 2.10/0.70  fof(f30,plain,(
% 2.10/0.70    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.70    inference(flattening,[],[f29])).
% 2.10/0.70  fof(f29,plain,(
% 2.10/0.70    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.70    inference(ennf_transformation,[],[f17])).
% 2.10/0.70  fof(f17,axiom,(
% 2.10/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.10/0.70  fof(f1074,plain,(
% 2.10/0.70    ~v4_pre_topc(sK1,sK0)),
% 2.10/0.70    inference(subsumption_resolution,[],[f1072,f483])).
% 2.10/0.70  fof(f483,plain,(
% 2.10/0.70    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.10/0.70    inference(backward_demodulation,[],[f288,f479])).
% 2.10/0.70  fof(f479,plain,(
% 2.10/0.70    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.10/0.70    inference(superposition,[],[f356,f426])).
% 2.10/0.70  fof(f426,plain,(
% 2.10/0.70    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))),
% 2.10/0.70    inference(superposition,[],[f348,f99])).
% 2.10/0.70  fof(f99,plain,(
% 2.10/0.70    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f50,f51,f56])).
% 2.10/0.70  fof(f56,plain,(
% 2.10/0.70    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.10/0.70    inference(cnf_transformation,[],[f27])).
% 2.10/0.70  fof(f27,plain,(
% 2.10/0.70    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.70    inference(ennf_transformation,[],[f21])).
% 2.10/0.70  fof(f21,axiom,(
% 2.10/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.10/0.70  fof(f348,plain,(
% 2.10/0.70    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)) )),
% 2.10/0.70    inference(backward_demodulation,[],[f102,f337])).
% 2.10/0.70  fof(f337,plain,(
% 2.10/0.70    ( ! [X0] : (k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(sK1,sK1,X0)) )),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f315,f87])).
% 2.10/0.70  fof(f87,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 2.10/0.70    inference(definition_unfolding,[],[f77,f79])).
% 2.10/0.70  fof(f79,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.10/0.70    inference(definition_unfolding,[],[f67,f64])).
% 2.10/0.70  fof(f64,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.10/0.70    inference(cnf_transformation,[],[f15])).
% 2.10/0.70  fof(f15,axiom,(
% 2.10/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.10/0.70  fof(f67,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.10/0.70    inference(cnf_transformation,[],[f3])).
% 2.10/0.70  fof(f3,axiom,(
% 2.10/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.10/0.70  fof(f77,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.70    inference(cnf_transformation,[],[f38])).
% 2.10/0.70  fof(f38,plain,(
% 2.10/0.70    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.70    inference(ennf_transformation,[],[f14])).
% 2.10/0.70  fof(f14,axiom,(
% 2.10/0.70    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.10/0.70  fof(f315,plain,(
% 2.10/0.70    m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 2.10/0.70    inference(superposition,[],[f237,f221])).
% 2.10/0.70  fof(f221,plain,(
% 2.10/0.70    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)),
% 2.10/0.70    inference(superposition,[],[f102,f81])).
% 2.10/0.70  fof(f81,plain,(
% 2.10/0.70    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 2.10/0.70    inference(definition_unfolding,[],[f55,f79])).
% 2.10/0.70  fof(f55,plain,(
% 2.10/0.70    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.10/0.70    inference(cnf_transformation,[],[f7])).
% 2.10/0.70  fof(f7,axiom,(
% 2.10/0.70    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.10/0.70  fof(f237,plain,(
% 2.10/0.70    ( ! [X0] : (m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(sK1))) )),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f225,f76])).
% 2.10/0.70  fof(f76,plain,(
% 2.10/0.70    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f48])).
% 2.10/0.70  fof(f48,plain,(
% 2.10/0.70    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.10/0.70    inference(nnf_transformation,[],[f16])).
% 2.10/0.70  fof(f16,axiom,(
% 2.10/0.70    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.10/0.70  fof(f225,plain,(
% 2.10/0.70    ( ! [X1] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X1),sK1)) )),
% 2.10/0.70    inference(superposition,[],[f83,f102])).
% 2.10/0.70  fof(f83,plain,(
% 2.10/0.70    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 2.10/0.70    inference(definition_unfolding,[],[f62,f79])).
% 2.10/0.70  fof(f62,plain,(
% 2.10/0.70    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f6])).
% 2.10/0.70  fof(f6,axiom,(
% 2.10/0.70    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.10/0.70  fof(f102,plain,(
% 2.10/0.70    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) )),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f51,f87])).
% 2.10/0.70  fof(f356,plain,(
% 2.10/0.70    ( ! [X0] : (k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k7_subset_1(sK1,sK1,X0))) )),
% 2.10/0.70    inference(backward_demodulation,[],[f244,f348])).
% 2.10/0.70  fof(f244,plain,(
% 2.10/0.70    ( ! [X0] : (k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) )),
% 2.10/0.70    inference(backward_demodulation,[],[f224,f243])).
% 2.10/0.70  fof(f243,plain,(
% 2.10/0.70    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) )),
% 2.10/0.70    inference(forward_demodulation,[],[f238,f63])).
% 2.10/0.70  fof(f63,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f10])).
% 2.10/0.70  fof(f10,axiom,(
% 2.10/0.70    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.10/0.70  fof(f238,plain,(
% 2.10/0.70    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1))) )),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f225,f85])).
% 2.10/0.70  fof(f85,plain,(
% 2.10/0.70    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 2.10/0.70    inference(definition_unfolding,[],[f68,f64])).
% 2.10/0.70  fof(f68,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f33])).
% 2.10/0.70  fof(f33,plain,(
% 2.10/0.70    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.10/0.70    inference(ennf_transformation,[],[f4])).
% 2.10/0.70  fof(f4,axiom,(
% 2.10/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.10/0.70  fof(f224,plain,(
% 2.10/0.70    ( ! [X0] : (k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))))) )),
% 2.10/0.70    inference(superposition,[],[f84,f102])).
% 2.10/0.70  fof(f84,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 2.10/0.70    inference(definition_unfolding,[],[f66,f64,f79,f79])).
% 2.10/0.70  fof(f66,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.10/0.70    inference(cnf_transformation,[],[f8])).
% 2.10/0.70  fof(f8,axiom,(
% 2.10/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.10/0.70  fof(f288,plain,(
% 2.10/0.70    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~v4_pre_topc(sK1,sK0)),
% 2.10/0.70    inference(forward_demodulation,[],[f287,f63])).
% 2.10/0.70  fof(f287,plain,(
% 2.10/0.70    ~v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))),
% 2.10/0.70    inference(resolution,[],[f256,f85])).
% 2.10/0.70  fof(f256,plain,(
% 2.10/0.70    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~v4_pre_topc(sK1,sK0)),
% 2.10/0.70    inference(resolution,[],[f93,f51])).
% 2.10/0.70  fof(f93,plain,(
% 2.10/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | r1_tarski(k2_tops_1(sK0,X0),X0)) )),
% 2.10/0.70    inference(resolution,[],[f50,f60])).
% 2.10/0.70  fof(f60,plain,(
% 2.10/0.70    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f32])).
% 2.10/0.70  fof(f32,plain,(
% 2.10/0.70    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.70    inference(flattening,[],[f31])).
% 2.10/0.70  fof(f31,plain,(
% 2.10/0.70    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.70    inference(ennf_transformation,[],[f20])).
% 2.10/0.70  fof(f20,axiom,(
% 2.10/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 2.10/0.70  fof(f1072,plain,(
% 2.10/0.70    k2_tops_1(sK0,sK1) != k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.10/0.70    inference(backward_demodulation,[],[f368,f1070])).
% 2.10/0.70  fof(f1070,plain,(
% 2.10/0.70    k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 2.10/0.70    inference(forward_demodulation,[],[f1067,f271])).
% 2.10/0.70  fof(f271,plain,(
% 2.10/0.70    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.10/0.70    inference(forward_demodulation,[],[f265,f250])).
% 2.10/0.70  fof(f250,plain,(
% 2.10/0.70    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))),
% 2.10/0.70    inference(forward_demodulation,[],[f247,f63])).
% 2.10/0.70  fof(f247,plain,(
% 2.10/0.70    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1))),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f241,f85])).
% 2.10/0.70  fof(f241,plain,(
% 2.10/0.70    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.10/0.70    inference(superposition,[],[f225,f99])).
% 2.10/0.70  fof(f265,plain,(
% 2.10/0.70    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))))),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f246,f86])).
% 2.10/0.70  fof(f86,plain,(
% 2.10/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.10/0.70    inference(definition_unfolding,[],[f69,f79])).
% 2.10/0.70  fof(f69,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.70    inference(cnf_transformation,[],[f34])).
% 2.10/0.70  fof(f34,plain,(
% 2.10/0.70    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.70    inference(ennf_transformation,[],[f11])).
% 2.10/0.70  fof(f11,axiom,(
% 2.10/0.70    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.10/0.70  fof(f246,plain,(
% 2.10/0.70    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f241,f76])).
% 2.10/0.70  fof(f1067,plain,(
% 2.10/0.70    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 2.10/0.70    inference(superposition,[],[f359,f250])).
% 2.10/0.70  fof(f359,plain,(
% 2.10/0.70    ( ! [X0] : (k3_subset_1(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(sK1,sK1,X0)) )),
% 2.10/0.70    inference(backward_demodulation,[],[f318,f348])).
% 2.10/0.70  fof(f318,plain,(
% 2.10/0.70    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k3_subset_1(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) )),
% 2.10/0.70    inference(forward_demodulation,[],[f307,f317])).
% 2.10/0.70  fof(f317,plain,(
% 2.10/0.70    ( ! [X0] : (k1_setfam_1(k2_tarski(sK1,X0)) = k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) )),
% 2.10/0.70    inference(forward_demodulation,[],[f316,f244])).
% 2.10/0.70  fof(f316,plain,(
% 2.10/0.70    ( ! [X0] : (k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) )),
% 2.10/0.70    inference(forward_demodulation,[],[f308,f243])).
% 2.10/0.70  fof(f308,plain,(
% 2.10/0.70    ( ! [X0] : (k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) = k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) )),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f237,f86])).
% 2.10/0.70  fof(f307,plain,(
% 2.10/0.70    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k3_subset_1(sK1,k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) )),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f237,f70])).
% 2.10/0.70  fof(f70,plain,(
% 2.10/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.10/0.70    inference(cnf_transformation,[],[f35])).
% 2.10/0.70  fof(f35,plain,(
% 2.10/0.70    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.70    inference(ennf_transformation,[],[f12])).
% 2.10/0.70  fof(f12,axiom,(
% 2.10/0.70    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.10/0.70  fof(f368,plain,(
% 2.10/0.70    k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.10/0.70    inference(backward_demodulation,[],[f53,f348])).
% 2.10/0.70  fof(f53,plain,(
% 2.10/0.70    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.10/0.70    inference(cnf_transformation,[],[f45])).
% 2.10/0.70  fof(f45,plain,(
% 2.10/0.70    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.10/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).
% 2.10/0.70  fof(f43,plain,(
% 2.10/0.70    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.10/0.70    introduced(choice_axiom,[])).
% 2.10/0.70  fof(f44,plain,(
% 2.10/0.70    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.10/0.70    introduced(choice_axiom,[])).
% 2.10/0.70  fof(f42,plain,(
% 2.10/0.70    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.10/0.70    inference(flattening,[],[f41])).
% 2.10/0.70  fof(f41,plain,(
% 2.10/0.70    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.10/0.70    inference(nnf_transformation,[],[f26])).
% 2.10/0.70  fof(f26,plain,(
% 2.10/0.70    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.10/0.70    inference(flattening,[],[f25])).
% 2.10/0.70  fof(f25,plain,(
% 2.10/0.70    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.10/0.70    inference(ennf_transformation,[],[f23])).
% 2.10/0.70  fof(f23,negated_conjecture,(
% 2.10/0.70    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.10/0.70    inference(negated_conjecture,[],[f22])).
% 2.10/0.70  fof(f22,conjecture,(
% 2.10/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 2.10/0.70  fof(f51,plain,(
% 2.10/0.70    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.10/0.70    inference(cnf_transformation,[],[f45])).
% 2.10/0.70  fof(f49,plain,(
% 2.10/0.70    v2_pre_topc(sK0)),
% 2.10/0.70    inference(cnf_transformation,[],[f45])).
% 2.10/0.70  fof(f50,plain,(
% 2.10/0.70    l1_pre_topc(sK0)),
% 2.10/0.70    inference(cnf_transformation,[],[f45])).
% 2.10/0.70  fof(f1735,plain,(
% 2.10/0.70    sK1 = k2_pre_topc(sK0,sK1)),
% 2.10/0.70    inference(forward_demodulation,[],[f1734,f1541])).
% 2.10/0.70  fof(f1541,plain,(
% 2.10/0.70    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.10/0.70    inference(backward_demodulation,[],[f81,f1530])).
% 2.10/0.70  fof(f1530,plain,(
% 2.10/0.70    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 2.10/0.70    inference(superposition,[],[f1523,f63])).
% 2.10/0.70  fof(f1523,plain,(
% 2.10/0.70    ( ! [X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X1))) )),
% 2.10/0.70    inference(forward_demodulation,[],[f1515,f1497])).
% 2.10/0.70  fof(f1497,plain,(
% 2.10/0.70    k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 2.10/0.70    inference(forward_demodulation,[],[f1487,f623])).
% 2.10/0.70  fof(f623,plain,(
% 2.10/0.70    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.10/0.70    inference(forward_demodulation,[],[f622,f81])).
% 2.10/0.70  fof(f622,plain,(
% 2.10/0.70    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)))),
% 2.10/0.70    inference(forward_demodulation,[],[f619,f521])).
% 2.10/0.70  fof(f521,plain,(
% 2.10/0.70    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))),
% 2.10/0.70    inference(backward_demodulation,[],[f491,f497])).
% 2.10/0.70  fof(f497,plain,(
% 2.10/0.70    k5_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.10/0.70    inference(backward_demodulation,[],[f496,f491])).
% 2.10/0.70  fof(f496,plain,(
% 2.10/0.70    k5_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)))),
% 2.10/0.70    inference(backward_demodulation,[],[f486,f495])).
% 2.10/0.70  fof(f495,plain,(
% 2.10/0.70    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)) = k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))))),
% 2.10/0.70    inference(forward_demodulation,[],[f492,f63])).
% 2.10/0.70  fof(f492,plain,(
% 2.10/0.70    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)) = k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k1_xboole_0))),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f487,f85])).
% 2.10/0.70  fof(f487,plain,(
% 2.10/0.70    r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k1_xboole_0)),
% 2.10/0.70    inference(superposition,[],[f83,f481])).
% 2.10/0.70  fof(f481,plain,(
% 2.10/0.70    k5_xboole_0(sK1,sK1) = k1_setfam_1(k2_tarski(k1_xboole_0,sK1))),
% 2.10/0.70    inference(forward_demodulation,[],[f477,f63])).
% 2.10/0.70  fof(f477,plain,(
% 2.10/0.70    k5_xboole_0(sK1,sK1) = k1_setfam_1(k2_tarski(sK1,k1_xboole_0))),
% 2.10/0.70    inference(superposition,[],[f356,f427])).
% 2.10/0.70  fof(f427,plain,(
% 2.10/0.70    sK1 = k7_subset_1(sK1,sK1,k1_xboole_0)),
% 2.10/0.70    inference(superposition,[],[f348,f221])).
% 2.10/0.70  fof(f486,plain,(
% 2.10/0.70    k5_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)))))),
% 2.10/0.70    inference(superposition,[],[f84,f481])).
% 2.10/0.70  fof(f491,plain,(
% 2.10/0.70    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f54,f487,f74])).
% 2.10/0.70  fof(f74,plain,(
% 2.10/0.70    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f47])).
% 2.10/0.70  fof(f47,plain,(
% 2.10/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.10/0.70    inference(flattening,[],[f46])).
% 2.10/0.70  fof(f46,plain,(
% 2.10/0.70    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.10/0.70    inference(nnf_transformation,[],[f2])).
% 2.10/0.70  fof(f2,axiom,(
% 2.10/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.10/0.70  fof(f54,plain,(
% 2.10/0.70    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f5])).
% 2.10/0.70  fof(f5,axiom,(
% 2.10/0.70    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.10/0.70  fof(f619,plain,(
% 2.10/0.70    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)))))),
% 2.10/0.70    inference(superposition,[],[f84,f520])).
% 2.10/0.70  fof(f520,plain,(
% 2.10/0.70    k1_setfam_1(k2_tarski(k1_xboole_0,sK1)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.10/0.70    inference(backward_demodulation,[],[f481,f497])).
% 2.10/0.70  fof(f1487,plain,(
% 2.10/0.70    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k7_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 2.10/0.70    inference(superposition,[],[f535,f82])).
% 2.10/0.70  fof(f82,plain,(
% 2.10/0.70    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 2.10/0.70    inference(definition_unfolding,[],[f61,f64])).
% 2.10/0.70  fof(f61,plain,(
% 2.10/0.70    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.10/0.70    inference(cnf_transformation,[],[f24])).
% 2.10/0.70  fof(f24,plain,(
% 2.10/0.70    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.10/0.70    inference(rectify,[],[f1])).
% 2.10/0.70  fof(f1,axiom,(
% 2.10/0.70    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.10/0.70  fof(f535,plain,(
% 2.10/0.70    ( ! [X0] : (k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) )),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f525,f87])).
% 2.10/0.70  fof(f525,plain,(
% 2.10/0.70    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 2.10/0.70    inference(forward_demodulation,[],[f524,f521])).
% 2.10/0.70  fof(f524,plain,(
% 2.10/0.70    m1_subset_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))),
% 2.10/0.70    inference(forward_demodulation,[],[f489,f497])).
% 2.10/0.70  fof(f489,plain,(
% 2.10/0.70    m1_subset_1(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k1_zfmisc_1(k1_xboole_0))),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f487,f76])).
% 2.10/0.70  fof(f1515,plain,(
% 2.10/0.70    ( ! [X1] : (k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k7_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) )),
% 2.10/0.70    inference(backward_demodulation,[],[f1499,f1503])).
% 2.10/0.70  fof(f1503,plain,(
% 2.10/0.70    ( ! [X0] : (k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X0)) )),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f54,f1492,f74])).
% 2.10/0.70  fof(f1492,plain,(
% 2.10/0.70    ( ! [X1] : (r1_tarski(k7_subset_1(k1_xboole_0,k1_xboole_0,X1),k1_xboole_0)) )),
% 2.10/0.70    inference(superposition,[],[f83,f535])).
% 2.10/0.70  fof(f1499,plain,(
% 2.10/0.70    ( ! [X1] : (k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k7_subset_1(k1_xboole_0,k1_xboole_0,k7_subset_1(k1_xboole_0,k1_xboole_0,X1))) )),
% 2.10/0.70    inference(forward_demodulation,[],[f1489,f535])).
% 2.10/0.70  fof(f1489,plain,(
% 2.10/0.70    ( ! [X1] : (k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k7_subset_1(k1_xboole_0,k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1))))) )),
% 2.10/0.70    inference(superposition,[],[f535,f84])).
% 2.10/0.70  fof(f1734,plain,(
% 2.10/0.70    k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0)),
% 2.10/0.70    inference(backward_demodulation,[],[f1112,f1733])).
% 2.10/0.70  fof(f1733,plain,(
% 2.10/0.70    k1_xboole_0 = k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)),
% 2.10/0.70    inference(forward_demodulation,[],[f1727,f1564])).
% 2.10/0.70  fof(f1564,plain,(
% 2.10/0.70    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.10/0.70    inference(forward_demodulation,[],[f1563,f82])).
% 2.10/0.70  fof(f1563,plain,(
% 2.10/0.70    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0)))) )),
% 2.10/0.70    inference(forward_demodulation,[],[f1557,f1541])).
% 2.10/0.70  fof(f1557,plain,(
% 2.10/0.70    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_xboole_0))))) )),
% 2.10/0.70    inference(superposition,[],[f84,f1530])).
% 2.10/0.70  fof(f1727,plain,(
% 2.10/0.70    k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)),
% 2.10/0.70    inference(superposition,[],[f1101,f1078])).
% 2.10/0.70  fof(f1078,plain,(
% 2.10/0.70    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 2.10/0.70    inference(backward_demodulation,[],[f479,f1075])).
% 2.10/0.70  fof(f1075,plain,(
% 2.10/0.70    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.10/0.70    inference(subsumption_resolution,[],[f1073,f1074])).
% 2.10/0.70  fof(f1073,plain,(
% 2.10/0.70    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.10/0.70    inference(backward_demodulation,[],[f367,f1070])).
% 2.10/0.70  fof(f367,plain,(
% 2.10/0.70    v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 2.10/0.70    inference(backward_demodulation,[],[f52,f348])).
% 2.10/0.70  fof(f52,plain,(
% 2.10/0.70    v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.10/0.70    inference(cnf_transformation,[],[f45])).
% 2.10/0.70  fof(f1101,plain,(
% 2.10/0.70    ( ! [X0] : (k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1)))) = k7_subset_1(sK1,k2_tops_1(sK0,sK1),X0)) )),
% 2.10/0.70    inference(backward_demodulation,[],[f830,f1099])).
% 2.10/0.70  fof(f1099,plain,(
% 2.10/0.70    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k7_subset_1(sK1,k2_tops_1(sK0,sK1),X0)) )),
% 2.10/0.70    inference(backward_demodulation,[],[f129,f1085])).
% 2.10/0.70  fof(f1085,plain,(
% 2.10/0.70    ( ! [X0] : (k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X0))) = k7_subset_1(sK1,k2_tops_1(sK0,sK1),X0)) )),
% 2.10/0.70    inference(backward_demodulation,[],[f802,f1075])).
% 2.10/0.70  fof(f802,plain,(
% 2.10/0.70    ( ! [X0] : (k7_subset_1(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),X0) = k5_xboole_0(k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),k1_setfam_1(k2_tarski(k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),X0)))) )),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f785,f87])).
% 2.10/0.70  fof(f785,plain,(
% 2.10/0.70    m1_subset_1(k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f784,f76])).
% 2.10/0.70  fof(f784,plain,(
% 2.10/0.70    r1_tarski(k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1)),
% 2.10/0.70    inference(superposition,[],[f83,f250])).
% 2.10/0.70  fof(f129,plain,(
% 2.10/0.70    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X0)))) )),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f97,f87])).
% 2.10/0.70  fof(f97,plain,(
% 2.10/0.70    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f50,f51,f71])).
% 2.10/0.70  fof(f71,plain,(
% 2.10/0.70    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.10/0.70    inference(cnf_transformation,[],[f37])).
% 2.10/0.70  fof(f37,plain,(
% 2.10/0.70    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.10/0.70    inference(flattening,[],[f36])).
% 2.10/0.70  fof(f36,plain,(
% 2.10/0.70    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.10/0.70    inference(ennf_transformation,[],[f18])).
% 2.10/0.70  fof(f18,axiom,(
% 2.10/0.70    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.10/0.70  fof(f830,plain,(
% 2.10/0.70    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1))))) )),
% 2.10/0.70    inference(superposition,[],[f129,f63])).
% 2.10/0.70  fof(f1112,plain,(
% 2.10/0.70    k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1))),
% 2.10/0.70    inference(backward_demodulation,[],[f140,f1099])).
% 2.10/0.70  fof(f140,plain,(
% 2.10/0.70    k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1))),
% 2.10/0.70    inference(forward_demodulation,[],[f139,f98])).
% 2.10/0.70  fof(f98,plain,(
% 2.10/0.70    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f50,f51,f57])).
% 2.10/0.70  fof(f57,plain,(
% 2.10/0.70    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.10/0.70    inference(cnf_transformation,[],[f28])).
% 2.10/0.70  fof(f28,plain,(
% 2.10/0.70    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.70    inference(ennf_transformation,[],[f19])).
% 2.10/0.70  fof(f19,axiom,(
% 2.10/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.10/0.70  fof(f139,plain,(
% 2.10/0.70    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1))),
% 2.10/0.70    inference(forward_demodulation,[],[f127,f129])).
% 2.10/0.70  fof(f127,plain,(
% 2.10/0.70    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))))),
% 2.10/0.70    inference(unit_resulting_resolution,[],[f51,f97,f88])).
% 2.10/0.70  fof(f88,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.70    inference(definition_unfolding,[],[f78,f80])).
% 2.10/0.70  fof(f80,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 2.10/0.70    inference(definition_unfolding,[],[f65,f79])).
% 2.10/0.70  fof(f65,plain,(
% 2.10/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.10/0.70    inference(cnf_transformation,[],[f9])).
% 2.10/0.70  fof(f9,axiom,(
% 2.10/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.10/0.70  fof(f78,plain,(
% 2.10/0.70    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.70    inference(cnf_transformation,[],[f40])).
% 2.10/0.70  fof(f40,plain,(
% 2.10/0.70    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.70    inference(flattening,[],[f39])).
% 2.10/0.70  fof(f39,plain,(
% 2.10/0.70    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.10/0.70    inference(ennf_transformation,[],[f13])).
% 2.10/0.70  fof(f13,axiom,(
% 2.10/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.10/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.10/0.70  % SZS output end Proof for theBenchmark
% 2.10/0.70  % (31085)------------------------------
% 2.10/0.70  % (31085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.70  % (31085)Termination reason: Refutation
% 2.10/0.70  
% 2.10/0.70  % (31085)Memory used [KB]: 7291
% 2.10/0.70  % (31085)Time elapsed: 0.261 s
% 2.10/0.70  % (31085)------------------------------
% 2.10/0.70  % (31085)------------------------------
% 2.10/0.70  % (31073)Success in time 0.324 s
%------------------------------------------------------------------------------
