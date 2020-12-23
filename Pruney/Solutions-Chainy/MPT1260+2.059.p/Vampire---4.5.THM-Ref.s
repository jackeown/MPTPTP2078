%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:43 EST 2020

% Result     : Theorem 7.93s
% Output     : Refutation 8.33s
% Verified   : 
% Statistics : Number of formulae       :  198 (21334 expanded)
%              Number of leaves         :   21 (5980 expanded)
%              Depth                    :   31
%              Number of atoms          :  394 (42707 expanded)
%              Number of equality atoms :  123 (17071 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8932,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f8900])).

fof(f8900,plain,(
    k5_xboole_0(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(backward_demodulation,[],[f8637,f8701])).

fof(f8701,plain,(
    sK1 = k3_subset_1(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f8295,f8700])).

fof(f8700,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f8300,f1390])).

fof(f1390,plain,(
    ! [X0] : k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f116,f488])).

fof(f488,plain,(
    ! [X0,X1] :
      ( k7_subset_1(X1,X0,k1_xboole_0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(forward_demodulation,[],[f463,f106])).

fof(f106,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f87,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f48,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f87,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f49,f85])).

fof(f85,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f61,f60])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f463,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_xboole_0) = k7_subset_1(X1,X0,k1_xboole_0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(superposition,[],[f93,f86])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f70,f85])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f116,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f115,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f115,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(forward_demodulation,[],[f113,f106])).

fof(f113,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[],[f89,f86])).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f58,f85])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f8300,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f2060,f8285])).

fof(f8285,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f8265,f8264])).

fof(f8264,plain,(
    ! [X0] : k1_xboole_0 = k7_subset_1(k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),X0) ),
    inference(unit_resulting_resolution,[],[f254,f8238,f741])).

fof(f741,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK2(X6,X7,X8),X8)
      | k7_subset_1(X6,X6,X7) = X8
      | r2_hidden(sK2(X6,X7,X8),X6) ) ),
    inference(resolution,[],[f480,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f480,plain,(
    ! [X2,X0,X1] :
      ( sP3(sK2(X0,X1,X2),X1,X0)
      | k7_subset_1(X0,X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(backward_demodulation,[],[f95,f457])).

fof(f457,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f116,f93])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( sP3(sK2(X0,X1,X2),X1,X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 ) ),
    inference(definition_unfolding,[],[f76,f85])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sP3(sK2(X0,X1,X2),X1,X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f8238,plain,(
    ! [X3] : ~ r2_hidden(X3,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(global_subsumption,[],[f6550,f7397,f8229])).

fof(f8229,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_tops_1(sK0,sK1))
      | ~ r2_hidden(X3,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) ) ),
    inference(resolution,[],[f2058,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f2058,plain,(
    ! [X12] :
      ( sP3(X12,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1)
      | ~ r2_hidden(X12,k1_tops_1(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f1837,f2044])).

fof(f2044,plain,(
    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2043,f678])).

fof(f678,plain,(
    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) ),
    inference(superposition,[],[f653,f90])).

fof(f90,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f59,f60,f60])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f653,plain,(
    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)) ),
    inference(unit_resulting_resolution,[],[f652,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f60])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f652,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f476,f645])).

fof(f645,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f47,f45,f632])).

fof(f632,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f50,f485])).

fof(f485,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(backward_demodulation,[],[f462,f457])).

fof(f462,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f45,f93])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f476,plain,(
    ! [X0,X1] : r1_tarski(k7_subset_1(X0,X0,X1),X0) ),
    inference(backward_demodulation,[],[f89,f457])).

fof(f2043,plain,(
    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f1953,f90])).

fof(f1953,plain,(
    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1))) ),
    inference(unit_resulting_resolution,[],[f654,f337])).

fof(f337,plain,(
    ! [X4,X5] :
      ( k3_subset_1(X4,X5) = k5_xboole_0(X4,k1_setfam_1(k2_tarski(X5,X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4)) ) ),
    inference(superposition,[],[f92,f90])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f64,f85])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f654,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f652,f68])).

fof(f1837,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,k1_tops_1(sK0,sK1))
      | sP3(X12,k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) ) ),
    inference(global_subsumption,[],[f658,f1829])).

fof(f1829,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,k1_tops_1(sK0,sK1))
      | sP3(X12,k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1)
      | ~ m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) ) ),
    inference(superposition,[],[f344,f657])).

fof(f657,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f654,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f344,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k3_subset_1(X3,X4))
      | sP3(X5,X4,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f102,f92])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | sP3(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f75,f85])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f658,plain,(
    m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f654,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f7397,plain,(
    ! [X23] :
      ( ~ r2_hidden(X23,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))
      | r2_hidden(X23,sK1) ) ),
    inference(resolution,[],[f1231,f1041])).

fof(f1041,plain,(
    r1_tarski(k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1) ),
    inference(superposition,[],[f120,f653])).

fof(f120,plain,(
    ! [X2,X3] : r1_tarski(k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2))),X2) ),
    inference(superposition,[],[f89,f90])).

fof(f1231,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f193,f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f193,plain,(
    ! [X6,X4,X5] :
      ( sP5(X6,X5,X4)
      | ~ r2_hidden(X6,X4)
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f104,f91])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1)))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f82,f60])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f6550,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_tops_1(sK0,sK1))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f6545])).

fof(f6545,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,k1_tops_1(sK0,sK1))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f6538,f797])).

fof(f797,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_tops_1(sK0,sK1))
      | r2_hidden(X0,k1_tops_1(sK0,sK1))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f650,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f650,plain,(
    ! [X1] :
      ( ~ sP3(X1,k2_tops_1(sK0,sK1),sK1)
      | r2_hidden(X1,k1_tops_1(sK0,sK1)) ) ),
    inference(superposition,[],[f482,f645])).

fof(f482,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k7_subset_1(X0,X0,X1))
      | ~ sP3(X3,X1,X0) ) ),
    inference(backward_demodulation,[],[f103,f457])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | ~ sP3(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f74,f85])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f6538,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_tops_1(sK0,sK1))
      | ~ r2_hidden(X2,sK1) ) ),
    inference(resolution,[],[f6518,f73])).

% (27564)Time limit reached!
% (27564)------------------------------
% (27564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27564)Termination reason: Time limit

% (27564)Memory used [KB]: 21108
% (27564)Time elapsed: 1.008 s
% (27564)------------------------------
% (27564)------------------------------
fof(f6518,plain,(
    ! [X3] :
      ( sP3(X3,sK1,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X3,k2_tops_1(sK0,sK1)) ) ),
    inference(global_subsumption,[],[f2363,f6435])).

fof(f6435,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f44,f6385])).

fof(f6385,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f775,f6375])).

fof(f6375,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f6372,f602])).

fof(f602,plain,
    ( v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f47,f45,f598])).

fof(f598,plain,
    ( v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f56,f347])).

fof(f347,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(forward_demodulation,[],[f346,f132])).

fof(f132,plain,(
    sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f108,f91])).

fof(f108,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f45,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f346,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f333,f90])).

fof(f333,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))) ),
    inference(unit_resulting_resolution,[],[f45,f92])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(f6372,plain,
    ( ~ v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f6362,f360])).

fof(f360,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f225,f347])).

fof(f225,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f45,f65])).

fof(f6362,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f2014,f2010])).

fof(f2010,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(backward_demodulation,[],[f828,f2007])).

fof(f2007,plain,(
    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2006,f1073])).

fof(f1073,plain,(
    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f893,f137])).

fof(f137,plain,(
    ! [X4,X5] :
      ( k1_setfam_1(k2_tarski(X5,X4)) = X4
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f91,f90])).

fof(f893,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f826,f69])).

fof(f826,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f534,f823])).

fof(f823,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f811,f347])).

fof(f811,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(unit_resulting_resolution,[],[f47,f45,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f534,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f368,f63])).

fof(f368,plain,(
    m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f312,f347])).

fof(f312,plain,(
    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f47,f155,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f155,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f45,f63])).

fof(f2006,plain,(
    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f1954,f90])).

fof(f1954,plain,(
    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f826,f337])).

fof(f828,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(backward_demodulation,[],[f436,f825])).

fof(f825,plain,(
    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f533,f823])).

fof(f533,plain,(
    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))) ),
    inference(unit_resulting_resolution,[],[f368,f65])).

fof(f436,plain,
    ( ~ v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | k5_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(global_subsumption,[],[f47,f429])).

fof(f429,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | k5_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f54,f348])).

fof(f348,plain,(
    m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f155,f347])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
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

fof(f2014,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f838,f2007])).

fof(f838,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f823,f825])).

fof(f775,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f45,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f44,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f2363,plain,(
    ! [X2] :
      ( sP3(X2,sK1,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X2,k2_tops_1(sK0,sK1))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(global_subsumption,[],[f314,f2340])).

fof(f2340,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_tops_1(sK0,sK1))
      | sP3(X2,sK1,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(superposition,[],[f474,f43])).

fof(f43,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f474,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ r2_hidden(X10,k7_subset_1(X9,X7,X8))
      | sP3(X10,X8,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X9)) ) ),
    inference(superposition,[],[f102,f93])).

fof(f314,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f47,f45,f67])).

fof(f254,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_subsumption,[],[f218,f252])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f250,f73])).

fof(f250,plain,(
    ! [X0,X1] :
      ( sP3(X1,k1_xboole_0,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(forward_demodulation,[],[f241,f106])).

fof(f241,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,k1_xboole_0))
      | sP3(X1,k1_xboole_0,X0) ) ),
    inference(superposition,[],[f102,f86])).

fof(f218,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f191,f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f191,plain,(
    ! [X0,X1] :
      ( sP5(X1,k1_xboole_0,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f104,f86])).

fof(f8265,plain,(
    ! [X0] : k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k7_subset_1(k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),X0) ),
    inference(unit_resulting_resolution,[],[f8238,f8238,f741])).

fof(f2060,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f1054,f2046])).

fof(f2046,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f657,f2044])).

fof(f1054,plain,(
    k3_subset_1(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f1050,f477])).

fof(f477,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(backward_demodulation,[],[f92,f457])).

fof(f1050,plain,(
    m1_subset_1(k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1041,f68])).

fof(f8295,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f2046,f8285])).

fof(f8637,plain,(
    k5_xboole_0(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k3_subset_1(sK1,k1_xboole_0)) ),
    inference(global_subsumption,[],[f6441,f8513])).

fof(f8513,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k3_subset_1(sK1,k1_xboole_0))
    | v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(backward_demodulation,[],[f5384,f8295])).

fof(f5384,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(global_subsumption,[],[f47,f46,f348,f5377])).

fof(f5377,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f53,f2008])).

fof(f2008,plain,(
    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f825,f2007])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f6441,plain,(
    ~ v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f6440,f347])).

fof(f6440,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f47,f45,f6435,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (27571)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.49  % (27563)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (27572)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (27568)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (27564)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.52  % (27570)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.25/0.53  % (27585)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.25/0.53  % (27577)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.25/0.53  % (27576)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.54  % (27582)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.54  % (27569)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.54  % (27562)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.55  % (27588)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.55  % (27583)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.56  % (27565)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.56  % (27579)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.56  % (27584)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.56  % (27591)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.56  % (27579)Refutation not found, incomplete strategy% (27579)------------------------------
% 1.38/0.56  % (27579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (27579)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (27579)Memory used [KB]: 10618
% 1.38/0.56  % (27579)Time elapsed: 0.148 s
% 1.38/0.56  % (27579)------------------------------
% 1.38/0.56  % (27579)------------------------------
% 1.38/0.56  % (27575)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.56  % (27580)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.56  % (27566)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.38/0.57  % (27589)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.57  % (27567)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.38/0.57  % (27586)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.57  % (27590)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.57  % (27584)Refutation not found, incomplete strategy% (27584)------------------------------
% 1.38/0.57  % (27584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (27584)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (27584)Memory used [KB]: 10746
% 1.38/0.57  % (27584)Time elapsed: 0.128 s
% 1.38/0.57  % (27584)------------------------------
% 1.38/0.57  % (27584)------------------------------
% 1.38/0.57  % (27581)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.58  % (27573)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.58  % (27578)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.58  % (27574)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.58  % (27587)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.53/0.73  % (27592)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.53/0.75  % (27593)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.60/0.84  % (27567)Time limit reached!
% 3.60/0.84  % (27567)------------------------------
% 3.60/0.84  % (27567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.60/0.84  % (27567)Termination reason: Time limit
% 3.60/0.84  
% 3.60/0.84  % (27567)Memory used [KB]: 7931
% 3.60/0.84  % (27567)Time elapsed: 0.400 s
% 3.60/0.84  % (27567)------------------------------
% 3.60/0.84  % (27567)------------------------------
% 3.60/0.91  % (27574)Time limit reached!
% 3.60/0.91  % (27574)------------------------------
% 3.60/0.91  % (27574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.60/0.92  % (27563)Time limit reached!
% 3.60/0.92  % (27563)------------------------------
% 3.60/0.92  % (27563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.60/0.92  % (27563)Termination reason: Time limit
% 3.60/0.92  
% 3.60/0.92  % (27563)Memory used [KB]: 7419
% 3.60/0.92  % (27563)Time elapsed: 0.506 s
% 3.60/0.92  % (27563)------------------------------
% 3.60/0.92  % (27563)------------------------------
% 3.60/0.92  % (27574)Termination reason: Time limit
% 3.60/0.92  
% 3.60/0.92  % (27574)Memory used [KB]: 8571
% 3.60/0.92  % (27574)Time elapsed: 0.510 s
% 3.60/0.92  % (27574)------------------------------
% 3.60/0.92  % (27574)------------------------------
% 4.28/0.93  % (27562)Time limit reached!
% 4.28/0.93  % (27562)------------------------------
% 4.28/0.93  % (27562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/0.93  % (27562)Termination reason: Time limit
% 4.28/0.93  % (27562)Termination phase: Saturation
% 4.28/0.93  
% 4.28/0.93  % (27562)Memory used [KB]: 5373
% 4.28/0.93  % (27562)Time elapsed: 0.500 s
% 4.28/0.93  % (27562)------------------------------
% 4.28/0.93  % (27562)------------------------------
% 4.28/0.93  % (27572)Time limit reached!
% 4.28/0.93  % (27572)------------------------------
% 4.28/0.93  % (27572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/0.93  % (27572)Termination reason: Time limit
% 4.28/0.93  
% 4.28/0.93  % (27572)Memory used [KB]: 12792
% 4.28/0.93  % (27572)Time elapsed: 0.520 s
% 4.28/0.93  % (27572)------------------------------
% 4.28/0.93  % (27572)------------------------------
% 4.68/0.99  % (27594)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.68/1.00  % (27590)Time limit reached!
% 4.68/1.00  % (27590)------------------------------
% 4.68/1.00  % (27590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.68/1.00  % (27590)Termination reason: Time limit
% 4.68/1.00  % (27590)Termination phase: Saturation
% 4.68/1.00  
% 4.68/1.00  % (27590)Memory used [KB]: 8187
% 4.68/1.00  % (27590)Time elapsed: 0.600 s
% 4.68/1.00  % (27590)------------------------------
% 4.68/1.00  % (27590)------------------------------
% 4.68/1.02  % (27569)Time limit reached!
% 4.68/1.02  % (27569)------------------------------
% 4.68/1.02  % (27569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.68/1.03  % (27597)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.68/1.04  % (27569)Termination reason: Time limit
% 4.68/1.04  
% 4.68/1.04  % (27569)Memory used [KB]: 11897
% 4.68/1.04  % (27569)Time elapsed: 0.612 s
% 4.68/1.04  % (27569)------------------------------
% 4.68/1.04  % (27569)------------------------------
% 4.68/1.04  % (27578)Time limit reached!
% 4.68/1.04  % (27578)------------------------------
% 4.68/1.04  % (27578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.68/1.04  % (27578)Termination reason: Time limit
% 4.68/1.04  
% 4.68/1.04  % (27578)Memory used [KB]: 15479
% 4.68/1.04  % (27578)Time elapsed: 0.611 s
% 4.68/1.04  % (27578)------------------------------
% 4.68/1.04  % (27578)------------------------------
% 5.16/1.07  % (27596)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.16/1.07  % (27598)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.67/1.09  % (27595)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 6.19/1.15  % (27600)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.19/1.17  % (27599)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.19/1.18  % (27601)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.84/1.23  % (27583)Time limit reached!
% 6.84/1.23  % (27583)------------------------------
% 6.84/1.23  % (27583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.84/1.23  % (27583)Termination reason: Time limit
% 6.84/1.23  
% 6.84/1.23  % (27583)Memory used [KB]: 5373
% 6.84/1.23  % (27583)Time elapsed: 0.806 s
% 6.84/1.23  % (27583)------------------------------
% 6.84/1.23  % (27583)------------------------------
% 7.77/1.37  % (27602)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 7.93/1.37  % (27595)Time limit reached!
% 7.93/1.37  % (27595)------------------------------
% 7.93/1.37  % (27595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.93/1.37  % (27595)Termination reason: Time limit
% 7.93/1.37  
% 7.93/1.37  % (27595)Memory used [KB]: 6652
% 7.93/1.37  % (27595)Time elapsed: 0.418 s
% 7.93/1.37  % (27595)------------------------------
% 7.93/1.37  % (27595)------------------------------
% 7.93/1.39  % (27596)Time limit reached!
% 7.93/1.39  % (27596)------------------------------
% 7.93/1.39  % (27596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.93/1.39  % (27586)Refutation found. Thanks to Tanya!
% 7.93/1.39  % SZS status Theorem for theBenchmark
% 7.93/1.39  % (27596)Termination reason: Time limit
% 7.93/1.39  
% 7.93/1.39  % (27596)Memory used [KB]: 13560
% 7.93/1.39  % (27596)Time elapsed: 0.424 s
% 7.93/1.39  % (27596)------------------------------
% 7.93/1.39  % (27596)------------------------------
% 7.93/1.40  % SZS output start Proof for theBenchmark
% 7.93/1.40  fof(f8932,plain,(
% 7.93/1.40    $false),
% 7.93/1.40    inference(trivial_inequality_removal,[],[f8900])).
% 7.93/1.40  fof(f8900,plain,(
% 7.93/1.40    k5_xboole_0(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),sK1)),
% 7.93/1.40    inference(backward_demodulation,[],[f8637,f8701])).
% 7.93/1.40  fof(f8701,plain,(
% 7.93/1.40    sK1 = k3_subset_1(sK1,k1_xboole_0)),
% 7.93/1.40    inference(backward_demodulation,[],[f8295,f8700])).
% 7.93/1.40  fof(f8700,plain,(
% 7.93/1.40    sK1 = k1_tops_1(sK0,sK1)),
% 7.93/1.40    inference(forward_demodulation,[],[f8300,f1390])).
% 7.93/1.40  fof(f1390,plain,(
% 7.93/1.40    ( ! [X0] : (k7_subset_1(X0,X0,k1_xboole_0) = X0) )),
% 7.93/1.40    inference(unit_resulting_resolution,[],[f116,f488])).
% 7.93/1.40  fof(f488,plain,(
% 7.93/1.40    ( ! [X0,X1] : (k7_subset_1(X1,X0,k1_xboole_0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.93/1.40    inference(forward_demodulation,[],[f463,f106])).
% 7.93/1.40  fof(f106,plain,(
% 7.93/1.40    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.93/1.40    inference(forward_demodulation,[],[f87,f86])).
% 7.93/1.40  fof(f86,plain,(
% 7.93/1.40    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 7.93/1.40    inference(definition_unfolding,[],[f48,f60])).
% 7.93/1.40  fof(f60,plain,(
% 7.93/1.40    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.93/1.40    inference(cnf_transformation,[],[f14])).
% 7.93/1.40  fof(f14,axiom,(
% 7.93/1.40    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.93/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 7.93/1.40  fof(f48,plain,(
% 7.93/1.40    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 7.93/1.40    inference(cnf_transformation,[],[f7])).
% 7.93/1.40  fof(f7,axiom,(
% 7.93/1.40    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 7.93/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 7.93/1.40  fof(f87,plain,(
% 7.93/1.40    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 7.93/1.40    inference(definition_unfolding,[],[f49,f85])).
% 7.93/1.40  fof(f85,plain,(
% 7.93/1.40    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 7.93/1.40    inference(definition_unfolding,[],[f61,f60])).
% 7.93/1.40  fof(f61,plain,(
% 7.93/1.40    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.93/1.40    inference(cnf_transformation,[],[f5])).
% 7.93/1.40  fof(f5,axiom,(
% 7.93/1.40    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.93/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 7.93/1.40  fof(f49,plain,(
% 7.93/1.40    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.93/1.40    inference(cnf_transformation,[],[f9])).
% 7.93/1.40  fof(f9,axiom,(
% 7.93/1.40    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.93/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 7.93/1.40  fof(f463,plain,(
% 7.93/1.40    ( ! [X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k7_subset_1(X1,X0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.93/1.40    inference(superposition,[],[f93,f86])).
% 7.93/1.40  fof(f93,plain,(
% 7.93/1.40    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.93/1.40    inference(definition_unfolding,[],[f70,f85])).
% 7.93/1.40  fof(f70,plain,(
% 7.93/1.40    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 7.93/1.40    inference(cnf_transformation,[],[f42])).
% 7.93/1.40  fof(f42,plain,(
% 7.93/1.40    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.93/1.40    inference(ennf_transformation,[],[f13])).
% 7.93/1.40  fof(f13,axiom,(
% 7.93/1.40    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 7.93/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 7.93/1.40  fof(f116,plain,(
% 7.93/1.40    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 7.93/1.40    inference(unit_resulting_resolution,[],[f115,f68])).
% 7.93/1.40  fof(f68,plain,(
% 7.93/1.40    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.93/1.40    inference(cnf_transformation,[],[f15])).
% 7.93/1.40  fof(f15,axiom,(
% 7.93/1.40    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.93/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 7.93/1.40  fof(f115,plain,(
% 7.93/1.40    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 7.93/1.40    inference(forward_demodulation,[],[f113,f106])).
% 7.93/1.40  fof(f113,plain,(
% 7.93/1.40    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0)) )),
% 7.93/1.40    inference(superposition,[],[f89,f86])).
% 7.93/1.40  fof(f89,plain,(
% 7.93/1.40    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 7.93/1.40    inference(definition_unfolding,[],[f58,f85])).
% 7.93/1.40  fof(f58,plain,(
% 7.93/1.40    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.93/1.40    inference(cnf_transformation,[],[f8])).
% 7.93/1.40  fof(f8,axiom,(
% 7.93/1.40    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.93/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 7.93/1.40  fof(f8300,plain,(
% 7.93/1.40    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_xboole_0)),
% 7.93/1.40    inference(backward_demodulation,[],[f2060,f8285])).
% 7.93/1.40  fof(f8285,plain,(
% 7.93/1.40    k1_xboole_0 = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 7.93/1.40    inference(backward_demodulation,[],[f8265,f8264])).
% 7.93/1.40  fof(f8264,plain,(
% 7.93/1.40    ( ! [X0] : (k1_xboole_0 = k7_subset_1(k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),X0)) )),
% 7.93/1.40    inference(unit_resulting_resolution,[],[f254,f8238,f741])).
% 7.93/1.40  fof(f741,plain,(
% 7.93/1.40    ( ! [X6,X8,X7] : (r2_hidden(sK2(X6,X7,X8),X8) | k7_subset_1(X6,X6,X7) = X8 | r2_hidden(sK2(X6,X7,X8),X6)) )),
% 7.93/1.40    inference(resolution,[],[f480,f72])).
% 7.93/1.40  fof(f72,plain,(
% 7.93/1.40    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 7.93/1.40    inference(cnf_transformation,[],[f3])).
% 7.93/1.40  fof(f3,axiom,(
% 7.93/1.40    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.93/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 7.93/1.40  fof(f480,plain,(
% 7.93/1.40    ( ! [X2,X0,X1] : (sP3(sK2(X0,X1,X2),X1,X0) | k7_subset_1(X0,X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.93/1.40    inference(backward_demodulation,[],[f95,f457])).
% 7.93/1.40  fof(f457,plain,(
% 7.93/1.40    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1)) )),
% 7.93/1.40    inference(unit_resulting_resolution,[],[f116,f93])).
% 7.93/1.40  fof(f95,plain,(
% 7.93/1.40    ( ! [X2,X0,X1] : (sP3(sK2(X0,X1,X2),X1,X0) | r2_hidden(sK2(X0,X1,X2),X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2) )),
% 7.93/1.40    inference(definition_unfolding,[],[f76,f85])).
% 7.93/1.40  fof(f76,plain,(
% 7.93/1.40    ( ! [X2,X0,X1] : (sP3(sK2(X0,X1,X2),X1,X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 7.93/1.40    inference(cnf_transformation,[],[f3])).
% 7.93/1.40  fof(f8238,plain,(
% 7.93/1.40    ( ! [X3] : (~r2_hidden(X3,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))) )),
% 7.93/1.40    inference(global_subsumption,[],[f6550,f7397,f8229])).
% 7.93/1.40  fof(f8229,plain,(
% 7.93/1.40    ( ! [X3] : (~r2_hidden(X3,k1_tops_1(sK0,sK1)) | ~r2_hidden(X3,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))) )),
% 7.93/1.40    inference(resolution,[],[f2058,f73])).
% 7.93/1.40  fof(f73,plain,(
% 7.93/1.40    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 7.93/1.40    inference(cnf_transformation,[],[f3])).
% 7.93/1.40  fof(f2058,plain,(
% 7.93/1.40    ( ! [X12] : (sP3(X12,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1) | ~r2_hidden(X12,k1_tops_1(sK0,sK1))) )),
% 7.93/1.40    inference(backward_demodulation,[],[f1837,f2044])).
% 7.93/1.40  fof(f2044,plain,(
% 7.93/1.40    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 7.93/1.40    inference(forward_demodulation,[],[f2043,f678])).
% 7.93/1.40  fof(f678,plain,(
% 7.93/1.40    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))),
% 7.93/1.40    inference(superposition,[],[f653,f90])).
% 7.93/1.40  fof(f90,plain,(
% 7.93/1.40    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 7.93/1.40    inference(definition_unfolding,[],[f59,f60,f60])).
% 7.93/1.40  fof(f59,plain,(
% 7.93/1.40    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.93/1.40    inference(cnf_transformation,[],[f1])).
% 7.93/1.40  fof(f1,axiom,(
% 7.93/1.40    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.93/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 7.93/1.40  fof(f653,plain,(
% 7.93/1.40    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1))),
% 7.93/1.40    inference(unit_resulting_resolution,[],[f652,f91])).
% 7.93/1.40  fof(f91,plain,(
% 7.93/1.40    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.93/1.40    inference(definition_unfolding,[],[f62,f60])).
% 7.93/1.40  fof(f62,plain,(
% 7.93/1.40    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 7.93/1.40    inference(cnf_transformation,[],[f34])).
% 7.93/1.40  fof(f34,plain,(
% 7.93/1.40    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.93/1.40    inference(ennf_transformation,[],[f6])).
% 7.93/1.40  fof(f6,axiom,(
% 7.93/1.40    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.93/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 7.93/1.40  fof(f652,plain,(
% 7.93/1.40    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 7.93/1.40    inference(superposition,[],[f476,f645])).
% 7.93/1.40  fof(f645,plain,(
% 7.93/1.40    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))),
% 7.93/1.40    inference(global_subsumption,[],[f47,f45,f632])).
% 7.93/1.40  fof(f632,plain,(
% 7.93/1.40    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 7.93/1.40    inference(superposition,[],[f50,f485])).
% 7.93/1.40  fof(f485,plain,(
% 7.93/1.40    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)) )),
% 7.93/1.40    inference(backward_demodulation,[],[f462,f457])).
% 7.93/1.40  fof(f462,plain,(
% 7.93/1.40    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) )),
% 7.93/1.40    inference(unit_resulting_resolution,[],[f45,f93])).
% 7.93/1.40  fof(f50,plain,(
% 7.93/1.40    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.93/1.40    inference(cnf_transformation,[],[f28])).
% 7.93/1.40  fof(f28,plain,(
% 7.93/1.40    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.93/1.40    inference(ennf_transformation,[],[f22])).
% 7.93/1.40  fof(f22,axiom,(
% 7.93/1.40    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 7.93/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 7.93/1.40  fof(f45,plain,(
% 7.93/1.40    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.93/1.40    inference(cnf_transformation,[],[f27])).
% 7.93/1.40  fof(f27,plain,(
% 7.93/1.40    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.93/1.40    inference(flattening,[],[f26])).
% 7.93/1.40  fof(f26,plain,(
% 7.93/1.40    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.93/1.40    inference(ennf_transformation,[],[f24])).
% 7.93/1.40  fof(f24,negated_conjecture,(
% 7.93/1.40    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 7.93/1.40    inference(negated_conjecture,[],[f23])).
% 7.93/1.40  fof(f23,conjecture,(
% 7.93/1.40    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 7.93/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 7.93/1.40  fof(f47,plain,(
% 7.93/1.40    l1_pre_topc(sK0)),
% 7.93/1.40    inference(cnf_transformation,[],[f27])).
% 7.93/1.40  fof(f476,plain,(
% 7.93/1.40    ( ! [X0,X1] : (r1_tarski(k7_subset_1(X0,X0,X1),X0)) )),
% 7.93/1.40    inference(backward_demodulation,[],[f89,f457])).
% 7.93/1.40  fof(f2043,plain,(
% 7.93/1.40    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))))),
% 7.93/1.40    inference(forward_demodulation,[],[f1953,f90])).
% 7.93/1.40  fof(f1953,plain,(
% 7.93/1.40    k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)))),
% 7.93/1.40    inference(unit_resulting_resolution,[],[f654,f337])).
% 7.93/1.40  fof(f337,plain,(
% 7.93/1.40    ( ! [X4,X5] : (k3_subset_1(X4,X5) = k5_xboole_0(X4,k1_setfam_1(k2_tarski(X5,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(X4))) )),
% 7.93/1.40    inference(superposition,[],[f92,f90])).
% 7.93/1.40  fof(f92,plain,(
% 7.93/1.40    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.93/1.40    inference(definition_unfolding,[],[f64,f85])).
% 7.93/1.40  fof(f64,plain,(
% 7.93/1.40    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 7.93/1.40    inference(cnf_transformation,[],[f36])).
% 7.93/1.40  fof(f36,plain,(
% 7.93/1.40    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.93/1.40    inference(ennf_transformation,[],[f10])).
% 7.93/1.40  fof(f10,axiom,(
% 7.93/1.40    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.93/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 7.93/1.40  fof(f654,plain,(
% 7.93/1.40    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 7.93/1.40    inference(unit_resulting_resolution,[],[f652,f68])).
% 7.93/1.41  fof(f1837,plain,(
% 7.93/1.41    ( ! [X12] : (~r2_hidden(X12,k1_tops_1(sK0,sK1)) | sP3(X12,k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1)) )),
% 7.93/1.41    inference(global_subsumption,[],[f658,f1829])).
% 7.93/1.41  fof(f1829,plain,(
% 7.93/1.41    ( ! [X12] : (~r2_hidden(X12,k1_tops_1(sK0,sK1)) | sP3(X12,k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) | ~m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))) )),
% 7.93/1.41    inference(superposition,[],[f344,f657])).
% 7.93/1.41  fof(f657,plain,(
% 7.93/1.41    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)))),
% 7.93/1.41    inference(unit_resulting_resolution,[],[f654,f65])).
% 7.93/1.41  fof(f65,plain,(
% 7.93/1.41    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.93/1.41    inference(cnf_transformation,[],[f37])).
% 7.93/1.41  fof(f37,plain,(
% 7.93/1.41    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.93/1.41    inference(ennf_transformation,[],[f12])).
% 7.93/1.41  fof(f12,axiom,(
% 7.93/1.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.93/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 7.93/1.41  fof(f344,plain,(
% 7.93/1.41    ( ! [X4,X5,X3] : (~r2_hidden(X5,k3_subset_1(X3,X4)) | sP3(X5,X4,X3) | ~m1_subset_1(X4,k1_zfmisc_1(X3))) )),
% 7.93/1.41    inference(superposition,[],[f102,f92])).
% 7.93/1.41  fof(f102,plain,(
% 7.93/1.41    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | sP3(X3,X1,X0)) )),
% 7.93/1.41    inference(equality_resolution,[],[f96])).
% 7.93/1.41  fof(f96,plain,(
% 7.93/1.41    ( ! [X2,X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 7.93/1.41    inference(definition_unfolding,[],[f75,f85])).
% 7.93/1.41  fof(f75,plain,(
% 7.93/1.41    ( ! [X2,X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.93/1.41    inference(cnf_transformation,[],[f3])).
% 7.93/1.41  fof(f658,plain,(
% 7.93/1.41    m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))),
% 7.93/1.41    inference(unit_resulting_resolution,[],[f654,f63])).
% 7.93/1.41  fof(f63,plain,(
% 7.93/1.41    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.93/1.41    inference(cnf_transformation,[],[f35])).
% 7.93/1.41  fof(f35,plain,(
% 7.93/1.41    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.93/1.41    inference(ennf_transformation,[],[f11])).
% 7.93/1.41  fof(f11,axiom,(
% 7.93/1.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.93/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 7.93/1.41  fof(f7397,plain,(
% 7.93/1.41    ( ! [X23] : (~r2_hidden(X23,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) | r2_hidden(X23,sK1)) )),
% 7.93/1.41    inference(resolution,[],[f1231,f1041])).
% 7.93/1.41  fof(f1041,plain,(
% 7.93/1.41    r1_tarski(k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1)),
% 7.93/1.41    inference(superposition,[],[f120,f653])).
% 7.93/1.41  fof(f120,plain,(
% 7.93/1.41    ( ! [X2,X3] : (r1_tarski(k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2))),X2)) )),
% 7.93/1.41    inference(superposition,[],[f89,f90])).
% 7.93/1.41  fof(f1231,plain,(
% 7.93/1.41    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 7.93/1.41    inference(resolution,[],[f193,f80])).
% 7.93/1.41  fof(f80,plain,(
% 7.93/1.41    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 7.93/1.41    inference(cnf_transformation,[],[f2])).
% 7.93/1.41  fof(f2,axiom,(
% 7.93/1.41    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.93/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 7.93/1.41  fof(f193,plain,(
% 7.93/1.41    ( ! [X6,X4,X5] : (sP5(X6,X5,X4) | ~r2_hidden(X6,X4) | ~r1_tarski(X4,X5)) )),
% 7.93/1.41    inference(superposition,[],[f104,f91])).
% 7.93/1.41  fof(f104,plain,(
% 7.93/1.41    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1))) | sP5(X3,X1,X0)) )),
% 7.93/1.41    inference(equality_resolution,[],[f100])).
% 7.93/1.41  fof(f100,plain,(
% 7.93/1.41    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 7.93/1.41    inference(definition_unfolding,[],[f82,f60])).
% 7.93/1.41  fof(f82,plain,(
% 7.93/1.41    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 7.93/1.41    inference(cnf_transformation,[],[f2])).
% 7.93/1.41  fof(f6550,plain,(
% 7.93/1.41    ( ! [X0] : (r2_hidden(X0,k1_tops_1(sK0,sK1)) | ~r2_hidden(X0,sK1)) )),
% 7.93/1.41    inference(duplicate_literal_removal,[],[f6545])).
% 7.93/1.41  fof(f6545,plain,(
% 7.93/1.41    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,k1_tops_1(sK0,sK1)) | ~r2_hidden(X0,sK1)) )),
% 7.93/1.41    inference(resolution,[],[f6538,f797])).
% 7.93/1.41  fof(f797,plain,(
% 7.93/1.41    ( ! [X0] : (r2_hidden(X0,k2_tops_1(sK0,sK1)) | r2_hidden(X0,k1_tops_1(sK0,sK1)) | ~r2_hidden(X0,sK1)) )),
% 7.93/1.41    inference(resolution,[],[f650,f71])).
% 7.93/1.41  fof(f71,plain,(
% 7.93/1.41    ( ! [X0,X3,X1] : (sP3(X3,X1,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 7.93/1.41    inference(cnf_transformation,[],[f3])).
% 7.93/1.41  fof(f650,plain,(
% 7.93/1.41    ( ! [X1] : (~sP3(X1,k2_tops_1(sK0,sK1),sK1) | r2_hidden(X1,k1_tops_1(sK0,sK1))) )),
% 7.93/1.41    inference(superposition,[],[f482,f645])).
% 7.93/1.41  fof(f482,plain,(
% 7.93/1.41    ( ! [X0,X3,X1] : (r2_hidden(X3,k7_subset_1(X0,X0,X1)) | ~sP3(X3,X1,X0)) )),
% 7.93/1.41    inference(backward_demodulation,[],[f103,f457])).
% 7.93/1.41  fof(f103,plain,(
% 7.93/1.41    ( ! [X0,X3,X1] : (r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | ~sP3(X3,X1,X0)) )),
% 7.93/1.41    inference(equality_resolution,[],[f97])).
% 7.93/1.41  fof(f97,plain,(
% 7.93/1.41    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 7.93/1.41    inference(definition_unfolding,[],[f74,f85])).
% 7.93/1.41  fof(f74,plain,(
% 7.93/1.41    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.93/1.41    inference(cnf_transformation,[],[f3])).
% 7.93/1.41  fof(f6538,plain,(
% 7.93/1.41    ( ! [X2] : (~r2_hidden(X2,k2_tops_1(sK0,sK1)) | ~r2_hidden(X2,sK1)) )),
% 7.93/1.41    inference(resolution,[],[f6518,f73])).
% 7.93/1.41  % (27564)Time limit reached!
% 7.93/1.41  % (27564)------------------------------
% 7.93/1.41  % (27564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.93/1.41  % (27564)Termination reason: Time limit
% 7.93/1.41  
% 7.93/1.41  % (27564)Memory used [KB]: 21108
% 7.93/1.41  % (27564)Time elapsed: 1.008 s
% 7.93/1.41  % (27564)------------------------------
% 7.93/1.41  % (27564)------------------------------
% 7.93/1.42  fof(f6518,plain,(
% 7.93/1.42    ( ! [X3] : (sP3(X3,sK1,k2_pre_topc(sK0,sK1)) | ~r2_hidden(X3,k2_tops_1(sK0,sK1))) )),
% 7.93/1.42    inference(global_subsumption,[],[f2363,f6435])).
% 7.93/1.42  fof(f6435,plain,(
% 7.93/1.42    ~v3_pre_topc(sK1,sK0)),
% 7.93/1.42    inference(global_subsumption,[],[f44,f6385])).
% 7.93/1.42  fof(f6385,plain,(
% 7.93/1.42    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 7.93/1.42    inference(superposition,[],[f775,f6375])).
% 7.93/1.42  fof(f6375,plain,(
% 7.93/1.42    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 7.93/1.42    inference(resolution,[],[f6372,f602])).
% 7.93/1.42  fof(f602,plain,(
% 7.93/1.42    v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~v3_pre_topc(sK1,sK0)),
% 7.93/1.42    inference(global_subsumption,[],[f47,f45,f598])).
% 7.93/1.42  fof(f598,plain,(
% 7.93/1.42    v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v3_pre_topc(sK1,sK0)),
% 7.93/1.42    inference(superposition,[],[f56,f347])).
% 7.93/1.42  fof(f347,plain,(
% 7.93/1.42    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)),
% 7.93/1.42    inference(forward_demodulation,[],[f346,f132])).
% 7.93/1.42  fof(f132,plain,(
% 7.93/1.42    sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))),
% 7.93/1.42    inference(unit_resulting_resolution,[],[f108,f91])).
% 7.93/1.42  fof(f108,plain,(
% 7.93/1.42    r1_tarski(sK1,u1_struct_0(sK0))),
% 7.93/1.42    inference(unit_resulting_resolution,[],[f45,f69])).
% 7.93/1.42  fof(f69,plain,(
% 7.93/1.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 7.93/1.42    inference(cnf_transformation,[],[f15])).
% 7.93/1.42  fof(f346,plain,(
% 7.93/1.42    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))),
% 7.93/1.42    inference(forward_demodulation,[],[f333,f90])).
% 7.93/1.42  fof(f333,plain,(
% 7.93/1.42    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)))),
% 7.93/1.42    inference(unit_resulting_resolution,[],[f45,f92])).
% 7.93/1.42  fof(f56,plain,(
% 7.93/1.42    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0)) )),
% 7.93/1.42    inference(cnf_transformation,[],[f33])).
% 7.93/1.42  fof(f33,plain,(
% 7.93/1.42    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.93/1.42    inference(ennf_transformation,[],[f21])).
% 7.93/1.42  fof(f21,axiom,(
% 7.93/1.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 7.93/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).
% 7.93/1.42  fof(f6372,plain,(
% 7.93/1.42    ~v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) | sK1 = k1_tops_1(sK0,sK1)),
% 7.93/1.42    inference(forward_demodulation,[],[f6362,f360])).
% 7.93/1.42  fof(f360,plain,(
% 7.93/1.42    sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),
% 7.93/1.42    inference(backward_demodulation,[],[f225,f347])).
% 7.93/1.42  fof(f225,plain,(
% 7.93/1.42    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 7.93/1.42    inference(unit_resulting_resolution,[],[f45,f65])).
% 7.93/1.42  fof(f6362,plain,(
% 7.93/1.42    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | ~v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 7.93/1.42    inference(superposition,[],[f2014,f2010])).
% 7.93/1.42  fof(f2010,plain,(
% 7.93/1.42    k5_xboole_0(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 7.93/1.42    inference(backward_demodulation,[],[f828,f2007])).
% 7.93/1.42  fof(f2007,plain,(
% 7.93/1.42    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 7.93/1.42    inference(forward_demodulation,[],[f2006,f1073])).
% 7.93/1.42  fof(f1073,plain,(
% 7.93/1.42    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 7.93/1.42    inference(unit_resulting_resolution,[],[f893,f137])).
% 7.93/1.42  fof(f137,plain,(
% 7.93/1.42    ( ! [X4,X5] : (k1_setfam_1(k2_tarski(X5,X4)) = X4 | ~r1_tarski(X4,X5)) )),
% 7.93/1.42    inference(superposition,[],[f91,f90])).
% 7.93/1.42  fof(f893,plain,(
% 7.93/1.42    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 7.93/1.42    inference(unit_resulting_resolution,[],[f826,f69])).
% 7.93/1.42  fof(f826,plain,(
% 7.93/1.42    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.93/1.42    inference(backward_demodulation,[],[f534,f823])).
% 7.93/1.42  fof(f823,plain,(
% 7.93/1.42    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)))),
% 7.93/1.42    inference(forward_demodulation,[],[f811,f347])).
% 7.93/1.42  fof(f811,plain,(
% 7.93/1.42    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 7.93/1.42    inference(unit_resulting_resolution,[],[f47,f45,f52])).
% 7.93/1.42  fof(f52,plain,(
% 7.93/1.42    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.93/1.42    inference(cnf_transformation,[],[f30])).
% 7.93/1.42  fof(f30,plain,(
% 7.93/1.42    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.93/1.42    inference(ennf_transformation,[],[f18])).
% 7.93/1.42  fof(f18,axiom,(
% 7.93/1.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 7.93/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 7.93/1.42  fof(f534,plain,(
% 7.93/1.42    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.93/1.42    inference(unit_resulting_resolution,[],[f368,f63])).
% 7.93/1.42  fof(f368,plain,(
% 7.93/1.42    m1_subset_1(k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.93/1.42    inference(backward_demodulation,[],[f312,f347])).
% 7.93/1.42  fof(f312,plain,(
% 7.93/1.42    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.93/1.42    inference(unit_resulting_resolution,[],[f47,f155,f67])).
% 7.93/1.42  fof(f67,plain,(
% 7.93/1.42    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.93/1.42    inference(cnf_transformation,[],[f41])).
% 7.93/1.42  fof(f41,plain,(
% 7.93/1.42    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.93/1.42    inference(flattening,[],[f40])).
% 7.93/1.42  fof(f40,plain,(
% 7.93/1.42    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.93/1.42    inference(ennf_transformation,[],[f16])).
% 7.93/1.42  fof(f16,axiom,(
% 7.93/1.42    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.93/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 7.93/1.42  fof(f155,plain,(
% 7.93/1.42    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.93/1.42    inference(unit_resulting_resolution,[],[f45,f63])).
% 7.93/1.42  fof(f2006,plain,(
% 7.93/1.42    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1))))),
% 7.93/1.42    inference(forward_demodulation,[],[f1954,f90])).
% 7.93/1.42  fof(f1954,plain,(
% 7.93/1.42    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))))),
% 7.93/1.42    inference(unit_resulting_resolution,[],[f826,f337])).
% 7.93/1.42  fof(f828,plain,(
% 7.93/1.42    k5_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 7.93/1.42    inference(backward_demodulation,[],[f436,f825])).
% 7.93/1.42  fof(f825,plain,(
% 7.93/1.42    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 7.93/1.42    inference(backward_demodulation,[],[f533,f823])).
% 7.93/1.42  fof(f533,plain,(
% 7.93/1.42    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))))),
% 7.93/1.42    inference(unit_resulting_resolution,[],[f368,f65])).
% 7.93/1.42  fof(f436,plain,(
% 7.93/1.42    ~v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) | k5_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))),
% 7.93/1.42    inference(global_subsumption,[],[f47,f429])).
% 7.93/1.42  fof(f429,plain,(
% 7.93/1.42    ~l1_pre_topc(sK0) | ~v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) | k5_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))),
% 7.93/1.42    inference(resolution,[],[f54,f348])).
% 7.93/1.42  fof(f348,plain,(
% 7.93/1.42    m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.93/1.42    inference(backward_demodulation,[],[f155,f347])).
% 7.93/1.42  fof(f54,plain,(
% 7.93/1.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 7.93/1.42    inference(cnf_transformation,[],[f32])).
% 7.93/1.42  fof(f32,plain,(
% 7.93/1.42    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.93/1.42    inference(flattening,[],[f31])).
% 7.93/1.42  fof(f31,plain,(
% 7.93/1.42    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.93/1.42    inference(ennf_transformation,[],[f17])).
% 7.93/1.42  fof(f17,axiom,(
% 7.93/1.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 7.93/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 7.93/1.42  fof(f2014,plain,(
% 7.93/1.42    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 7.93/1.42    inference(backward_demodulation,[],[f838,f2007])).
% 7.93/1.42  fof(f838,plain,(
% 7.93/1.42    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 7.93/1.42    inference(backward_demodulation,[],[f823,f825])).
% 7.93/1.42  fof(f775,plain,(
% 7.93/1.42    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 7.93/1.42    inference(unit_resulting_resolution,[],[f47,f45,f51])).
% 7.93/1.42  fof(f51,plain,(
% 7.93/1.42    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.93/1.42    inference(cnf_transformation,[],[f29])).
% 7.93/1.42  fof(f29,plain,(
% 7.93/1.42    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.93/1.42    inference(ennf_transformation,[],[f20])).
% 7.93/1.42  fof(f20,axiom,(
% 7.93/1.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 7.93/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 7.93/1.42  fof(f44,plain,(
% 7.93/1.42    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 7.93/1.42    inference(cnf_transformation,[],[f27])).
% 7.93/1.42  fof(f2363,plain,(
% 7.93/1.42    ( ! [X2] : (sP3(X2,sK1,k2_pre_topc(sK0,sK1)) | ~r2_hidden(X2,k2_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)) )),
% 7.93/1.42    inference(global_subsumption,[],[f314,f2340])).
% 7.93/1.42  fof(f2340,plain,(
% 7.93/1.42    ( ! [X2] : (~r2_hidden(X2,k2_tops_1(sK0,sK1)) | sP3(X2,sK1,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) )),
% 7.93/1.42    inference(superposition,[],[f474,f43])).
% 7.93/1.42  fof(f43,plain,(
% 7.93/1.42    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 7.93/1.42    inference(cnf_transformation,[],[f27])).
% 7.93/1.42  fof(f474,plain,(
% 7.93/1.42    ( ! [X10,X8,X7,X9] : (~r2_hidden(X10,k7_subset_1(X9,X7,X8)) | sP3(X10,X8,X7) | ~m1_subset_1(X7,k1_zfmisc_1(X9))) )),
% 7.93/1.42    inference(superposition,[],[f102,f93])).
% 7.93/1.42  fof(f314,plain,(
% 7.93/1.42    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.93/1.42    inference(unit_resulting_resolution,[],[f47,f45,f67])).
% 7.93/1.42  fof(f254,plain,(
% 7.93/1.42    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 7.93/1.42    inference(global_subsumption,[],[f218,f252])).
% 7.93/1.42  fof(f252,plain,(
% 7.93/1.42    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 7.93/1.42    inference(resolution,[],[f250,f73])).
% 7.93/1.42  fof(f250,plain,(
% 7.93/1.42    ( ! [X0,X1] : (sP3(X1,k1_xboole_0,X0) | ~r2_hidden(X1,X0)) )),
% 7.93/1.42    inference(forward_demodulation,[],[f241,f106])).
% 7.93/1.42  fof(f241,plain,(
% 7.93/1.42    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,k1_xboole_0)) | sP3(X1,k1_xboole_0,X0)) )),
% 7.93/1.42    inference(superposition,[],[f102,f86])).
% 7.93/1.42  fof(f218,plain,(
% 7.93/1.42    ( ! [X2,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X2)) )),
% 7.93/1.42    inference(resolution,[],[f191,f79])).
% 7.93/1.42  fof(f79,plain,(
% 7.93/1.42    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 7.93/1.42    inference(cnf_transformation,[],[f2])).
% 7.93/1.42  fof(f191,plain,(
% 7.93/1.42    ( ! [X0,X1] : (sP5(X1,k1_xboole_0,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 7.93/1.42    inference(superposition,[],[f104,f86])).
% 7.93/1.42  fof(f8265,plain,(
% 7.93/1.42    ( ! [X0] : (k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k7_subset_1(k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),X0)) )),
% 7.93/1.42    inference(unit_resulting_resolution,[],[f8238,f8238,f741])).
% 7.93/1.42  fof(f2060,plain,(
% 7.93/1.42    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))),
% 7.93/1.42    inference(backward_demodulation,[],[f1054,f2046])).
% 7.93/1.42  fof(f2046,plain,(
% 7.93/1.42    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))),
% 7.93/1.42    inference(backward_demodulation,[],[f657,f2044])).
% 7.93/1.42  fof(f1054,plain,(
% 7.93/1.42    k3_subset_1(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))),
% 7.93/1.42    inference(unit_resulting_resolution,[],[f1050,f477])).
% 7.93/1.42  fof(f477,plain,(
% 7.93/1.42    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.93/1.42    inference(backward_demodulation,[],[f92,f457])).
% 7.93/1.42  fof(f1050,plain,(
% 7.93/1.42    m1_subset_1(k5_xboole_0(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))),
% 7.93/1.42    inference(unit_resulting_resolution,[],[f1041,f68])).
% 7.93/1.42  fof(f8295,plain,(
% 7.93/1.42    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_xboole_0)),
% 7.93/1.42    inference(backward_demodulation,[],[f2046,f8285])).
% 8.33/1.44  fof(f8637,plain,(
% 8.33/1.44    k5_xboole_0(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k3_subset_1(sK1,k1_xboole_0))),
% 8.33/1.44    inference(global_subsumption,[],[f6441,f8513])).
% 8.33/1.44  fof(f8513,plain,(
% 8.33/1.44    k5_xboole_0(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k3_subset_1(sK1,k1_xboole_0)) | v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 8.33/1.44    inference(backward_demodulation,[],[f5384,f8295])).
% 8.33/1.44  fof(f5384,plain,(
% 8.33/1.44    k5_xboole_0(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 8.33/1.44    inference(global_subsumption,[],[f47,f46,f348,f5377])).
% 8.33/1.44  fof(f5377,plain,(
% 8.33/1.44    k5_xboole_0(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 8.33/1.44    inference(superposition,[],[f53,f2008])).
% 8.33/1.44  fof(f2008,plain,(
% 8.33/1.44    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 8.33/1.44    inference(backward_demodulation,[],[f825,f2007])).
% 8.33/1.44  fof(f53,plain,(
% 8.33/1.44    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 8.33/1.44    inference(cnf_transformation,[],[f32])).
% 8.33/1.44  fof(f46,plain,(
% 8.33/1.44    v2_pre_topc(sK0)),
% 8.33/1.44    inference(cnf_transformation,[],[f27])).
% 8.33/1.44  fof(f6441,plain,(
% 8.33/1.44    ~v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 8.33/1.44    inference(forward_demodulation,[],[f6440,f347])).
% 8.33/1.44  fof(f6440,plain,(
% 8.33/1.44    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 8.33/1.44    inference(unit_resulting_resolution,[],[f47,f45,f6435,f55])).
% 8.33/1.44  fof(f55,plain,(
% 8.33/1.44    ( ! [X0,X1] : (~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(X1,X0)) )),
% 8.33/1.44    inference(cnf_transformation,[],[f33])).
% 8.33/1.44  % SZS output end Proof for theBenchmark
% 8.33/1.44  % (27586)------------------------------
% 8.33/1.44  % (27586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.33/1.44  % (27586)Termination reason: Refutation
% 8.33/1.44  
% 8.33/1.44  % (27586)Memory used [KB]: 16375
% 8.33/1.44  % (27586)Time elapsed: 0.939 s
% 8.33/1.44  % (27586)------------------------------
% 8.33/1.44  % (27586)------------------------------
% 8.33/1.44  % (27561)Success in time 1.073 s
%------------------------------------------------------------------------------
