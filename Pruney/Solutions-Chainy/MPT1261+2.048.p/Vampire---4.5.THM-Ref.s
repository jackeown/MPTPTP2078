%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:55 EST 2020

% Result     : Theorem 2.55s
% Output     : Refutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  167 (5397 expanded)
%              Number of leaves         :   22 (1555 expanded)
%              Depth                    :   23
%              Number of atoms          :  318 (10045 expanded)
%              Number of equality atoms :  109 (4170 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2657,plain,(
    $false ),
    inference(global_subsumption,[],[f865,f2656])).

fof(f2656,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f2655,f124])).

fof(f124,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f107,f115])).

fof(f115,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f51,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f107,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[],[f85,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f85,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f52,f83])).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f64,f61])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f52,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f2655,plain,(
    k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f944,f2652])).

fof(f2652,plain,(
    k1_xboole_0 = k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f2650,f2577])).

fof(f2577,plain,(
    k1_xboole_0 = k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f2404,f2399,f423])).

fof(f423,plain,(
    ! [X2,X0,X1] :
      ( sP3(sK2(X0,X1,X2),X1,X0)
      | k7_subset_1(X0,X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(backward_demodulation,[],[f94,f395])).

fof(f395,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f126,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f74,f83])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f126,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f114,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f114,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f87,f85])).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f59,f83])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( sP3(sK2(X0,X1,X2),X1,X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 ) ),
    inference(definition_unfolding,[],[f81,f83])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( sP3(sK2(X0,X1,X2),X1,X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f2399,plain,(
    ! [X12] : ~ sP3(X12,u1_struct_0(sK0),k2_tops_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f146,f1114,f2398])).

fof(f2398,plain,(
    ! [X12] :
      ( r2_hidden(X12,k1_xboole_0)
      | ~ sP3(X12,u1_struct_0(sK0),k2_tops_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f2389,f339])).

fof(f339,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f324,f332])).

fof(f332,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f331,f124])).

fof(f331,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f278,f160])).

fof(f160,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(superposition,[],[f115,f60])).

fof(f278,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f100,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f67,f83])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f100,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f51,f71])).

fof(f324,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f323,f166])).

fof(f166,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f100,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f323,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k5_xboole_0(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f281,f189])).

fof(f189,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k1_setfam_1(k2_tarski(X0,k3_subset_1(X0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f187,f60])).

fof(f187,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k1_setfam_1(k2_tarski(k3_subset_1(X0,k1_xboole_0),X0)) ),
    inference(unit_resulting_resolution,[],[f183,f89])).

fof(f183,plain,(
    ! [X0] : r1_tarski(k3_subset_1(X0,k1_xboole_0),X0) ),
    inference(unit_resulting_resolution,[],[f131,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f131,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f100,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f281,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_subset_1(X0,k1_xboole_0)))) ),
    inference(unit_resulting_resolution,[],[f131,f90])).

fof(f2389,plain,(
    ! [X12] :
      ( r2_hidden(X12,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)))
      | ~ sP3(X12,u1_struct_0(sK0),k2_tops_1(sK0,sK1)) ) ),
    inference(superposition,[],[f221,f883])).

fof(f883,plain,(
    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f881,f60])).

fof(f881,plain,(
    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f864,f89])).

fof(f864,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f859,f208])).

fof(f208,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f202,f46])).

fof(f46,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f202,plain,(
    ! [X0] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f194,f72])).

fof(f194,plain,(
    ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f48,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f859,plain,(
    ~ v4_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f50,f48,f448,f858])).

fof(f858,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f853,f429])).

fof(f429,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(backward_demodulation,[],[f399,f395])).

fof(f399,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f48,f91])).

fof(f853,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f55,f389])).

fof(f389,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f50,f385])).

fof(f385,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f57,f48])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f448,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f47,f429])).

fof(f47,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f221,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))))
      | ~ sP3(X2,X1,X0) ) ),
    inference(superposition,[],[f98,f60])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | ~ sP3(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f79,f83])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1114,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f348,f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f348,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f212,f339])).

fof(f212,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,X0))
      | sP3(X1,X0,X0) ) ),
    inference(superposition,[],[f97,f86])).

fof(f86,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f58,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | sP3(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f80,f83])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f146,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k1_xboole_0)
      | r2_hidden(X5,X6) ) ),
    inference(resolution,[],[f69,f100])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f2404,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f861,f2401,f349])).

fof(f349,plain,(
    ! [X4,X2,X3] :
      ( sP3(X4,X3,X2)
      | ~ r2_hidden(X4,k1_xboole_0)
      | ~ r1_tarski(X2,X3) ) ),
    inference(backward_demodulation,[],[f213,f339])).

fof(f213,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k5_xboole_0(X2,X2))
      | sP3(X4,X3,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f97,f89])).

fof(f2401,plain,(
    ! [X14] : ~ sP3(X14,sK1,k2_tops_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f2363,f2399,f2400])).

fof(f2400,plain,(
    ! [X14] :
      ( r2_hidden(X14,k1_xboole_0)
      | ~ sP3(X14,sK1,k2_tops_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f2391,f339])).

fof(f2391,plain,(
    ! [X14] :
      ( r2_hidden(X14,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)))
      | ~ sP3(X14,sK1,k2_tops_1(sK0,sK1)) ) ),
    inference(superposition,[],[f221,f870])).

fof(f870,plain,(
    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f868,f60])).

fof(f868,plain,(
    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) ),
    inference(unit_resulting_resolution,[],[f861,f89])).

fof(f2363,plain,(
    ! [X12] :
      ( sP3(X12,u1_struct_0(sK0),k2_tops_1(sK0,sK1))
      | ~ r2_hidden(X12,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f2354,f339])).

fof(f2354,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)))
      | sP3(X12,u1_struct_0(sK0),k2_tops_1(sK0,sK1)) ) ),
    inference(superposition,[],[f210,f883])).

fof(f210,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))))
      | sP3(X2,X1,X0) ) ),
    inference(superposition,[],[f97,f60])).

fof(f861,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f859,f479])).

fof(f479,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f418,f447])).

fof(f447,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f46,f429])).

fof(f418,plain,(
    ! [X0,X1] : r1_tarski(k7_subset_1(X0,X0,X1),X0) ),
    inference(backward_demodulation,[],[f87,f395])).

fof(f2650,plain,(
    k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) = k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f2399,f2411,f423])).

fof(f2411,plain,(
    ! [X0] : ~ r2_hidden(X0,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)) ),
    inference(forward_demodulation,[],[f2405,f892])).

fof(f892,plain,(
    ! [X0] : k7_subset_1(sK1,k2_tops_1(sK0,sK1),X0) = k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0) ),
    inference(unit_resulting_resolution,[],[f869,f420])).

fof(f420,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(backward_demodulation,[],[f91,f395])).

fof(f869,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f861,f71])).

fof(f2405,plain,(
    ! [X0] : ~ r2_hidden(X0,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) ),
    inference(unit_resulting_resolution,[],[f2401,f424])).

fof(f424,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k7_subset_1(X0,X0,X1))
      | sP3(X3,X1,X0) ) ),
    inference(backward_demodulation,[],[f97,f395])).

fof(f944,plain,(
    k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)) ),
    inference(backward_demodulation,[],[f908,f943])).

fof(f943,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f942,f675])).

fof(f675,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f50,f48,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f942,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f941,f908])).

fof(f941,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)) ),
    inference(forward_demodulation,[],[f936,f892])).

fof(f936,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) ),
    inference(unit_resulting_resolution,[],[f48,f863,f421])).

fof(f421,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(backward_demodulation,[],[f92,f395])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ) ),
    inference(definition_unfolding,[],[f75,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f62,f83])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f863,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f859,f198])).

fof(f198,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f48,f197])).

fof(f197,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f73,f46])).

fof(f908,plain,(
    k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)) ),
    inference(backward_demodulation,[],[f896,f892])).

fof(f896,plain,(
    k5_xboole_0(sK1,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f126,f869,f421])).

fof(f865,plain,(
    sK1 != k2_pre_topc(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f49,f50,f48,f859,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:26:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.50  % (7798)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (7812)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (7804)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (7801)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (7811)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (7800)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (7821)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (7813)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (7802)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (7824)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (7807)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (7823)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (7819)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (7799)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (7808)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (7806)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (7814)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (7818)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (7803)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.55  % (7826)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (7820)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  % (7817)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (7816)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (7815)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (7805)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (7822)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.56  % (7827)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.56  % (7825)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.56  % (7820)Refutation not found, incomplete strategy% (7820)------------------------------
% 0.20/0.56  % (7820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (7820)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (7820)Memory used [KB]: 10746
% 0.20/0.56  % (7820)Time elapsed: 0.144 s
% 0.20/0.56  % (7820)------------------------------
% 0.20/0.56  % (7820)------------------------------
% 0.20/0.56  % (7810)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (7809)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.46/0.58  % (7815)Refutation not found, incomplete strategy% (7815)------------------------------
% 1.46/0.58  % (7815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.58  % (7815)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.58  
% 1.46/0.58  % (7815)Memory used [KB]: 10618
% 1.46/0.58  % (7815)Time elapsed: 0.149 s
% 1.46/0.58  % (7815)------------------------------
% 1.46/0.58  % (7815)------------------------------
% 2.55/0.72  % (7913)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.55/0.72  % (7903)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.55/0.75  % (7822)Refutation found. Thanks to Tanya!
% 2.55/0.75  % SZS status Theorem for theBenchmark
% 2.55/0.76  % SZS output start Proof for theBenchmark
% 2.55/0.76  fof(f2657,plain,(
% 2.55/0.76    $false),
% 2.55/0.76    inference(global_subsumption,[],[f865,f2656])).
% 2.55/0.76  fof(f2656,plain,(
% 2.55/0.76    sK1 = k2_pre_topc(sK0,sK1)),
% 2.55/0.76    inference(forward_demodulation,[],[f2655,f124])).
% 2.55/0.76  fof(f124,plain,(
% 2.55/0.76    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.55/0.76    inference(backward_demodulation,[],[f107,f115])).
% 2.55/0.76  fof(f115,plain,(
% 2.55/0.76    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) )),
% 2.55/0.76    inference(unit_resulting_resolution,[],[f51,f89])).
% 2.55/0.76  fof(f89,plain,(
% 2.55/0.76    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.55/0.76    inference(definition_unfolding,[],[f65,f61])).
% 2.55/0.76  fof(f61,plain,(
% 2.55/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.55/0.76    inference(cnf_transformation,[],[f18])).
% 2.55/0.76  fof(f18,axiom,(
% 2.55/0.76    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.55/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.55/0.76  fof(f65,plain,(
% 2.55/0.76    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.55/0.76    inference(cnf_transformation,[],[f35])).
% 2.55/0.76  fof(f35,plain,(
% 2.55/0.76    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.55/0.76    inference(ennf_transformation,[],[f4])).
% 2.55/0.76  fof(f4,axiom,(
% 2.55/0.76    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.55/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.55/0.76  fof(f51,plain,(
% 2.55/0.76    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.55/0.76    inference(cnf_transformation,[],[f5])).
% 2.55/0.76  fof(f5,axiom,(
% 2.55/0.76    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.55/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.55/0.76  fof(f107,plain,(
% 2.55/0.76    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = X0) )),
% 2.55/0.76    inference(superposition,[],[f85,f60])).
% 2.55/0.76  fof(f60,plain,(
% 2.55/0.76    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.55/0.76    inference(cnf_transformation,[],[f10])).
% 2.55/0.76  fof(f10,axiom,(
% 2.55/0.76    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.55/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.55/0.76  fof(f85,plain,(
% 2.55/0.76    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 2.55/0.76    inference(definition_unfolding,[],[f52,f83])).
% 2.55/0.76  fof(f83,plain,(
% 2.55/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.55/0.76    inference(definition_unfolding,[],[f64,f61])).
% 2.55/0.76  fof(f64,plain,(
% 2.55/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.55/0.76    inference(cnf_transformation,[],[f3])).
% 2.55/0.76  fof(f3,axiom,(
% 2.55/0.76    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.55/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.55/0.76  fof(f52,plain,(
% 2.55/0.76    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.55/0.76    inference(cnf_transformation,[],[f7])).
% 2.55/0.76  fof(f7,axiom,(
% 2.55/0.76    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.55/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.55/0.76  fof(f2655,plain,(
% 2.55/0.76    k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0)),
% 2.55/0.76    inference(backward_demodulation,[],[f944,f2652])).
% 2.55/0.76  fof(f2652,plain,(
% 2.55/0.76    k1_xboole_0 = k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)),
% 2.55/0.76    inference(forward_demodulation,[],[f2650,f2577])).
% 2.55/0.76  fof(f2577,plain,(
% 2.55/0.76    k1_xboole_0 = k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 2.55/0.76    inference(unit_resulting_resolution,[],[f2404,f2399,f423])).
% 2.55/0.76  fof(f423,plain,(
% 2.55/0.76    ( ! [X2,X0,X1] : (sP3(sK2(X0,X1,X2),X1,X0) | k7_subset_1(X0,X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.55/0.76    inference(backward_demodulation,[],[f94,f395])).
% 2.55/0.76  fof(f395,plain,(
% 2.55/0.76    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1)) )),
% 2.55/0.76    inference(unit_resulting_resolution,[],[f126,f91])).
% 2.55/0.76  fof(f91,plain,(
% 2.55/0.76    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.55/0.76    inference(definition_unfolding,[],[f74,f83])).
% 2.55/0.76  fof(f74,plain,(
% 2.55/0.76    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.55/0.76    inference(cnf_transformation,[],[f43])).
% 2.55/0.76  fof(f43,plain,(
% 2.55/0.76    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.55/0.76    inference(ennf_transformation,[],[f17])).
% 2.55/0.76  fof(f17,axiom,(
% 2.55/0.76    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.55/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.55/0.76  fof(f126,plain,(
% 2.55/0.76    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.55/0.76    inference(unit_resulting_resolution,[],[f114,f71])).
% 2.55/0.76  fof(f71,plain,(
% 2.55/0.76    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.55/0.76    inference(cnf_transformation,[],[f19])).
% 2.55/0.76  fof(f19,axiom,(
% 2.55/0.76    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.55/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.55/0.76  fof(f114,plain,(
% 2.55/0.76    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.55/0.76    inference(superposition,[],[f87,f85])).
% 2.55/0.76  fof(f87,plain,(
% 2.55/0.76    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 2.55/0.76    inference(definition_unfolding,[],[f59,f83])).
% 2.55/0.76  fof(f59,plain,(
% 2.55/0.76    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.55/0.76    inference(cnf_transformation,[],[f6])).
% 2.55/0.76  fof(f6,axiom,(
% 2.55/0.76    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.55/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.55/0.76  fof(f94,plain,(
% 2.55/0.76    ( ! [X2,X0,X1] : (sP3(sK2(X0,X1,X2),X1,X0) | r2_hidden(sK2(X0,X1,X2),X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2) )),
% 2.55/0.76    inference(definition_unfolding,[],[f81,f83])).
% 2.55/0.76  fof(f81,plain,(
% 2.55/0.76    ( ! [X2,X0,X1] : (sP3(sK2(X0,X1,X2),X1,X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.55/0.76    inference(cnf_transformation,[],[f1])).
% 2.55/0.76  fof(f1,axiom,(
% 2.55/0.76    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.55/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.55/0.76  fof(f2399,plain,(
% 2.55/0.76    ( ! [X12] : (~sP3(X12,u1_struct_0(sK0),k2_tops_1(sK0,sK1))) )),
% 2.55/0.76    inference(global_subsumption,[],[f146,f1114,f2398])).
% 2.55/0.76  fof(f2398,plain,(
% 2.55/0.76    ( ! [X12] : (r2_hidden(X12,k1_xboole_0) | ~sP3(X12,u1_struct_0(sK0),k2_tops_1(sK0,sK1))) )),
% 2.55/0.76    inference(forward_demodulation,[],[f2389,f339])).
% 2.55/0.76  fof(f339,plain,(
% 2.55/0.76    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.55/0.76    inference(backward_demodulation,[],[f324,f332])).
% 2.55/0.76  fof(f332,plain,(
% 2.55/0.76    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 2.55/0.76    inference(forward_demodulation,[],[f331,f124])).
% 2.55/0.76  fof(f331,plain,(
% 2.55/0.76    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 2.55/0.76    inference(forward_demodulation,[],[f278,f160])).
% 2.55/0.76  fof(f160,plain,(
% 2.55/0.76    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 2.55/0.76    inference(superposition,[],[f115,f60])).
% 2.55/0.76  fof(f278,plain,(
% 2.55/0.76    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0)) )),
% 2.55/0.76    inference(unit_resulting_resolution,[],[f100,f90])).
% 2.55/0.76  fof(f90,plain,(
% 2.55/0.76    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.55/0.76    inference(definition_unfolding,[],[f67,f83])).
% 2.55/0.76  fof(f67,plain,(
% 2.55/0.76    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.55/0.76    inference(cnf_transformation,[],[f37])).
% 2.55/0.76  fof(f37,plain,(
% 2.55/0.76    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.55/0.76    inference(ennf_transformation,[],[f11])).
% 2.55/0.76  fof(f11,axiom,(
% 2.55/0.76    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.55/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.55/0.76  fof(f100,plain,(
% 2.55/0.76    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.55/0.76    inference(unit_resulting_resolution,[],[f51,f71])).
% 2.55/0.76  fof(f324,plain,(
% 2.55/0.76    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 2.55/0.76    inference(forward_demodulation,[],[f323,f166])).
% 2.55/0.76  fof(f166,plain,(
% 2.55/0.76    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 2.55/0.76    inference(unit_resulting_resolution,[],[f100,f68])).
% 2.55/0.76  fof(f68,plain,(
% 2.55/0.76    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.55/0.76    inference(cnf_transformation,[],[f38])).
% 2.55/0.76  fof(f38,plain,(
% 2.55/0.76    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.55/0.76    inference(ennf_transformation,[],[f14])).
% 2.55/0.76  fof(f14,axiom,(
% 2.55/0.76    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.55/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.55/0.76  fof(f323,plain,(
% 2.55/0.76    ( ! [X0] : (k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k5_xboole_0(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 2.55/0.76    inference(forward_demodulation,[],[f281,f189])).
% 2.55/0.76  fof(f189,plain,(
% 2.55/0.76    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k1_setfam_1(k2_tarski(X0,k3_subset_1(X0,k1_xboole_0)))) )),
% 2.55/0.76    inference(forward_demodulation,[],[f187,f60])).
% 2.55/0.76  fof(f187,plain,(
% 2.55/0.76    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k1_setfam_1(k2_tarski(k3_subset_1(X0,k1_xboole_0),X0))) )),
% 2.55/0.76    inference(unit_resulting_resolution,[],[f183,f89])).
% 2.55/0.76  fof(f183,plain,(
% 2.55/0.76    ( ! [X0] : (r1_tarski(k3_subset_1(X0,k1_xboole_0),X0)) )),
% 2.55/0.76    inference(unit_resulting_resolution,[],[f131,f72])).
% 2.55/0.76  fof(f72,plain,(
% 2.55/0.76    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.55/0.76    inference(cnf_transformation,[],[f19])).
% 2.55/0.76  fof(f131,plain,(
% 2.55/0.76    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 2.55/0.76    inference(unit_resulting_resolution,[],[f100,f66])).
% 2.55/0.76  fof(f66,plain,(
% 2.55/0.76    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.55/0.76    inference(cnf_transformation,[],[f36])).
% 2.55/0.76  fof(f36,plain,(
% 2.55/0.76    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.55/0.76    inference(ennf_transformation,[],[f12])).
% 2.98/0.77  fof(f12,axiom,(
% 2.98/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.98/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.98/0.77  fof(f281,plain,(
% 2.98/0.77    ( ! [X0] : (k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_subset_1(X0,k1_xboole_0))))) )),
% 2.98/0.77    inference(unit_resulting_resolution,[],[f131,f90])).
% 2.98/0.77  fof(f2389,plain,(
% 2.98/0.77    ( ! [X12] : (r2_hidden(X12,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) | ~sP3(X12,u1_struct_0(sK0),k2_tops_1(sK0,sK1))) )),
% 2.98/0.77    inference(superposition,[],[f221,f883])).
% 2.98/0.77  fof(f883,plain,(
% 2.98/0.77    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 2.98/0.77    inference(forward_demodulation,[],[f881,f60])).
% 2.98/0.77  fof(f881,plain,(
% 2.98/0.77    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)))),
% 2.98/0.77    inference(unit_resulting_resolution,[],[f864,f89])).
% 2.98/0.77  fof(f864,plain,(
% 2.98/0.77    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 2.98/0.77    inference(unit_resulting_resolution,[],[f859,f208])).
% 2.98/0.77  fof(f208,plain,(
% 2.98/0.77    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | v4_pre_topc(sK1,sK0)),
% 2.98/0.77    inference(superposition,[],[f202,f46])).
% 2.98/0.77  fof(f46,plain,(
% 2.98/0.77    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.98/0.77    inference(cnf_transformation,[],[f29])).
% 2.98/0.77  fof(f29,plain,(
% 2.98/0.77    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.98/0.77    inference(flattening,[],[f28])).
% 2.98/0.77  fof(f28,plain,(
% 2.98/0.77    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.98/0.77    inference(ennf_transformation,[],[f26])).
% 2.98/0.77  fof(f26,negated_conjecture,(
% 2.98/0.77    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.98/0.77    inference(negated_conjecture,[],[f25])).
% 2.98/0.77  fof(f25,conjecture,(
% 2.98/0.77    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.98/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 2.98/0.77  fof(f202,plain,(
% 2.98/0.77    ( ! [X0] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0))) )),
% 2.98/0.77    inference(unit_resulting_resolution,[],[f194,f72])).
% 2.98/0.77  fof(f194,plain,(
% 2.98/0.77    ( ! [X0] : (m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.98/0.77    inference(unit_resulting_resolution,[],[f48,f73])).
% 2.98/0.77  fof(f73,plain,(
% 2.98/0.77    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.98/0.77    inference(cnf_transformation,[],[f42])).
% 2.98/0.77  fof(f42,plain,(
% 2.98/0.77    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.98/0.77    inference(ennf_transformation,[],[f13])).
% 2.98/0.77  fof(f13,axiom,(
% 2.98/0.77    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.98/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 2.98/0.78  fof(f48,plain,(
% 2.98/0.78    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.98/0.78    inference(cnf_transformation,[],[f29])).
% 2.98/0.78  fof(f859,plain,(
% 2.98/0.78    ~v4_pre_topc(sK1,sK0)),
% 2.98/0.78    inference(global_subsumption,[],[f50,f48,f448,f858])).
% 2.98/0.78  fof(f858,plain,(
% 2.98/0.78    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0)),
% 2.98/0.78    inference(forward_demodulation,[],[f853,f429])).
% 2.98/0.78  fof(f429,plain,(
% 2.98/0.78    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)) )),
% 2.98/0.78    inference(backward_demodulation,[],[f399,f395])).
% 2.98/0.78  fof(f399,plain,(
% 2.98/0.78    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) )),
% 2.98/0.78    inference(unit_resulting_resolution,[],[f48,f91])).
% 2.98/0.78  fof(f853,plain,(
% 2.98/0.78    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0)),
% 2.98/0.78    inference(superposition,[],[f55,f389])).
% 2.98/0.78  fof(f389,plain,(
% 2.98/0.78    sK1 = k2_pre_topc(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 2.98/0.78    inference(global_subsumption,[],[f50,f385])).
% 2.98/0.78  fof(f385,plain,(
% 2.98/0.78    ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 2.98/0.78    inference(resolution,[],[f57,f48])).
% 2.98/0.78  fof(f57,plain,(
% 2.98/0.78    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 2.98/0.78    inference(cnf_transformation,[],[f34])).
% 2.98/0.78  fof(f34,plain,(
% 2.98/0.78    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.98/0.78    inference(flattening,[],[f33])).
% 2.98/0.78  fof(f33,plain,(
% 2.98/0.78    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.98/0.78    inference(ennf_transformation,[],[f20])).
% 2.98/0.78  fof(f20,axiom,(
% 2.98/0.78    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.98/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.98/0.78  fof(f55,plain,(
% 2.98/0.78    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.98/0.78    inference(cnf_transformation,[],[f32])).
% 2.98/0.78  fof(f32,plain,(
% 2.98/0.78    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.98/0.78    inference(ennf_transformation,[],[f22])).
% 2.98/0.78  fof(f22,axiom,(
% 2.98/0.78    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.98/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 2.98/0.78  fof(f448,plain,(
% 2.98/0.78    k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.98/0.78    inference(backward_demodulation,[],[f47,f429])).
% 2.98/0.78  fof(f47,plain,(
% 2.98/0.78    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.98/0.78    inference(cnf_transformation,[],[f29])).
% 2.98/0.78  fof(f50,plain,(
% 2.98/0.78    l1_pre_topc(sK0)),
% 2.98/0.78    inference(cnf_transformation,[],[f29])).
% 2.98/0.78  fof(f221,plain,(
% 2.98/0.78    ( ! [X2,X0,X1] : (r2_hidden(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))) | ~sP3(X2,X1,X0)) )),
% 2.98/0.78    inference(superposition,[],[f98,f60])).
% 2.98/0.78  fof(f98,plain,(
% 2.98/0.78    ( ! [X0,X3,X1] : (r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | ~sP3(X3,X1,X0)) )),
% 2.98/0.78    inference(equality_resolution,[],[f96])).
% 2.98/0.78  fof(f96,plain,(
% 2.98/0.78    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 2.98/0.78    inference(definition_unfolding,[],[f79,f83])).
% 2.98/0.78  fof(f79,plain,(
% 2.98/0.78    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.98/0.78    inference(cnf_transformation,[],[f1])).
% 2.98/0.78  fof(f1114,plain,(
% 2.98/0.78    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 2.98/0.78    inference(resolution,[],[f348,f78])).
% 2.98/0.78  fof(f78,plain,(
% 2.98/0.78    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 2.98/0.78    inference(cnf_transformation,[],[f1])).
% 2.98/0.78  fof(f348,plain,(
% 2.98/0.78    ( ! [X0,X1] : (sP3(X1,X0,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 2.98/0.78    inference(backward_demodulation,[],[f212,f339])).
% 2.98/0.78  fof(f212,plain,(
% 2.98/0.78    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0)) | sP3(X1,X0,X0)) )),
% 2.98/0.78    inference(superposition,[],[f97,f86])).
% 2.98/0.78  fof(f86,plain,(
% 2.98/0.78    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 2.98/0.78    inference(definition_unfolding,[],[f58,f61])).
% 2.98/0.78  fof(f58,plain,(
% 2.98/0.78    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.98/0.78    inference(cnf_transformation,[],[f27])).
% 2.98/0.78  fof(f27,plain,(
% 2.98/0.78    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.98/0.78    inference(rectify,[],[f2])).
% 2.98/0.78  fof(f2,axiom,(
% 2.98/0.78    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.98/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.98/0.78  fof(f97,plain,(
% 2.98/0.78    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | sP3(X3,X1,X0)) )),
% 2.98/0.78    inference(equality_resolution,[],[f95])).
% 2.98/0.78  fof(f95,plain,(
% 2.98/0.78    ( ! [X2,X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 2.98/0.78    inference(definition_unfolding,[],[f80,f83])).
% 2.98/0.78  fof(f80,plain,(
% 2.98/0.78    ( ! [X2,X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.98/0.78    inference(cnf_transformation,[],[f1])).
% 2.98/0.78  fof(f146,plain,(
% 2.98/0.78    ( ! [X6,X5] : (~r2_hidden(X5,k1_xboole_0) | r2_hidden(X5,X6)) )),
% 2.98/0.78    inference(resolution,[],[f69,f100])).
% 2.98/0.78  fof(f69,plain,(
% 2.98/0.78    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 2.98/0.78    inference(cnf_transformation,[],[f39])).
% 2.98/0.78  fof(f39,plain,(
% 2.98/0.78    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.98/0.78    inference(ennf_transformation,[],[f15])).
% 2.98/0.78  fof(f15,axiom,(
% 2.98/0.78    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.98/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 2.98/0.78  fof(f2404,plain,(
% 2.98/0.78    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.98/0.78    inference(unit_resulting_resolution,[],[f861,f2401,f349])).
% 2.98/0.78  fof(f349,plain,(
% 2.98/0.78    ( ! [X4,X2,X3] : (sP3(X4,X3,X2) | ~r2_hidden(X4,k1_xboole_0) | ~r1_tarski(X2,X3)) )),
% 2.98/0.78    inference(backward_demodulation,[],[f213,f339])).
% 2.98/0.78  fof(f213,plain,(
% 2.98/0.78    ( ! [X4,X2,X3] : (~r2_hidden(X4,k5_xboole_0(X2,X2)) | sP3(X4,X3,X2) | ~r1_tarski(X2,X3)) )),
% 2.98/0.78    inference(superposition,[],[f97,f89])).
% 2.98/0.78  fof(f2401,plain,(
% 2.98/0.78    ( ! [X14] : (~sP3(X14,sK1,k2_tops_1(sK0,sK1))) )),
% 2.98/0.78    inference(global_subsumption,[],[f2363,f2399,f2400])).
% 2.98/0.78  fof(f2400,plain,(
% 2.98/0.78    ( ! [X14] : (r2_hidden(X14,k1_xboole_0) | ~sP3(X14,sK1,k2_tops_1(sK0,sK1))) )),
% 2.98/0.78    inference(forward_demodulation,[],[f2391,f339])).
% 2.98/0.78  fof(f2391,plain,(
% 2.98/0.78    ( ! [X14] : (r2_hidden(X14,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) | ~sP3(X14,sK1,k2_tops_1(sK0,sK1))) )),
% 2.98/0.78    inference(superposition,[],[f221,f870])).
% 2.98/0.78  fof(f870,plain,(
% 2.98/0.78    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 2.98/0.78    inference(forward_demodulation,[],[f868,f60])).
% 2.98/0.78  fof(f868,plain,(
% 2.98/0.78    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))),
% 2.98/0.78    inference(unit_resulting_resolution,[],[f861,f89])).
% 2.98/0.78  fof(f2363,plain,(
% 2.98/0.78    ( ! [X12] : (sP3(X12,u1_struct_0(sK0),k2_tops_1(sK0,sK1)) | ~r2_hidden(X12,k1_xboole_0)) )),
% 2.98/0.78    inference(forward_demodulation,[],[f2354,f339])).
% 2.98/0.78  fof(f2354,plain,(
% 2.98/0.78    ( ! [X12] : (~r2_hidden(X12,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) | sP3(X12,u1_struct_0(sK0),k2_tops_1(sK0,sK1))) )),
% 2.98/0.78    inference(superposition,[],[f210,f883])).
% 2.98/0.78  fof(f210,plain,(
% 2.98/0.78    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))) | sP3(X2,X1,X0)) )),
% 2.98/0.78    inference(superposition,[],[f97,f60])).
% 2.98/0.78  fof(f861,plain,(
% 2.98/0.78    r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.98/0.78    inference(unit_resulting_resolution,[],[f859,f479])).
% 2.98/0.78  fof(f479,plain,(
% 2.98/0.78    r1_tarski(k2_tops_1(sK0,sK1),sK1) | v4_pre_topc(sK1,sK0)),
% 2.98/0.78    inference(superposition,[],[f418,f447])).
% 2.98/0.78  fof(f447,plain,(
% 2.98/0.78    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.98/0.78    inference(backward_demodulation,[],[f46,f429])).
% 2.98/0.78  fof(f418,plain,(
% 2.98/0.78    ( ! [X0,X1] : (r1_tarski(k7_subset_1(X0,X0,X1),X0)) )),
% 2.98/0.78    inference(backward_demodulation,[],[f87,f395])).
% 2.98/0.78  fof(f2650,plain,(
% 2.98/0.78    k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) = k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 2.98/0.78    inference(unit_resulting_resolution,[],[f2399,f2411,f423])).
% 2.98/0.78  fof(f2411,plain,(
% 2.98/0.78    ( ! [X0] : (~r2_hidden(X0,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1))) )),
% 2.98/0.78    inference(forward_demodulation,[],[f2405,f892])).
% 2.98/0.78  fof(f892,plain,(
% 2.98/0.78    ( ! [X0] : (k7_subset_1(sK1,k2_tops_1(sK0,sK1),X0) = k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0)) )),
% 2.98/0.78    inference(unit_resulting_resolution,[],[f869,f420])).
% 2.98/0.78  fof(f420,plain,(
% 2.98/0.78    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.98/0.78    inference(backward_demodulation,[],[f91,f395])).
% 2.98/0.78  fof(f869,plain,(
% 2.98/0.78    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.98/0.78    inference(unit_resulting_resolution,[],[f861,f71])).
% 2.98/0.78  fof(f2405,plain,(
% 2.98/0.78    ( ! [X0] : (~r2_hidden(X0,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1))) )),
% 2.98/0.78    inference(unit_resulting_resolution,[],[f2401,f424])).
% 2.98/0.78  fof(f424,plain,(
% 2.98/0.78    ( ! [X0,X3,X1] : (~r2_hidden(X3,k7_subset_1(X0,X0,X1)) | sP3(X3,X1,X0)) )),
% 2.98/0.78    inference(backward_demodulation,[],[f97,f395])).
% 2.98/0.78  fof(f944,plain,(
% 2.98/0.78    k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1))),
% 2.98/0.78    inference(backward_demodulation,[],[f908,f943])).
% 2.98/0.78  fof(f943,plain,(
% 2.98/0.78    k2_pre_topc(sK0,sK1) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))),
% 2.98/0.78    inference(forward_demodulation,[],[f942,f675])).
% 2.98/0.78  fof(f675,plain,(
% 2.98/0.78    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.98/0.78    inference(unit_resulting_resolution,[],[f50,f48,f54])).
% 2.98/0.78  fof(f54,plain,(
% 2.98/0.78    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.98/0.78    inference(cnf_transformation,[],[f31])).
% 2.98/0.78  fof(f31,plain,(
% 2.98/0.78    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.98/0.78    inference(ennf_transformation,[],[f24])).
% 2.98/0.78  fof(f24,axiom,(
% 2.98/0.78    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.98/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.98/0.78  fof(f942,plain,(
% 2.98/0.78    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))),
% 2.98/0.78    inference(forward_demodulation,[],[f941,f908])).
% 2.98/0.78  fof(f941,plain,(
% 2.98/0.78    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1))),
% 2.98/0.78    inference(forward_demodulation,[],[f936,f892])).
% 2.98/0.78  fof(f936,plain,(
% 2.98/0.78    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1))),
% 2.98/0.78    inference(unit_resulting_resolution,[],[f48,f863,f421])).
% 2.98/0.78  fof(f421,plain,(
% 2.98/0.78    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.98/0.78    inference(backward_demodulation,[],[f92,f395])).
% 2.98/0.78  fof(f92,plain,(
% 2.98/0.78    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))) )),
% 2.98/0.78    inference(definition_unfolding,[],[f75,f84])).
% 2.98/0.78  fof(f84,plain,(
% 2.98/0.78    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 2.98/0.78    inference(definition_unfolding,[],[f62,f83])).
% 2.98/0.78  fof(f62,plain,(
% 2.98/0.78    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.98/0.78    inference(cnf_transformation,[],[f9])).
% 2.98/0.78  fof(f9,axiom,(
% 2.98/0.78    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.98/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.98/0.78  fof(f75,plain,(
% 2.98/0.78    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 2.98/0.78    inference(cnf_transformation,[],[f45])).
% 2.98/0.78  fof(f45,plain,(
% 2.98/0.78    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.98/0.78    inference(flattening,[],[f44])).
% 2.98/0.78  fof(f44,plain,(
% 2.98/0.78    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.98/0.78    inference(ennf_transformation,[],[f16])).
% 2.98/0.78  fof(f16,axiom,(
% 2.98/0.78    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.98/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.98/0.78  fof(f863,plain,(
% 2.98/0.78    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.98/0.78    inference(unit_resulting_resolution,[],[f859,f198])).
% 2.98/0.78  fof(f198,plain,(
% 2.98/0.78    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK1,sK0)),
% 2.98/0.78    inference(global_subsumption,[],[f48,f197])).
% 2.98/0.78  fof(f197,plain,(
% 2.98/0.78    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK1,sK0)),
% 2.98/0.78    inference(superposition,[],[f73,f46])).
% 2.98/0.78  fof(f908,plain,(
% 2.98/0.78    k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(sK1,k2_tops_1(sK0,sK1),sK1))),
% 2.98/0.78    inference(backward_demodulation,[],[f896,f892])).
% 2.98/0.78  fof(f896,plain,(
% 2.98/0.78    k5_xboole_0(sK1,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))),
% 2.98/0.78    inference(unit_resulting_resolution,[],[f126,f869,f421])).
% 2.98/0.78  fof(f865,plain,(
% 2.98/0.78    sK1 != k2_pre_topc(sK0,sK1)),
% 2.98/0.78    inference(unit_resulting_resolution,[],[f49,f50,f48,f859,f56])).
% 2.98/0.78  fof(f56,plain,(
% 2.98/0.78    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 2.98/0.78    inference(cnf_transformation,[],[f34])).
% 2.98/0.78  fof(f49,plain,(
% 2.98/0.78    v2_pre_topc(sK0)),
% 2.98/0.78    inference(cnf_transformation,[],[f29])).
% 2.98/0.78  % SZS output end Proof for theBenchmark
% 2.98/0.78  % (7822)------------------------------
% 2.98/0.78  % (7822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.98/0.78  % (7822)Termination reason: Refutation
% 2.98/0.78  
% 2.98/0.78  % (7822)Memory used [KB]: 9338
% 2.98/0.78  % (7822)Time elapsed: 0.338 s
% 2.98/0.78  % (7822)------------------------------
% 2.98/0.78  % (7822)------------------------------
% 2.98/0.78  % (7797)Success in time 0.411 s
%------------------------------------------------------------------------------
