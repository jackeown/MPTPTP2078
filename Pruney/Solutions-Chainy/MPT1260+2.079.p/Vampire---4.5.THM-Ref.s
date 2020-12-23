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
% DateTime   : Thu Dec  3 13:11:46 EST 2020

% Result     : Theorem 2.76s
% Output     : Refutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  125 (3591 expanded)
%              Number of leaves         :   12 (1079 expanded)
%              Depth                    :   32
%              Number of atoms          :  296 (7168 expanded)
%              Number of equality atoms :   82 (2877 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2309,plain,(
    $false ),
    inference(global_subsumption,[],[f328,f2308])).

fof(f2308,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f2280,f68])).

fof(f68,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f54,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f28,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f54,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f29,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f2280,plain,(
    k5_xboole_0(sK1,k1_xboole_0) = k1_tops_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f682,f2274])).

fof(f2274,plain,(
    k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f2271,f983])).

fof(f983,plain,(
    ! [X8,X9] :
      ( sP5(sK2(sK1,sK1,k1_setfam_1(k2_tarski(X8,X9))),X9,X8)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X8,X9)) ) ),
    inference(resolution,[],[f973,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1)))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f49,f34])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f973,plain,(
    ! [X6] :
      ( r2_hidden(sK2(sK1,sK1,X6),X6)
      | k1_xboole_0 = X6 ) ),
    inference(resolution,[],[f857,f838])).

fof(f838,plain,(
    ! [X5] : ~ sP3(X5,sK1,sK1) ),
    inference(global_subsumption,[],[f83,f833])).

fof(f833,plain,(
    ! [X5] :
      ( r2_hidden(X5,k1_xboole_0)
      | ~ sP3(X5,sK1,sK1) ) ),
    inference(superposition,[],[f129,f811])).

fof(f811,plain,(
    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f801])).

fof(f801,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    inference(resolution,[],[f755,f754])).

fof(f754,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k1_xboole_0,X1,k7_subset_1(u1_struct_0(sK0),sK1,X0)),X0)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,X0) ) ),
    inference(resolution,[],[f452,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f452,plain,(
    ! [X6,X5] :
      ( sP3(sK4(k1_xboole_0,X6,k7_subset_1(u1_struct_0(sK0),sK1,X5)),X5,sK1)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,X5) ) ),
    inference(resolution,[],[f172,f130])).

fof(f130,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k7_subset_1(u1_struct_0(sK0),sK1,X4))
      | sP3(X5,X4,sK1) ) ),
    inference(superposition,[],[f64,f117])).

fof(f117,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f25,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f37,f52])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | sP3(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f172,plain,(
    ! [X10,X9] :
      ( r2_hidden(sK4(k1_xboole_0,X9,X10),X10)
      | k1_xboole_0 = X10 ) ),
    inference(forward_demodulation,[],[f161,f156])).

fof(f156,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f83,f86,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sP5(sK4(X0,X1,X2),X1,X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f50,f34])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP5(sK4(X0,X1,X2),X1,X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f86,plain,(
    ! [X0,X1] : ~ sP5(X0,X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f83,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f161,plain,(
    ! [X10,X9] :
      ( r2_hidden(sK4(k1_xboole_0,X9,X10),X10)
      | k1_setfam_1(k2_tarski(k1_xboole_0,X9)) = X10 ) ),
    inference(resolution,[],[f61,f86])).

fof(f755,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(k1_xboole_0,X3,k7_subset_1(u1_struct_0(sK0),sK1,X2)),sK1)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,X2) ) ),
    inference(resolution,[],[f452,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f129,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,k7_subset_1(u1_struct_0(sK0),sK1,X2))
      | ~ sP3(X3,X2,sK1) ) ),
    inference(superposition,[],[f65,f117])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | ~ sP3(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f83,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_subsumption,[],[f76,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f80,f40])).

fof(f80,plain,(
    ! [X0,X1] :
      ( sP3(X1,k1_xboole_0,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(forward_demodulation,[],[f79,f68])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,k1_xboole_0))
      | sP3(X1,k1_xboole_0,X0) ) ),
    inference(superposition,[],[f64,f53])).

fof(f76,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f74,f46])).

fof(f74,plain,(
    ! [X0,X1] :
      ( sP5(X1,k1_xboole_0,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f66,f53])).

fof(f857,plain,(
    ! [X0] :
      ( sP3(sK2(sK1,sK1,X0),sK1,sK1)
      | r2_hidden(sK2(sK1,sK1,X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f845,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
      | r2_hidden(sK2(X0,X1,X2),X2)
      | sP3(sK2(X0,X1,X2),X1,X0) ) ),
    inference(definition_unfolding,[],[f43,f52])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sP3(sK2(X0,X1,X2),X1,X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f845,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK1))) ),
    inference(unit_resulting_resolution,[],[f83,f838,f57])).

fof(f2271,plain,(
    ! [X6] : ~ sP5(X6,k2_tops_1(sK0,sK1),sK1) ),
    inference(global_subsumption,[],[f328,f2270])).

fof(f2270,plain,(
    ! [X6] :
      ( sK1 = k1_tops_1(sK0,sK1)
      | ~ sP5(X6,k2_tops_1(sK0,sK1),sK1) ) ),
    inference(forward_demodulation,[],[f2253,f68])).

fof(f2253,plain,(
    ! [X6] :
      ( k5_xboole_0(sK1,k1_xboole_0) = k1_tops_1(sK0,sK1)
      | ~ sP5(X6,k2_tops_1(sK0,sK1),sK1) ) ),
    inference(superposition,[],[f682,f2214])).

fof(f2214,plain,(
    ! [X2] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
      | ~ sP5(X2,k2_tops_1(sK0,sK1),sK1) ) ),
    inference(resolution,[],[f2194,f172])).

fof(f2194,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))
      | ~ sP5(X1,k2_tops_1(sK0,sK1),sK1) ) ),
    inference(resolution,[],[f2181,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f34])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f2181,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))
      | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) ) ),
    inference(resolution,[],[f1050,f1031])).

fof(f1031,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK2(sK1,sK1,k1_setfam_1(k2_tarski(X4,X5))),X4)
      | ~ r2_hidden(X3,k1_setfam_1(k2_tarski(X4,X5))) ) ),
    inference(resolution,[],[f884,f46])).

fof(f884,plain,(
    ! [X14,X15,X16] :
      ( sP5(sK2(sK1,sK1,k1_setfam_1(k2_tarski(X15,X16))),X16,X15)
      | ~ r2_hidden(X14,k1_setfam_1(k2_tarski(X15,X16))) ) ),
    inference(resolution,[],[f855,f66])).

fof(f855,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK2(sK1,sK1,X2),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(global_subsumption,[],[f838,f848])).

fof(f848,plain,(
    ! [X2,X1] :
      ( sP3(X1,sK1,sK1)
      | r2_hidden(sK2(sK1,sK1,X2),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f838,f252])).

fof(f252,plain,(
    ! [X14,X12,X15,X13] :
      ( sP3(sK2(X12,X13,X14),X13,X12)
      | sP3(X15,X13,X12)
      | r2_hidden(sK2(X12,X13,X14),X14)
      | ~ r2_hidden(X15,X14) ) ),
    inference(superposition,[],[f64,f57])).

fof(f1050,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(sK2(sK1,sK1,k1_setfam_1(k2_tarski(X29,k2_tops_1(sK0,sK1)))),sK1)
      | ~ r2_hidden(X28,k1_setfam_1(k2_tarski(X29,k2_tops_1(sK0,sK1)))) ) ),
    inference(resolution,[],[f1030,f374])).

fof(f374,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_tops_1(sK0,sK1))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f371,f40])).

fof(f371,plain,(
    ! [X0] :
      ( sP3(X0,sK1,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X0,k2_tops_1(sK0,sK1)) ) ),
    inference(superposition,[],[f265,f321])).

fof(f321,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f320,f23])).

fof(f23,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f320,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f24,f315])).

fof(f315,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f186,f311])).

fof(f311,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f27,f26,f302])).

fof(f302,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f285,f25])).

fof(f285,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(sK1,sK0)
      | sK1 = k1_tops_1(sK0,sK1) ) ),
    inference(global_subsumption,[],[f27,f276])).

fof(f276,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(sK1,sK0)
      | sK1 = k1_tops_1(sK0,sK1) ) ),
    inference(resolution,[],[f33,f25])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f26,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f186,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f27,f25,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f24,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f265,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X9,k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X8))
      | sP3(X9,X8,k2_pre_topc(sK0,sK1)) ) ),
    inference(superposition,[],[f64,f118])).

fof(f118,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),X0))) ),
    inference(unit_resulting_resolution,[],[f113,f55])).

fof(f113,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f27,f25,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f1030,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(sK1,sK1,k1_setfam_1(k2_tarski(X1,X2))),X2)
      | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(resolution,[],[f884,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f682,plain,(
    k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f27,f25,f141])).

fof(f141,plain,(
    ! [X2,X3] :
      ( k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k2_tops_1(X2,X3)))) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,(
    ! [X2,X3] :
      ( k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k2_tops_1(X2,X3)))) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f30,f55])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f328,plain,(
    sK1 != k1_tops_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f27,f26,f27,f236,f25,f320,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X0,X2) != X2
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f236,plain,(
    m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f27,f182,f36])).

fof(f182,plain,(
    m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f27,f116,f36])).

fof(f116,plain,(
    m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f27,f115,f36])).

fof(f115,plain,(
    m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f27,f114,f36])).

fof(f114,plain,(
    m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f27,f113,f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:58:24 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (27890)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.50  % (27898)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (27914)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.52  % (27893)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (27894)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (27897)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (27910)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (27912)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (27895)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.53  % (27902)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.33/0.53  % (27904)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.33/0.53  % (27911)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.33/0.54  % (27904)Refutation not found, incomplete strategy% (27904)------------------------------
% 1.33/0.54  % (27904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (27915)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.33/0.54  % (27899)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.33/0.54  % (27904)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (27904)Memory used [KB]: 6140
% 1.33/0.54  % (27904)Time elapsed: 0.004 s
% 1.33/0.54  % (27904)------------------------------
% 1.33/0.54  % (27904)------------------------------
% 1.33/0.54  % (27892)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.54  % (27896)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.33/0.54  % (27918)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.33/0.54  % (27891)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.54  % (27903)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.55  % (27913)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.33/0.55  % (27906)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.33/0.55  % (27910)Refutation not found, incomplete strategy% (27910)------------------------------
% 1.33/0.55  % (27910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (27910)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (27910)Memory used [KB]: 1791
% 1.33/0.55  % (27910)Time elapsed: 0.135 s
% 1.33/0.55  % (27910)------------------------------
% 1.33/0.55  % (27910)------------------------------
% 1.33/0.55  % (27917)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.43/0.55  % (27889)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.43/0.55  % (27911)Refutation not found, incomplete strategy% (27911)------------------------------
% 1.43/0.55  % (27911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (27911)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (27911)Memory used [KB]: 10746
% 1.43/0.55  % (27911)Time elapsed: 0.134 s
% 1.43/0.55  % (27911)------------------------------
% 1.43/0.55  % (27911)------------------------------
% 1.43/0.55  % (27905)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.55  % (27906)Refutation not found, incomplete strategy% (27906)------------------------------
% 1.43/0.55  % (27906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (27908)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.55  % (27906)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (27906)Memory used [KB]: 10618
% 1.43/0.55  % (27906)Time elapsed: 0.111 s
% 1.43/0.55  % (27906)------------------------------
% 1.43/0.55  % (27906)------------------------------
% 1.43/0.55  % (27909)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.56  % (27907)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.56  % (27901)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.57  % (27916)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.43/0.58  % (27900)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.31/0.68  % (27930)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.31/0.68  % (27931)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.31/0.69  % (27934)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.31/0.69  % (27932)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.76/0.75  % (27913)Refutation found. Thanks to Tanya!
% 2.76/0.75  % SZS status Theorem for theBenchmark
% 2.76/0.75  % SZS output start Proof for theBenchmark
% 2.76/0.76  fof(f2309,plain,(
% 2.76/0.76    $false),
% 2.76/0.76    inference(global_subsumption,[],[f328,f2308])).
% 2.76/0.76  fof(f2308,plain,(
% 2.76/0.76    sK1 = k1_tops_1(sK0,sK1)),
% 2.76/0.76    inference(forward_demodulation,[],[f2280,f68])).
% 2.76/0.76  fof(f68,plain,(
% 2.76/0.76    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.76/0.76    inference(forward_demodulation,[],[f54,f53])).
% 2.76/0.76  fof(f53,plain,(
% 2.76/0.76    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 2.76/0.76    inference(definition_unfolding,[],[f28,f34])).
% 2.76/0.76  fof(f34,plain,(
% 2.76/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.76/0.76    inference(cnf_transformation,[],[f7])).
% 2.76/0.76  fof(f7,axiom,(
% 2.76/0.76    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.76/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.76/0.76  fof(f28,plain,(
% 2.76/0.76    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.76/0.76    inference(cnf_transformation,[],[f4])).
% 2.76/0.76  fof(f4,axiom,(
% 2.76/0.76    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.76/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.76/0.76  fof(f54,plain,(
% 2.76/0.76    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 2.76/0.76    inference(definition_unfolding,[],[f29,f52])).
% 2.76/0.76  fof(f52,plain,(
% 2.76/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.76/0.76    inference(definition_unfolding,[],[f35,f34])).
% 2.76/0.76  fof(f35,plain,(
% 2.76/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.76/0.76    inference(cnf_transformation,[],[f3])).
% 2.76/0.76  fof(f3,axiom,(
% 2.76/0.76    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.76/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.76/0.76  fof(f29,plain,(
% 2.76/0.76    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.76/0.76    inference(cnf_transformation,[],[f5])).
% 2.76/0.76  fof(f5,axiom,(
% 2.76/0.76    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.76/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.76/0.76  fof(f2280,plain,(
% 2.76/0.76    k5_xboole_0(sK1,k1_xboole_0) = k1_tops_1(sK0,sK1)),
% 2.76/0.76    inference(backward_demodulation,[],[f682,f2274])).
% 2.76/0.76  fof(f2274,plain,(
% 2.76/0.76    k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 2.76/0.76    inference(unit_resulting_resolution,[],[f2271,f983])).
% 2.76/0.76  fof(f983,plain,(
% 2.76/0.76    ( ! [X8,X9] : (sP5(sK2(sK1,sK1,k1_setfam_1(k2_tarski(X8,X9))),X9,X8) | k1_xboole_0 = k1_setfam_1(k2_tarski(X8,X9))) )),
% 2.76/0.76    inference(resolution,[],[f973,f66])).
% 2.76/0.76  fof(f66,plain,(
% 2.76/0.76    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1))) | sP5(X3,X1,X0)) )),
% 2.76/0.76    inference(equality_resolution,[],[f62])).
% 2.76/0.76  fof(f62,plain,(
% 2.76/0.76    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 2.76/0.76    inference(definition_unfolding,[],[f49,f34])).
% 2.76/0.76  fof(f49,plain,(
% 2.76/0.76    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.76/0.76    inference(cnf_transformation,[],[f1])).
% 2.76/0.76  fof(f1,axiom,(
% 2.76/0.76    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.76/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.76/0.76  fof(f973,plain,(
% 2.76/0.76    ( ! [X6] : (r2_hidden(sK2(sK1,sK1,X6),X6) | k1_xboole_0 = X6) )),
% 2.76/0.76    inference(resolution,[],[f857,f838])).
% 2.76/0.76  fof(f838,plain,(
% 2.76/0.76    ( ! [X5] : (~sP3(X5,sK1,sK1)) )),
% 2.76/0.76    inference(global_subsumption,[],[f83,f833])).
% 2.76/0.76  fof(f833,plain,(
% 2.76/0.76    ( ! [X5] : (r2_hidden(X5,k1_xboole_0) | ~sP3(X5,sK1,sK1)) )),
% 2.76/0.76    inference(superposition,[],[f129,f811])).
% 2.76/0.76  fof(f811,plain,(
% 2.76/0.76    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)),
% 2.76/0.76    inference(duplicate_literal_removal,[],[f801])).
% 2.76/0.76  fof(f801,plain,(
% 2.76/0.76    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)),
% 2.76/0.76    inference(resolution,[],[f755,f754])).
% 2.76/0.76  fof(f754,plain,(
% 2.76/0.76    ( ! [X0,X1] : (~r2_hidden(sK4(k1_xboole_0,X1,k7_subset_1(u1_struct_0(sK0),sK1,X0)),X0) | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,X0)) )),
% 2.76/0.76    inference(resolution,[],[f452,f40])).
% 2.76/0.76  fof(f40,plain,(
% 2.76/0.76    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 2.76/0.76    inference(cnf_transformation,[],[f2])).
% 2.76/0.76  fof(f2,axiom,(
% 2.76/0.76    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.76/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.76/0.76  fof(f452,plain,(
% 2.76/0.76    ( ! [X6,X5] : (sP3(sK4(k1_xboole_0,X6,k7_subset_1(u1_struct_0(sK0),sK1,X5)),X5,sK1) | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,X5)) )),
% 2.76/0.76    inference(resolution,[],[f172,f130])).
% 2.76/0.76  fof(f130,plain,(
% 2.76/0.76    ( ! [X4,X5] : (~r2_hidden(X5,k7_subset_1(u1_struct_0(sK0),sK1,X4)) | sP3(X5,X4,sK1)) )),
% 2.76/0.76    inference(superposition,[],[f64,f117])).
% 2.76/0.76  fof(f117,plain,(
% 2.76/0.76    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) )),
% 2.76/0.76    inference(unit_resulting_resolution,[],[f25,f55])).
% 2.76/0.76  fof(f55,plain,(
% 2.76/0.76    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.76/0.76    inference(definition_unfolding,[],[f37,f52])).
% 2.76/0.76  fof(f37,plain,(
% 2.76/0.76    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.76/0.76    inference(cnf_transformation,[],[f22])).
% 2.76/0.76  fof(f22,plain,(
% 2.76/0.76    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.76/0.76    inference(ennf_transformation,[],[f6])).
% 2.76/0.76  fof(f6,axiom,(
% 2.76/0.76    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.76/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.76/0.76  fof(f25,plain,(
% 2.76/0.76    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.76/0.76    inference(cnf_transformation,[],[f15])).
% 2.76/0.76  fof(f15,plain,(
% 2.76/0.76    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.76/0.76    inference(flattening,[],[f14])).
% 2.76/0.76  fof(f14,plain,(
% 2.76/0.76    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.76/0.76    inference(ennf_transformation,[],[f13])).
% 2.76/0.76  fof(f13,negated_conjecture,(
% 2.76/0.76    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.76/0.76    inference(negated_conjecture,[],[f12])).
% 2.76/0.76  fof(f12,conjecture,(
% 2.76/0.76    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.76/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 2.76/0.76  fof(f64,plain,(
% 2.76/0.76    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | sP3(X3,X1,X0)) )),
% 2.76/0.76    inference(equality_resolution,[],[f58])).
% 2.76/0.76  fof(f58,plain,(
% 2.76/0.76    ( ! [X2,X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 2.76/0.76    inference(definition_unfolding,[],[f42,f52])).
% 2.76/0.76  fof(f42,plain,(
% 2.76/0.76    ( ! [X2,X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.76/0.76    inference(cnf_transformation,[],[f2])).
% 2.76/0.76  fof(f172,plain,(
% 2.76/0.76    ( ! [X10,X9] : (r2_hidden(sK4(k1_xboole_0,X9,X10),X10) | k1_xboole_0 = X10) )),
% 2.76/0.76    inference(forward_demodulation,[],[f161,f156])).
% 2.76/0.76  fof(f156,plain,(
% 2.76/0.76    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) )),
% 2.76/0.76    inference(unit_resulting_resolution,[],[f83,f86,f61])).
% 2.76/0.76  fof(f61,plain,(
% 2.76/0.76    ( ! [X2,X0,X1] : (sP5(sK4(X0,X1,X2),X1,X0) | r2_hidden(sK4(X0,X1,X2),X2) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 2.76/0.76    inference(definition_unfolding,[],[f50,f34])).
% 2.76/0.76  fof(f50,plain,(
% 2.76/0.76    ( ! [X2,X0,X1] : (sP5(sK4(X0,X1,X2),X1,X0) | r2_hidden(sK4(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.76/0.76    inference(cnf_transformation,[],[f1])).
% 2.76/0.76  fof(f86,plain,(
% 2.76/0.76    ( ! [X0,X1] : (~sP5(X0,X1,k1_xboole_0)) )),
% 2.76/0.76    inference(unit_resulting_resolution,[],[f83,f46])).
% 2.76/0.76  fof(f46,plain,(
% 2.76/0.76    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 2.76/0.76    inference(cnf_transformation,[],[f1])).
% 2.76/0.76  fof(f161,plain,(
% 2.76/0.76    ( ! [X10,X9] : (r2_hidden(sK4(k1_xboole_0,X9,X10),X10) | k1_setfam_1(k2_tarski(k1_xboole_0,X9)) = X10) )),
% 2.76/0.76    inference(resolution,[],[f61,f86])).
% 2.76/0.76  fof(f755,plain,(
% 2.76/0.76    ( ! [X2,X3] : (r2_hidden(sK4(k1_xboole_0,X3,k7_subset_1(u1_struct_0(sK0),sK1,X2)),sK1) | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,X2)) )),
% 2.76/0.76    inference(resolution,[],[f452,f39])).
% 2.76/0.76  fof(f39,plain,(
% 2.76/0.76    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 2.76/0.76    inference(cnf_transformation,[],[f2])).
% 2.76/0.76  fof(f129,plain,(
% 2.76/0.76    ( ! [X2,X3] : (r2_hidden(X3,k7_subset_1(u1_struct_0(sK0),sK1,X2)) | ~sP3(X3,X2,sK1)) )),
% 2.76/0.76    inference(superposition,[],[f65,f117])).
% 2.76/0.76  fof(f65,plain,(
% 2.76/0.76    ( ! [X0,X3,X1] : (r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | ~sP3(X3,X1,X0)) )),
% 2.76/0.76    inference(equality_resolution,[],[f59])).
% 2.76/0.76  fof(f59,plain,(
% 2.76/0.76    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 2.76/0.76    inference(definition_unfolding,[],[f41,f52])).
% 2.76/0.76  fof(f41,plain,(
% 2.76/0.76    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.76/0.76    inference(cnf_transformation,[],[f2])).
% 2.76/0.76  fof(f83,plain,(
% 2.76/0.76    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.76/0.76    inference(global_subsumption,[],[f76,f81])).
% 2.76/0.76  fof(f81,plain,(
% 2.76/0.76    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 2.76/0.76    inference(resolution,[],[f80,f40])).
% 2.76/0.76  fof(f80,plain,(
% 2.76/0.76    ( ! [X0,X1] : (sP3(X1,k1_xboole_0,X0) | ~r2_hidden(X1,X0)) )),
% 2.76/0.76    inference(forward_demodulation,[],[f79,f68])).
% 2.76/0.76  fof(f79,plain,(
% 2.76/0.76    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,k1_xboole_0)) | sP3(X1,k1_xboole_0,X0)) )),
% 2.76/0.76    inference(superposition,[],[f64,f53])).
% 2.76/0.76  fof(f76,plain,(
% 2.76/0.76    ( ! [X2,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X2)) )),
% 2.76/0.76    inference(resolution,[],[f74,f46])).
% 2.76/0.76  fof(f74,plain,(
% 2.76/0.76    ( ! [X0,X1] : (sP5(X1,k1_xboole_0,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 2.76/0.76    inference(superposition,[],[f66,f53])).
% 2.76/0.76  fof(f857,plain,(
% 2.76/0.76    ( ! [X0] : (sP3(sK2(sK1,sK1,X0),sK1,sK1) | r2_hidden(sK2(sK1,sK1,X0),X0) | k1_xboole_0 = X0) )),
% 2.76/0.76    inference(superposition,[],[f845,f57])).
% 2.76/0.76  fof(f57,plain,(
% 2.76/0.76    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 | r2_hidden(sK2(X0,X1,X2),X2) | sP3(sK2(X0,X1,X2),X1,X0)) )),
% 2.76/0.76    inference(definition_unfolding,[],[f43,f52])).
% 2.76/0.76  fof(f43,plain,(
% 2.76/0.76    ( ! [X2,X0,X1] : (sP3(sK2(X0,X1,X2),X1,X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.76/0.76    inference(cnf_transformation,[],[f2])).
% 2.76/0.76  fof(f845,plain,(
% 2.76/0.76    k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK1)))),
% 2.76/0.76    inference(unit_resulting_resolution,[],[f83,f838,f57])).
% 2.76/0.76  fof(f2271,plain,(
% 2.76/0.76    ( ! [X6] : (~sP5(X6,k2_tops_1(sK0,sK1),sK1)) )),
% 2.76/0.76    inference(global_subsumption,[],[f328,f2270])).
% 2.76/0.76  fof(f2270,plain,(
% 2.76/0.76    ( ! [X6] : (sK1 = k1_tops_1(sK0,sK1) | ~sP5(X6,k2_tops_1(sK0,sK1),sK1)) )),
% 2.76/0.76    inference(forward_demodulation,[],[f2253,f68])).
% 2.76/0.76  fof(f2253,plain,(
% 2.76/0.76    ( ! [X6] : (k5_xboole_0(sK1,k1_xboole_0) = k1_tops_1(sK0,sK1) | ~sP5(X6,k2_tops_1(sK0,sK1),sK1)) )),
% 2.76/0.76    inference(superposition,[],[f682,f2214])).
% 2.76/0.76  fof(f2214,plain,(
% 2.76/0.76    ( ! [X2] : (k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~sP5(X2,k2_tops_1(sK0,sK1),sK1)) )),
% 2.76/0.76    inference(resolution,[],[f2194,f172])).
% 2.76/0.76  fof(f2194,plain,(
% 2.76/0.76    ( ! [X0,X1] : (~r2_hidden(X0,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) | ~sP5(X1,k2_tops_1(sK0,sK1),sK1)) )),
% 2.76/0.76    inference(resolution,[],[f2181,f67])).
% 2.76/0.76  fof(f67,plain,(
% 2.76/0.76    ( ! [X0,X3,X1] : (r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1))) | ~sP5(X3,X1,X0)) )),
% 2.76/0.76    inference(equality_resolution,[],[f63])).
% 2.76/0.76  fof(f63,plain,(
% 2.76/0.76    ( ! [X2,X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 2.76/0.76    inference(definition_unfolding,[],[f48,f34])).
% 2.76/0.76  fof(f48,plain,(
% 2.76/0.76    ( ! [X2,X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.76/0.76    inference(cnf_transformation,[],[f1])).
% 2.76/0.76  fof(f2181,plain,(
% 2.76/0.76    ( ! [X2,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) | ~r2_hidden(X1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))) )),
% 2.76/0.76    inference(resolution,[],[f1050,f1031])).
% 2.76/0.76  fof(f1031,plain,(
% 2.76/0.76    ( ! [X4,X5,X3] : (r2_hidden(sK2(sK1,sK1,k1_setfam_1(k2_tarski(X4,X5))),X4) | ~r2_hidden(X3,k1_setfam_1(k2_tarski(X4,X5)))) )),
% 2.76/0.76    inference(resolution,[],[f884,f46])).
% 2.76/0.76  fof(f884,plain,(
% 2.76/0.76    ( ! [X14,X15,X16] : (sP5(sK2(sK1,sK1,k1_setfam_1(k2_tarski(X15,X16))),X16,X15) | ~r2_hidden(X14,k1_setfam_1(k2_tarski(X15,X16)))) )),
% 2.76/0.76    inference(resolution,[],[f855,f66])).
% 2.93/0.78  fof(f855,plain,(
% 2.93/0.78    ( ! [X2,X1] : (r2_hidden(sK2(sK1,sK1,X2),X2) | ~r2_hidden(X1,X2)) )),
% 2.93/0.78    inference(global_subsumption,[],[f838,f848])).
% 2.93/0.78  fof(f848,plain,(
% 2.93/0.78    ( ! [X2,X1] : (sP3(X1,sK1,sK1) | r2_hidden(sK2(sK1,sK1,X2),X2) | ~r2_hidden(X1,X2)) )),
% 2.93/0.78    inference(resolution,[],[f838,f252])).
% 2.93/0.78  fof(f252,plain,(
% 2.93/0.78    ( ! [X14,X12,X15,X13] : (sP3(sK2(X12,X13,X14),X13,X12) | sP3(X15,X13,X12) | r2_hidden(sK2(X12,X13,X14),X14) | ~r2_hidden(X15,X14)) )),
% 2.93/0.78    inference(superposition,[],[f64,f57])).
% 2.93/0.78  fof(f1050,plain,(
% 2.93/0.78    ( ! [X28,X29] : (~r2_hidden(sK2(sK1,sK1,k1_setfam_1(k2_tarski(X29,k2_tops_1(sK0,sK1)))),sK1) | ~r2_hidden(X28,k1_setfam_1(k2_tarski(X29,k2_tops_1(sK0,sK1))))) )),
% 2.93/0.78    inference(resolution,[],[f1030,f374])).
% 2.93/0.78  fof(f374,plain,(
% 2.93/0.78    ( ! [X1] : (~r2_hidden(X1,k2_tops_1(sK0,sK1)) | ~r2_hidden(X1,sK1)) )),
% 2.93/0.78    inference(resolution,[],[f371,f40])).
% 2.93/0.78  fof(f371,plain,(
% 2.93/0.78    ( ! [X0] : (sP3(X0,sK1,k2_pre_topc(sK0,sK1)) | ~r2_hidden(X0,k2_tops_1(sK0,sK1))) )),
% 2.93/0.78    inference(superposition,[],[f265,f321])).
% 2.93/0.78  fof(f321,plain,(
% 2.93/0.78    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.93/0.78    inference(unit_resulting_resolution,[],[f320,f23])).
% 2.93/0.78  fof(f23,plain,(
% 2.93/0.78    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 2.93/0.78    inference(cnf_transformation,[],[f15])).
% 2.93/0.78  fof(f320,plain,(
% 2.93/0.78    ~v3_pre_topc(sK1,sK0)),
% 2.93/0.78    inference(global_subsumption,[],[f24,f315])).
% 2.93/0.78  fof(f315,plain,(
% 2.93/0.78    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.93/0.78    inference(superposition,[],[f186,f311])).
% 2.93/0.78  fof(f311,plain,(
% 2.93/0.78    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.93/0.78    inference(global_subsumption,[],[f27,f26,f302])).
% 2.93/0.78  fof(f302,plain,(
% 2.93/0.78    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v3_pre_topc(sK1,sK0) | sK1 = k1_tops_1(sK0,sK1)),
% 2.93/0.78    inference(resolution,[],[f285,f25])).
% 2.93/0.78  fof(f285,plain,(
% 2.93/0.78    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v3_pre_topc(sK1,sK0) | sK1 = k1_tops_1(sK0,sK1)) )),
% 2.93/0.78    inference(global_subsumption,[],[f27,f276])).
% 2.93/0.78  fof(f276,plain,(
% 2.93/0.78    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_pre_topc(sK1,sK0) | sK1 = k1_tops_1(sK0,sK1)) )),
% 2.93/0.78    inference(resolution,[],[f33,f25])).
% 2.93/0.78  fof(f33,plain,(
% 2.93/0.78    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3) )),
% 2.93/0.78    inference(cnf_transformation,[],[f19])).
% 2.93/0.78  fof(f19,plain,(
% 2.93/0.78    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.93/0.78    inference(flattening,[],[f18])).
% 2.93/0.78  fof(f18,plain,(
% 2.93/0.78    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.93/0.78    inference(ennf_transformation,[],[f10])).
% 2.93/0.78  fof(f10,axiom,(
% 2.93/0.78    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.93/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 2.93/0.78  fof(f26,plain,(
% 2.93/0.78    v2_pre_topc(sK0)),
% 2.93/0.78    inference(cnf_transformation,[],[f15])).
% 2.93/0.78  fof(f27,plain,(
% 2.93/0.78    l1_pre_topc(sK0)),
% 2.93/0.78    inference(cnf_transformation,[],[f15])).
% 2.93/0.78  fof(f186,plain,(
% 2.93/0.78    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.93/0.78    inference(unit_resulting_resolution,[],[f27,f25,f31])).
% 2.93/0.78  fof(f31,plain,(
% 2.93/0.78    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.93/0.78    inference(cnf_transformation,[],[f17])).
% 2.93/0.78  fof(f17,plain,(
% 2.93/0.78    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.93/0.78    inference(ennf_transformation,[],[f9])).
% 2.93/0.78  fof(f9,axiom,(
% 2.93/0.78    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.93/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 2.93/0.78  fof(f24,plain,(
% 2.93/0.78    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.93/0.78    inference(cnf_transformation,[],[f15])).
% 2.93/0.78  fof(f265,plain,(
% 2.93/0.78    ( ! [X8,X9] : (~r2_hidden(X9,k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X8)) | sP3(X9,X8,k2_pre_topc(sK0,sK1))) )),
% 2.93/0.78    inference(superposition,[],[f64,f118])).
% 2.93/0.78  fof(f118,plain,(
% 2.93/0.78    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),X0)))) )),
% 2.93/0.78    inference(unit_resulting_resolution,[],[f113,f55])).
% 2.93/0.78  fof(f113,plain,(
% 2.93/0.78    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.93/0.78    inference(unit_resulting_resolution,[],[f27,f25,f36])).
% 2.93/0.78  fof(f36,plain,(
% 2.93/0.78    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.93/0.78    inference(cnf_transformation,[],[f21])).
% 2.93/0.78  fof(f21,plain,(
% 2.93/0.78    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.93/0.78    inference(flattening,[],[f20])).
% 2.93/0.78  fof(f20,plain,(
% 2.93/0.78    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.93/0.78    inference(ennf_transformation,[],[f8])).
% 2.93/0.78  fof(f8,axiom,(
% 2.93/0.78    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.93/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.93/0.78  fof(f1030,plain,(
% 2.93/0.78    ( ! [X2,X0,X1] : (r2_hidden(sK2(sK1,sK1,k1_setfam_1(k2_tarski(X1,X2))),X2) | ~r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 2.93/0.78    inference(resolution,[],[f884,f47])).
% 2.93/0.78  fof(f47,plain,(
% 2.93/0.78    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 2.93/0.78    inference(cnf_transformation,[],[f1])).
% 2.93/0.78  fof(f682,plain,(
% 2.93/0.78    k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))),
% 2.93/0.78    inference(unit_resulting_resolution,[],[f27,f25,f141])).
% 2.93/0.78  fof(f141,plain,(
% 2.93/0.78    ( ! [X2,X3] : (k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k2_tops_1(X2,X3)))) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 2.93/0.78    inference(duplicate_literal_removal,[],[f137])).
% 2.93/0.78  fof(f137,plain,(
% 2.93/0.78    ( ! [X2,X3] : (k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k2_tops_1(X2,X3)))) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 2.93/0.78    inference(superposition,[],[f30,f55])).
% 2.93/0.78  fof(f30,plain,(
% 2.93/0.78    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.93/0.78    inference(cnf_transformation,[],[f16])).
% 2.93/0.78  fof(f16,plain,(
% 2.93/0.78    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.93/0.78    inference(ennf_transformation,[],[f11])).
% 2.93/0.78  fof(f11,axiom,(
% 2.93/0.78    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.93/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.93/0.78  fof(f328,plain,(
% 2.93/0.78    sK1 != k1_tops_1(sK0,sK1)),
% 2.93/0.78    inference(unit_resulting_resolution,[],[f27,f26,f27,f236,f25,f320,f32])).
% 2.93/0.78  fof(f32,plain,(
% 2.93/0.78    ( ! [X2,X0,X3,X1] : (k1_tops_1(X0,X2) != X2 | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X0) | v3_pre_topc(X2,X0)) )),
% 2.93/0.78    inference(cnf_transformation,[],[f19])).
% 2.93/0.78  fof(f236,plain,(
% 2.93/0.78    m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.93/0.78    inference(unit_resulting_resolution,[],[f27,f182,f36])).
% 2.93/0.78  fof(f182,plain,(
% 2.93/0.78    m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.93/0.78    inference(unit_resulting_resolution,[],[f27,f116,f36])).
% 2.93/0.78  fof(f116,plain,(
% 2.93/0.78    m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.93/0.78    inference(unit_resulting_resolution,[],[f27,f115,f36])).
% 2.93/0.78  fof(f115,plain,(
% 2.93/0.78    m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.93/0.78    inference(unit_resulting_resolution,[],[f27,f114,f36])).
% 2.93/0.78  fof(f114,plain,(
% 2.93/0.78    m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.93/0.78    inference(unit_resulting_resolution,[],[f27,f113,f36])).
% 2.93/0.78  % SZS output end Proof for theBenchmark
% 2.93/0.78  % (27913)------------------------------
% 2.93/0.78  % (27913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.93/0.78  % (27913)Termination reason: Refutation
% 2.93/0.78  
% 2.93/0.78  % (27913)Memory used [KB]: 9210
% 2.93/0.78  % (27913)Time elapsed: 0.347 s
% 2.93/0.78  % (27913)------------------------------
% 2.93/0.78  % (27913)------------------------------
% 2.93/0.78  % (27888)Success in time 0.41 s
%------------------------------------------------------------------------------
