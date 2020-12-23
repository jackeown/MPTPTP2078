%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:12 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 332 expanded)
%              Number of leaves         :   11 (  79 expanded)
%              Depth                    :   20
%              Number of atoms          :  183 ( 854 expanded)
%              Number of equality atoms :   14 (  65 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1414,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1413,f101])).

fof(f101,plain,(
    ! [X2] : r1_tarski(k4_xboole_0(sK1,X2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f97,f44])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f97,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k4_xboole_0(sK1,X2))
      | r1_tarski(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f71,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK1)
      | ~ r1_tarski(X1,X0)
      | r1_tarski(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f68,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f68,plain,(
    ! [X10] :
      ( r1_tarski(X10,u1_struct_0(sK0))
      | ~ r1_tarski(X10,sK1) ) ),
    inference(resolution,[],[f43,f47])).

fof(f47,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f38,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1413,plain,(
    ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f1412,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1412,plain,(
    ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f1411,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f1411,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1410,f32])).

fof(f1410,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1409,f27])).

fof(f1409,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f1408,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f1408,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1407,f676])).

fof(f676,plain,(
    r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    inference(superposition,[],[f437,f477])).

fof(f477,plain,(
    ! [X0] : k4_xboole_0(X0,k1_tops_1(sK0,k4_xboole_0(sK1,X0))) = X0 ),
    inference(resolution,[],[f470,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f113,f44])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f60,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f60,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k4_xboole_0(X1,X2))
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f36,f32])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f470,plain,(
    ! [X1] : r1_xboole_0(X1,k1_tops_1(sK0,k4_xboole_0(sK1,X1))) ),
    inference(resolution,[],[f346,f171])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k4_xboole_0(X1,X0))
      | r1_xboole_0(X0,X2) ) ),
    inference(superposition,[],[f167,f118])).

fof(f118,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k4_xboole_0(X10,X9)) = X9 ),
    inference(resolution,[],[f114,f55])).

fof(f55,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f52,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f52,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f41,f44])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f167,plain,(
    ! [X4,X5,X3] :
      ( r1_xboole_0(k4_xboole_0(X5,X4),X3)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f124,f33])).

fof(f124,plain,(
    ! [X6,X7,X5] :
      ( r1_xboole_0(X7,k4_xboole_0(X6,X5))
      | ~ r1_tarski(X7,X5) ) ),
    inference(superposition,[],[f41,f118])).

fof(f346,plain,(
    ! [X13] : r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X13)),k4_xboole_0(sK1,X13)) ),
    inference(resolution,[],[f314,f101])).

fof(f314,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f300,f37])).

fof(f300,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f30,f29])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f437,plain,(
    ! [X1] : r1_xboole_0(X1,k1_tops_1(sK0,k4_xboole_0(sK2,X1))) ),
    inference(resolution,[],[f341,f171])).

fof(f341,plain,(
    ! [X2] : r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK2,X2)),k4_xboole_0(sK2,X2)) ),
    inference(resolution,[],[f314,f88])).

fof(f88,plain,(
    ! [X2] : r1_tarski(k4_xboole_0(sK2,X2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f84,f44])).

fof(f84,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k4_xboole_0(sK2,X2))
      | r1_tarski(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f69,f32])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK2)
      | ~ r1_tarski(X1,X0)
      | r1_tarski(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f67,f43])).

fof(f67,plain,(
    ! [X9] :
      ( r1_tarski(X9,u1_struct_0(sK0))
      | ~ r1_tarski(X9,sK2) ) ),
    inference(resolution,[],[f43,f46])).

fof(f46,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f38,f25])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f1407,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f1098,f42])).

fof(f1098,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f428,f1077])).

fof(f1077,plain,(
    ! [X63] : k4_xboole_0(k1_tops_1(sK0,sK1),X63) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X63) ),
    inference(resolution,[],[f427,f380])).

fof(f380,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f318,f44])).

fof(f318,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
      | r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f313,f71])).

fof(f313,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f300,f27])).

fof(f427,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X4)
      | k4_xboole_0(X2,X3) = k7_subset_1(X4,X2,X3) ) ),
    inference(resolution,[],[f39,f37])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f428,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f26,f426])).

fof(f426,plain,(
    ! [X1] : k4_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,X1) ),
    inference(resolution,[],[f39,f27])).

fof(f26,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:40:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (23624)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (23622)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (23621)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (23625)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (23639)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (23627)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (23641)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (23633)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (23620)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (23632)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (23623)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (23629)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (23635)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (23640)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (23642)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (23637)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (23619)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.54  % (23634)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (23638)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.54  % (23630)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.55  % (23626)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.55  % (23645)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.55  % (23628)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.55  % (23636)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.52/0.56  % (23643)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.52/0.57  % (23644)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.66/0.62  % (23639)Refutation found. Thanks to Tanya!
% 1.66/0.62  % SZS status Theorem for theBenchmark
% 1.66/0.62  % SZS output start Proof for theBenchmark
% 1.66/0.62  fof(f1414,plain,(
% 1.66/0.62    $false),
% 1.66/0.62    inference(subsumption_resolution,[],[f1413,f101])).
% 1.66/0.62  fof(f101,plain,(
% 1.66/0.62    ( ! [X2] : (r1_tarski(k4_xboole_0(sK1,X2),u1_struct_0(sK0))) )),
% 1.66/0.62    inference(resolution,[],[f97,f44])).
% 1.66/0.62  fof(f44,plain,(
% 1.66/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.66/0.62    inference(equality_resolution,[],[f35])).
% 1.66/0.62  fof(f35,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.66/0.62    inference(cnf_transformation,[],[f2])).
% 1.66/0.62  fof(f2,axiom,(
% 1.66/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.66/0.62  fof(f97,plain,(
% 1.66/0.62    ( ! [X2,X1] : (~r1_tarski(X1,k4_xboole_0(sK1,X2)) | r1_tarski(X1,u1_struct_0(sK0))) )),
% 1.66/0.62    inference(resolution,[],[f71,f32])).
% 1.66/0.62  fof(f32,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f5])).
% 1.66/0.62  fof(f5,axiom,(
% 1.66/0.62    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.66/0.62  fof(f71,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~r1_tarski(X0,sK1) | ~r1_tarski(X1,X0) | r1_tarski(X1,u1_struct_0(sK0))) )),
% 1.66/0.62    inference(resolution,[],[f68,f43])).
% 1.66/0.62  fof(f43,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f24])).
% 1.66/0.62  fof(f24,plain,(
% 1.66/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.66/0.62    inference(flattening,[],[f23])).
% 1.66/0.62  fof(f23,plain,(
% 1.66/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.66/0.62    inference(ennf_transformation,[],[f4])).
% 1.66/0.62  fof(f4,axiom,(
% 1.66/0.62    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.66/0.62  fof(f68,plain,(
% 1.66/0.62    ( ! [X10] : (r1_tarski(X10,u1_struct_0(sK0)) | ~r1_tarski(X10,sK1)) )),
% 1.66/0.62    inference(resolution,[],[f43,f47])).
% 1.66/0.62  fof(f47,plain,(
% 1.66/0.62    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.66/0.62    inference(resolution,[],[f38,f27])).
% 1.66/0.62  fof(f27,plain,(
% 1.66/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.62    inference(cnf_transformation,[],[f14])).
% 1.66/0.62  fof(f14,plain,(
% 1.66/0.62    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.66/0.62    inference(flattening,[],[f13])).
% 1.66/0.62  fof(f13,plain,(
% 1.66/0.62    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.66/0.62    inference(ennf_transformation,[],[f12])).
% 1.66/0.62  fof(f12,negated_conjecture,(
% 1.66/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.66/0.62    inference(negated_conjecture,[],[f11])).
% 1.66/0.62  fof(f11,conjecture,(
% 1.66/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).
% 1.66/0.62  fof(f38,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f8])).
% 1.66/0.62  fof(f8,axiom,(
% 1.66/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.66/0.62  fof(f1413,plain,(
% 1.66/0.62    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))),
% 1.66/0.62    inference(resolution,[],[f1412,f37])).
% 1.66/0.62  fof(f37,plain,(
% 1.66/0.62    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f8])).
% 1.66/0.62  fof(f1412,plain,(
% 1.66/0.62    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.62    inference(subsumption_resolution,[],[f1411,f29])).
% 1.66/0.62  fof(f29,plain,(
% 1.66/0.62    l1_pre_topc(sK0)),
% 1.66/0.62    inference(cnf_transformation,[],[f14])).
% 1.66/0.62  fof(f1411,plain,(
% 1.66/0.62    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.66/0.62    inference(subsumption_resolution,[],[f1410,f32])).
% 1.66/0.62  fof(f1410,plain,(
% 1.66/0.62    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~l1_pre_topc(sK0)),
% 1.66/0.62    inference(subsumption_resolution,[],[f1409,f27])).
% 1.66/0.62  fof(f1409,plain,(
% 1.66/0.62    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~l1_pre_topc(sK0)),
% 1.66/0.62    inference(resolution,[],[f1408,f31])).
% 1.66/0.62  fof(f31,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f17])).
% 1.66/0.62  fof(f17,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.66/0.62    inference(flattening,[],[f16])).
% 1.66/0.62  fof(f16,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.66/0.62    inference(ennf_transformation,[],[f10])).
% 1.66/0.62  fof(f10,axiom,(
% 1.66/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 1.66/0.62  fof(f1408,plain,(
% 1.66/0.62    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))),
% 1.66/0.62    inference(subsumption_resolution,[],[f1407,f676])).
% 1.66/0.62  fof(f676,plain,(
% 1.66/0.62    r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))),
% 1.66/0.62    inference(superposition,[],[f437,f477])).
% 1.66/0.62  fof(f477,plain,(
% 1.66/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_tops_1(sK0,k4_xboole_0(sK1,X0))) = X0) )),
% 1.66/0.62    inference(resolution,[],[f470,f114])).
% 1.66/0.62  fof(f114,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f113,f44])).
% 1.66/0.62  fof(f113,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1) | ~r1_tarski(X0,X0)) )),
% 1.66/0.62    inference(resolution,[],[f60,f42])).
% 1.66/0.62  fof(f42,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f22])).
% 1.66/0.62  fof(f22,plain,(
% 1.66/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 1.66/0.62    inference(flattening,[],[f21])).
% 1.66/0.62  fof(f21,plain,(
% 1.66/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.66/0.62    inference(ennf_transformation,[],[f6])).
% 1.66/0.62  fof(f6,axiom,(
% 1.66/0.62    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 1.66/0.62  fof(f60,plain,(
% 1.66/0.62    ( ! [X2,X1] : (~r1_tarski(X1,k4_xboole_0(X1,X2)) | k4_xboole_0(X1,X2) = X1) )),
% 1.66/0.62    inference(resolution,[],[f36,f32])).
% 1.66/0.62  fof(f36,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.66/0.62    inference(cnf_transformation,[],[f2])).
% 1.66/0.62  fof(f470,plain,(
% 1.66/0.62    ( ! [X1] : (r1_xboole_0(X1,k1_tops_1(sK0,k4_xboole_0(sK1,X1)))) )),
% 1.66/0.62    inference(resolution,[],[f346,f171])).
% 1.66/0.62  fof(f171,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X2,k4_xboole_0(X1,X0)) | r1_xboole_0(X0,X2)) )),
% 1.66/0.62    inference(superposition,[],[f167,f118])).
% 1.66/0.62  fof(f118,plain,(
% 1.66/0.62    ( ! [X10,X9] : (k4_xboole_0(X9,k4_xboole_0(X10,X9)) = X9) )),
% 1.66/0.62    inference(resolution,[],[f114,f55])).
% 1.66/0.62  fof(f55,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.66/0.63    inference(resolution,[],[f52,f33])).
% 1.66/0.63  fof(f33,plain,(
% 1.66/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.66/0.63    inference(cnf_transformation,[],[f18])).
% 1.66/0.63  fof(f18,plain,(
% 1.66/0.63    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.66/0.63    inference(ennf_transformation,[],[f1])).
% 1.66/0.63  fof(f1,axiom,(
% 1.66/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.66/0.63  fof(f52,plain,(
% 1.66/0.63    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.66/0.63    inference(resolution,[],[f41,f44])).
% 1.66/0.63  fof(f41,plain,(
% 1.66/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.66/0.63    inference(cnf_transformation,[],[f20])).
% 1.66/0.63  fof(f20,plain,(
% 1.66/0.63    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.66/0.63    inference(ennf_transformation,[],[f3])).
% 1.66/0.63  fof(f3,axiom,(
% 1.66/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.66/0.63  fof(f167,plain,(
% 1.66/0.63    ( ! [X4,X5,X3] : (r1_xboole_0(k4_xboole_0(X5,X4),X3) | ~r1_tarski(X3,X4)) )),
% 1.66/0.63    inference(resolution,[],[f124,f33])).
% 1.66/0.63  fof(f124,plain,(
% 1.66/0.63    ( ! [X6,X7,X5] : (r1_xboole_0(X7,k4_xboole_0(X6,X5)) | ~r1_tarski(X7,X5)) )),
% 1.66/0.63    inference(superposition,[],[f41,f118])).
% 1.66/0.63  fof(f346,plain,(
% 1.66/0.63    ( ! [X13] : (r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X13)),k4_xboole_0(sK1,X13))) )),
% 1.66/0.63    inference(resolution,[],[f314,f101])).
% 1.66/0.63  fof(f314,plain,(
% 1.66/0.63    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 1.66/0.63    inference(resolution,[],[f300,f37])).
% 1.66/0.63  fof(f300,plain,(
% 1.66/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 1.66/0.63    inference(resolution,[],[f30,f29])).
% 1.66/0.63  fof(f30,plain,(
% 1.66/0.63    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.66/0.63    inference(cnf_transformation,[],[f15])).
% 1.66/0.63  fof(f15,plain,(
% 1.66/0.63    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.66/0.63    inference(ennf_transformation,[],[f9])).
% 1.66/0.63  fof(f9,axiom,(
% 1.66/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.66/0.63  fof(f437,plain,(
% 1.66/0.63    ( ! [X1] : (r1_xboole_0(X1,k1_tops_1(sK0,k4_xboole_0(sK2,X1)))) )),
% 1.66/0.63    inference(resolution,[],[f341,f171])).
% 1.66/0.63  fof(f341,plain,(
% 1.66/0.63    ( ! [X2] : (r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK2,X2)),k4_xboole_0(sK2,X2))) )),
% 1.66/0.63    inference(resolution,[],[f314,f88])).
% 1.66/0.63  fof(f88,plain,(
% 1.66/0.63    ( ! [X2] : (r1_tarski(k4_xboole_0(sK2,X2),u1_struct_0(sK0))) )),
% 1.66/0.63    inference(resolution,[],[f84,f44])).
% 1.66/0.63  fof(f84,plain,(
% 1.66/0.63    ( ! [X2,X1] : (~r1_tarski(X1,k4_xboole_0(sK2,X2)) | r1_tarski(X1,u1_struct_0(sK0))) )),
% 1.66/0.63    inference(resolution,[],[f69,f32])).
% 1.66/0.63  fof(f69,plain,(
% 1.66/0.63    ( ! [X0,X1] : (~r1_tarski(X0,sK2) | ~r1_tarski(X1,X0) | r1_tarski(X1,u1_struct_0(sK0))) )),
% 1.66/0.63    inference(resolution,[],[f67,f43])).
% 1.66/0.63  fof(f67,plain,(
% 1.66/0.63    ( ! [X9] : (r1_tarski(X9,u1_struct_0(sK0)) | ~r1_tarski(X9,sK2)) )),
% 1.66/0.63    inference(resolution,[],[f43,f46])).
% 1.66/0.63  fof(f46,plain,(
% 1.66/0.63    r1_tarski(sK2,u1_struct_0(sK0))),
% 1.66/0.63    inference(resolution,[],[f38,f25])).
% 1.66/0.63  fof(f25,plain,(
% 1.66/0.63    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.63    inference(cnf_transformation,[],[f14])).
% 1.66/0.63  fof(f1407,plain,(
% 1.66/0.63    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))),
% 1.66/0.63    inference(resolution,[],[f1098,f42])).
% 1.66/0.63  fof(f1098,plain,(
% 1.66/0.63    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.66/0.63    inference(backward_demodulation,[],[f428,f1077])).
% 1.66/0.63  fof(f1077,plain,(
% 1.66/0.63    ( ! [X63] : (k4_xboole_0(k1_tops_1(sK0,sK1),X63) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X63)) )),
% 1.66/0.63    inference(resolution,[],[f427,f380])).
% 1.66/0.63  fof(f380,plain,(
% 1.66/0.63    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 1.66/0.63    inference(resolution,[],[f318,f44])).
% 1.66/0.63  fof(f318,plain,(
% 1.66/0.63    ( ! [X0] : (~r1_tarski(X0,k1_tops_1(sK0,sK1)) | r1_tarski(X0,u1_struct_0(sK0))) )),
% 1.66/0.63    inference(resolution,[],[f313,f71])).
% 1.66/0.63  fof(f313,plain,(
% 1.66/0.63    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.66/0.63    inference(resolution,[],[f300,f27])).
% 1.66/0.63  fof(f427,plain,(
% 1.66/0.63    ( ! [X4,X2,X3] : (~r1_tarski(X2,X4) | k4_xboole_0(X2,X3) = k7_subset_1(X4,X2,X3)) )),
% 1.66/0.63    inference(resolution,[],[f39,f37])).
% 1.66/0.63  fof(f39,plain,(
% 1.66/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 1.66/0.63    inference(cnf_transformation,[],[f19])).
% 1.66/0.63  fof(f19,plain,(
% 1.66/0.63    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.66/0.63    inference(ennf_transformation,[],[f7])).
% 1.66/0.63  fof(f7,axiom,(
% 1.66/0.63    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.66/0.63  fof(f428,plain,(
% 1.66/0.63    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.66/0.63    inference(backward_demodulation,[],[f26,f426])).
% 1.66/0.63  fof(f426,plain,(
% 1.66/0.63    ( ! [X1] : (k4_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,X1)) )),
% 1.66/0.63    inference(resolution,[],[f39,f27])).
% 1.66/0.63  fof(f26,plain,(
% 1.66/0.63    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.66/0.63    inference(cnf_transformation,[],[f14])).
% 1.66/0.63  % SZS output end Proof for theBenchmark
% 1.66/0.63  % (23639)------------------------------
% 1.66/0.63  % (23639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.63  % (23639)Termination reason: Refutation
% 1.66/0.63  
% 1.66/0.63  % (23639)Memory used [KB]: 2686
% 1.66/0.63  % (23639)Time elapsed: 0.208 s
% 1.66/0.63  % (23639)------------------------------
% 1.66/0.63  % (23639)------------------------------
% 1.66/0.63  % (23618)Success in time 0.264 s
%------------------------------------------------------------------------------
