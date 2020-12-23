%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:52 EST 2020

% Result     : Theorem 11.73s
% Output     : Refutation 11.73s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 223 expanded)
%              Number of leaves         :   16 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  174 ( 654 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31380,plain,(
    $false ),
    inference(subsumption_resolution,[],[f31379,f5245])).

fof(f5245,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f38,f41,f36,f5176,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f5176,plain,(
    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f5131,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f5131,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f5124,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f5124,plain,(
    r1_tarski(k2_xboole_0(sK2,sK1),u1_struct_0(sK0)) ),
    inference(superposition,[],[f3094,f84])).

fof(f84,plain,(
    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f69,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f69,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_1)).

fof(f3094,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f620,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f620,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k2_xboole_0(X0,sK1),X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f70,f233,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f233,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) ),
    inference(unit_resulting_resolution,[],[f57,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
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

fof(f70,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f51])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f31379,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f31378,f43])).

fof(f31378,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(forward_demodulation,[],[f31332,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f31332,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) ),
    inference(backward_demodulation,[],[f528,f31331])).

fof(f31331,plain,(
    ! [X0] : k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f31310,f1758])).

fof(f1758,plain,(
    ! [X0] : k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f1676,f1731])).

fof(f1731,plain,(
    ! [X0] : k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k4_xboole_0(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f34,f299,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f299,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f186,f50])).

fof(f186,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f42,f70,f55])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1676,plain,(
    ! [X0] : k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f38,f37,f34,f299,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_pre_topc)).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f31310,plain,(
    ! [X0] : k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f505,f1718,f56])).

fof(f1718,plain,(
    ! [X0] : m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f38,f299,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f505,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f38,f34,f46])).

fof(f528,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f527,f53])).

fof(f527,plain,(
    ~ r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f373,f525])).

fof(f525,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(unit_resulting_resolution,[],[f506,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f506,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f38,f36,f46])).

fof(f373,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f35,f372])).

fof(f372,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(unit_resulting_resolution,[],[f36,f52])).

fof(f35,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (16458)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (16456)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (16472)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (16452)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (16473)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (16453)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (16455)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (16460)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (16466)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (16462)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (16463)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (16457)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (16476)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (16461)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (16465)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (16474)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (16470)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.54  % (16454)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.54  % (16477)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.55  % (16469)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.55  % (16471)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.55  % (16464)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.56  % (16468)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.58  % (16475)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.58  % (16467)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.59  % (16459)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 4.04/0.91  % (16466)Time limit reached!
% 4.04/0.91  % (16466)------------------------------
% 4.04/0.91  % (16466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.04/0.92  % (16452)Time limit reached!
% 4.04/0.92  % (16452)------------------------------
% 4.04/0.92  % (16452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.04/0.92  % (16452)Termination reason: Time limit
% 4.04/0.92  
% 4.04/0.92  % (16452)Memory used [KB]: 14967
% 4.04/0.92  % (16452)Time elapsed: 0.505 s
% 4.04/0.92  % (16452)------------------------------
% 4.04/0.92  % (16452)------------------------------
% 4.37/0.92  % (16465)Time limit reached!
% 4.37/0.92  % (16465)------------------------------
% 4.37/0.92  % (16465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.37/0.92  % (16465)Termination reason: Time limit
% 4.37/0.92  
% 4.37/0.92  % (16465)Memory used [KB]: 9466
% 4.37/0.92  % (16465)Time elapsed: 0.507 s
% 4.37/0.92  % (16465)------------------------------
% 4.37/0.92  % (16465)------------------------------
% 4.37/0.93  % (16466)Termination reason: Time limit
% 4.37/0.93  % (16466)Termination phase: Saturation
% 4.37/0.93  
% 4.37/0.93  % (16466)Memory used [KB]: 7675
% 4.37/0.93  % (16466)Time elapsed: 0.500 s
% 4.37/0.93  % (16466)------------------------------
% 4.37/0.93  % (16466)------------------------------
% 5.18/1.02  % (16458)Time limit reached!
% 5.18/1.02  % (16458)------------------------------
% 5.18/1.02  % (16458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.18/1.04  % (16458)Termination reason: Time limit
% 5.18/1.04  % (16458)Termination phase: Saturation
% 5.18/1.04  
% 5.18/1.04  % (16458)Memory used [KB]: 13432
% 5.18/1.04  % (16458)Time elapsed: 0.600 s
% 5.18/1.04  % (16458)------------------------------
% 5.18/1.04  % (16458)------------------------------
% 7.50/1.33  % (16460)Time limit reached!
% 7.50/1.33  % (16460)------------------------------
% 7.50/1.33  % (16460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.50/1.33  % (16460)Termination reason: Time limit
% 7.50/1.33  % (16460)Termination phase: Saturation
% 7.50/1.33  
% 7.50/1.33  % (16460)Memory used [KB]: 12665
% 7.50/1.33  % (16460)Time elapsed: 0.900 s
% 7.50/1.33  % (16460)------------------------------
% 7.50/1.33  % (16460)------------------------------
% 7.97/1.42  % (16453)Time limit reached!
% 7.97/1.42  % (16453)------------------------------
% 7.97/1.42  % (16453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.97/1.42  % (16453)Termination reason: Time limit
% 7.97/1.42  % (16453)Termination phase: Saturation
% 7.97/1.42  
% 7.97/1.42  % (16453)Memory used [KB]: 23666
% 7.97/1.42  % (16453)Time elapsed: 1.0000 s
% 7.97/1.42  % (16453)------------------------------
% 7.97/1.42  % (16453)------------------------------
% 9.34/1.53  % (16456)Time limit reached!
% 9.34/1.53  % (16456)------------------------------
% 9.34/1.53  % (16456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.34/1.53  % (16456)Termination reason: Time limit
% 9.34/1.53  
% 9.34/1.53  % (16456)Memory used [KB]: 12409
% 9.34/1.53  % (16456)Time elapsed: 1.111 s
% 9.34/1.53  % (16456)------------------------------
% 9.34/1.53  % (16456)------------------------------
% 11.73/1.88  % (16459)Refutation found. Thanks to Tanya!
% 11.73/1.88  % SZS status Theorem for theBenchmark
% 11.73/1.88  % SZS output start Proof for theBenchmark
% 11.73/1.88  fof(f31380,plain,(
% 11.73/1.88    $false),
% 11.73/1.88    inference(subsumption_resolution,[],[f31379,f5245])).
% 11.73/1.88  fof(f5245,plain,(
% 11.73/1.88    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)))),
% 11.73/1.88    inference(unit_resulting_resolution,[],[f38,f41,f36,f5176,f39])).
% 11.73/1.88  fof(f39,plain,(
% 11.73/1.88    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 11.73/1.88    inference(cnf_transformation,[],[f21])).
% 11.73/1.88  fof(f21,plain,(
% 11.73/1.88    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.73/1.88    inference(flattening,[],[f20])).
% 11.73/1.88  fof(f20,plain,(
% 11.73/1.88    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.73/1.88    inference(ennf_transformation,[],[f14])).
% 11.73/1.88  fof(f14,axiom,(
% 11.73/1.88    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 11.73/1.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).
% 11.73/1.88  fof(f5176,plain,(
% 11.73/1.88    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.73/1.88    inference(unit_resulting_resolution,[],[f5131,f50])).
% 11.73/1.88  fof(f50,plain,(
% 11.73/1.88    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.73/1.88    inference(cnf_transformation,[],[f12])).
% 11.73/1.88  fof(f12,axiom,(
% 11.73/1.88    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.73/1.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 11.73/1.88  fof(f5131,plain,(
% 11.73/1.88    r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0))),
% 11.73/1.88    inference(forward_demodulation,[],[f5124,f43])).
% 11.73/1.88  fof(f43,plain,(
% 11.73/1.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.73/1.88    inference(cnf_transformation,[],[f1])).
% 11.73/1.88  fof(f1,axiom,(
% 11.73/1.88    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.73/1.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 11.73/1.88  fof(f5124,plain,(
% 11.73/1.88    r1_tarski(k2_xboole_0(sK2,sK1),u1_struct_0(sK0))),
% 11.73/1.88    inference(superposition,[],[f3094,f84])).
% 11.73/1.88  fof(f84,plain,(
% 11.73/1.88    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0))),
% 11.73/1.88    inference(unit_resulting_resolution,[],[f69,f45])).
% 11.73/1.88  fof(f45,plain,(
% 11.73/1.88    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 11.73/1.88    inference(cnf_transformation,[],[f24])).
% 11.73/1.88  fof(f24,plain,(
% 11.73/1.88    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.73/1.88    inference(ennf_transformation,[],[f3])).
% 11.73/1.88  fof(f3,axiom,(
% 11.73/1.88    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.73/1.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 11.73/1.88  fof(f69,plain,(
% 11.73/1.88    r1_tarski(sK2,u1_struct_0(sK0))),
% 11.73/1.88    inference(unit_resulting_resolution,[],[f34,f51])).
% 11.73/1.88  fof(f51,plain,(
% 11.73/1.88    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 11.73/1.88    inference(cnf_transformation,[],[f12])).
% 11.73/1.90  fof(f34,plain,(
% 11.73/1.90    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.73/1.90    inference(cnf_transformation,[],[f19])).
% 11.73/1.90  fof(f19,plain,(
% 11.73/1.90    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.73/1.90    inference(flattening,[],[f18])).
% 11.73/1.90  fof(f18,plain,(
% 11.73/1.90    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.73/1.90    inference(ennf_transformation,[],[f17])).
% 11.73/1.90  fof(f17,negated_conjecture,(
% 11.73/1.90    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 11.73/1.90    inference(negated_conjecture,[],[f16])).
% 11.73/1.90  fof(f16,conjecture,(
% 11.73/1.90    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 11.73/1.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_1)).
% 11.73/1.90  fof(f3094,plain,(
% 11.73/1.90    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,u1_struct_0(sK0)))) )),
% 11.73/1.90    inference(unit_resulting_resolution,[],[f620,f54])).
% 11.73/1.90  fof(f54,plain,(
% 11.73/1.90    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 11.73/1.90    inference(cnf_transformation,[],[f29])).
% 11.73/1.90  fof(f29,plain,(
% 11.73/1.90    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.73/1.90    inference(ennf_transformation,[],[f8])).
% 11.73/1.90  fof(f8,axiom,(
% 11.73/1.90    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.73/1.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 11.73/1.90  fof(f620,plain,(
% 11.73/1.90    ( ! [X0] : (r1_tarski(k4_xboole_0(k2_xboole_0(X0,sK1),X0),u1_struct_0(sK0))) )),
% 11.73/1.90    inference(unit_resulting_resolution,[],[f70,f233,f55])).
% 11.73/1.90  fof(f55,plain,(
% 11.73/1.90    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 11.73/1.90    inference(cnf_transformation,[],[f31])).
% 11.73/1.90  fof(f31,plain,(
% 11.73/1.90    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.73/1.90    inference(flattening,[],[f30])).
% 11.73/1.90  fof(f30,plain,(
% 11.73/1.90    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.73/1.90    inference(ennf_transformation,[],[f4])).
% 11.73/1.90  fof(f4,axiom,(
% 11.73/1.90    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.73/1.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 11.73/1.90  fof(f233,plain,(
% 11.73/1.90    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1)) )),
% 11.73/1.90    inference(unit_resulting_resolution,[],[f57,f53])).
% 11.73/1.90  fof(f53,plain,(
% 11.73/1.90    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 11.73/1.90    inference(cnf_transformation,[],[f28])).
% 11.73/1.90  fof(f28,plain,(
% 11.73/1.90    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.73/1.90    inference(ennf_transformation,[],[f7])).
% 11.73/1.90  fof(f7,axiom,(
% 11.73/1.90    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.73/1.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 11.73/1.90  fof(f57,plain,(
% 11.73/1.90    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.73/1.90    inference(equality_resolution,[],[f48])).
% 11.73/1.90  fof(f48,plain,(
% 11.73/1.90    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.73/1.90    inference(cnf_transformation,[],[f2])).
% 11.73/1.90  fof(f2,axiom,(
% 11.73/1.90    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.73/1.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 11.73/1.90  fof(f70,plain,(
% 11.73/1.90    r1_tarski(sK1,u1_struct_0(sK0))),
% 11.73/1.90    inference(unit_resulting_resolution,[],[f36,f51])).
% 11.73/1.90  fof(f36,plain,(
% 11.73/1.90    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.73/1.90    inference(cnf_transformation,[],[f19])).
% 11.73/1.90  fof(f41,plain,(
% 11.73/1.90    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.73/1.90    inference(cnf_transformation,[],[f9])).
% 11.73/1.90  fof(f9,axiom,(
% 11.73/1.90    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.73/1.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 11.73/1.90  fof(f38,plain,(
% 11.73/1.90    l1_pre_topc(sK0)),
% 11.73/1.90    inference(cnf_transformation,[],[f19])).
% 11.73/1.90  fof(f31379,plain,(
% 11.73/1.90    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)))),
% 11.73/1.90    inference(forward_demodulation,[],[f31378,f43])).
% 11.73/1.90  fof(f31378,plain,(
% 11.73/1.90    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)))),
% 11.73/1.90    inference(forward_demodulation,[],[f31332,f44])).
% 11.73/1.90  fof(f44,plain,(
% 11.73/1.90    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.73/1.90    inference(cnf_transformation,[],[f6])).
% 11.73/1.90  fof(f6,axiom,(
% 11.73/1.90    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.73/1.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 11.73/1.90  fof(f31332,plain,(
% 11.73/1.90    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))),
% 11.73/1.90    inference(backward_demodulation,[],[f528,f31331])).
% 11.73/1.90  fof(f31331,plain,(
% 11.73/1.90    ( ! [X0] : (k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0)))) )),
% 11.73/1.90    inference(forward_demodulation,[],[f31310,f1758])).
% 11.73/1.90  fof(f1758,plain,(
% 11.73/1.90    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0)))) )),
% 11.73/1.90    inference(forward_demodulation,[],[f1676,f1731])).
% 11.73/1.90  fof(f1731,plain,(
% 11.73/1.90    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k4_xboole_0(sK1,X0))) )),
% 11.73/1.90    inference(unit_resulting_resolution,[],[f34,f299,f56])).
% 11.73/1.90  fof(f56,plain,(
% 11.73/1.90    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 11.73/1.90    inference(cnf_transformation,[],[f33])).
% 11.73/1.90  fof(f33,plain,(
% 11.73/1.90    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.73/1.90    inference(flattening,[],[f32])).
% 11.73/1.90  fof(f32,plain,(
% 11.73/1.90    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.73/1.90    inference(ennf_transformation,[],[f10])).
% 11.73/1.90  fof(f10,axiom,(
% 11.73/1.90    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.73/1.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 11.73/1.90  fof(f299,plain,(
% 11.73/1.90    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 11.73/1.90    inference(unit_resulting_resolution,[],[f186,f50])).
% 11.73/1.90  fof(f186,plain,(
% 11.73/1.90    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0))) )),
% 11.73/1.90    inference(unit_resulting_resolution,[],[f42,f70,f55])).
% 11.73/1.90  fof(f42,plain,(
% 11.73/1.90    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.73/1.90    inference(cnf_transformation,[],[f5])).
% 11.73/1.90  fof(f5,axiom,(
% 11.73/1.90    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.73/1.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 11.73/1.90  fof(f1676,plain,(
% 11.73/1.90    ( ! [X0] : (k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0)))) )),
% 11.73/1.90    inference(unit_resulting_resolution,[],[f38,f37,f34,f299,f40])).
% 11.73/1.90  fof(f40,plain,(
% 11.73/1.90    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) )),
% 11.73/1.90    inference(cnf_transformation,[],[f23])).
% 11.73/1.90  fof(f23,plain,(
% 11.73/1.90    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.73/1.90    inference(flattening,[],[f22])).
% 11.73/1.90  fof(f22,plain,(
% 11.73/1.90    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.73/1.90    inference(ennf_transformation,[],[f15])).
% 11.73/1.90  fof(f15,axiom,(
% 11.73/1.90    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))))),
% 11.73/1.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_pre_topc)).
% 11.73/1.90  fof(f37,plain,(
% 11.73/1.90    v2_pre_topc(sK0)),
% 11.73/1.90    inference(cnf_transformation,[],[f19])).
% 11.73/1.90  fof(f31310,plain,(
% 11.73/1.90    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0)))) )),
% 11.73/1.90    inference(unit_resulting_resolution,[],[f505,f1718,f56])).
% 11.73/1.90  fof(f1718,plain,(
% 11.73/1.90    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 11.73/1.90    inference(unit_resulting_resolution,[],[f38,f299,f46])).
% 11.73/1.90  fof(f46,plain,(
% 11.73/1.90    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.73/1.90    inference(cnf_transformation,[],[f26])).
% 11.73/1.90  fof(f26,plain,(
% 11.73/1.90    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.73/1.90    inference(flattening,[],[f25])).
% 11.73/1.90  fof(f25,plain,(
% 11.73/1.90    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.73/1.90    inference(ennf_transformation,[],[f13])).
% 11.73/1.90  fof(f13,axiom,(
% 11.73/1.90    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.73/1.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 11.73/1.90  fof(f505,plain,(
% 11.73/1.90    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.73/1.90    inference(unit_resulting_resolution,[],[f38,f34,f46])).
% 11.73/1.90  fof(f528,plain,(
% 11.73/1.90    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))))),
% 11.73/1.90    inference(unit_resulting_resolution,[],[f527,f53])).
% 11.73/1.90  fof(f527,plain,(
% 11.73/1.90    ~r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))),
% 11.73/1.90    inference(backward_demodulation,[],[f373,f525])).
% 11.73/1.90  fof(f525,plain,(
% 11.73/1.90    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)) )),
% 11.73/1.90    inference(unit_resulting_resolution,[],[f506,f52])).
% 11.73/1.90  fof(f52,plain,(
% 11.73/1.90    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 11.73/1.90    inference(cnf_transformation,[],[f27])).
% 11.73/1.90  fof(f27,plain,(
% 11.73/1.90    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.73/1.90    inference(ennf_transformation,[],[f11])).
% 11.73/1.90  fof(f11,axiom,(
% 11.73/1.90    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 11.73/1.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 11.73/1.90  fof(f506,plain,(
% 11.73/1.90    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.73/1.90    inference(unit_resulting_resolution,[],[f38,f36,f46])).
% 11.73/1.90  fof(f373,plain,(
% 11.73/1.90    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))),
% 11.73/1.90    inference(backward_demodulation,[],[f35,f372])).
% 11.73/1.90  fof(f372,plain,(
% 11.73/1.90    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) )),
% 11.73/1.90    inference(unit_resulting_resolution,[],[f36,f52])).
% 11.73/1.90  fof(f35,plain,(
% 11.73/1.90    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 11.73/1.90    inference(cnf_transformation,[],[f19])).
% 11.73/1.90  % SZS output end Proof for theBenchmark
% 11.73/1.90  % (16459)------------------------------
% 11.73/1.90  % (16459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.73/1.90  % (16459)Termination reason: Refutation
% 11.73/1.90  
% 11.73/1.90  % (16459)Memory used [KB]: 21108
% 11.73/1.90  % (16459)Time elapsed: 1.349 s
% 11.73/1.90  % (16459)------------------------------
% 11.73/1.90  % (16459)------------------------------
% 12.26/1.90  % (16451)Success in time 1.532 s
%------------------------------------------------------------------------------
