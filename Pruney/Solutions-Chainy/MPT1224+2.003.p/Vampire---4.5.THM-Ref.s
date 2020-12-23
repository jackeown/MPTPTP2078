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
% DateTime   : Thu Dec  3 13:10:52 EST 2020

% Result     : Theorem 11.28s
% Output     : Refutation 11.28s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 214 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  178 ( 630 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28683,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28682,f5566])).

fof(f5566,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f45,f48,f43,f5357,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f5357,plain,(
    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f5355,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f5355,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f5348,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f5348,plain,(
    r1_tarski(k2_xboole_0(sK2,sK1),u1_struct_0(sK0)) ),
    inference(superposition,[],[f2283,f84])).

fof(f84,plain,(
    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f76,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f76,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f41,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_1)).

fof(f2283,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f597,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f597,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k2_xboole_0(X0,sK1),X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f77,f289,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f289,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) ),
    inference(unit_resulting_resolution,[],[f67,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f77,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f43,f60])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f28682,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f28681,f49])).

fof(f28681,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(forward_demodulation,[],[f28636,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f28636,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) ),
    inference(backward_demodulation,[],[f951,f28635])).

fof(f28635,plain,(
    ! [X0] : k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f28616,f1572])).

fof(f1572,plain,(
    ! [X0] : k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f1481,f1545])).

fof(f1545,plain,(
    ! [X0] : k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k4_xboole_0(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f41,f109,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f109,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f100,f59])).

fof(f100,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f77,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f1481,plain,(
    ! [X0] : k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f45,f44,f41,f109,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
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
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_pre_topc)).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f28616,plain,(
    ! [X0] : k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f913,f1525,f66])).

fof(f1525,plain,(
    ! [X0] : m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f45,f109,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f913,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f45,f41,f55])).

fof(f951,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f950,f63])).

fof(f950,plain,(
    ~ r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f776,f943])).

fof(f943,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(unit_resulting_resolution,[],[f914,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f914,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f45,f43,f55])).

fof(f776,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f42,f775])).

fof(f775,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(unit_resulting_resolution,[],[f43,f62])).

fof(f42,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:32:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (26162)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.48  % (26166)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.48  % (26174)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.50  % (26179)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.50  % (26164)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.50  % (26167)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (26159)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (26158)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (26163)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (26161)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (26172)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (26171)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (26156)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (26177)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (26180)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (26160)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (26168)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (26176)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (26173)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (26175)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (26155)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (26169)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (26178)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (26157)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (26170)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.54  % (26165)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 4.13/0.91  % (26169)Time limit reached!
% 4.13/0.91  % (26169)------------------------------
% 4.13/0.91  % (26169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.13/0.91  % (26169)Termination reason: Time limit
% 4.13/0.91  
% 4.13/0.91  % (26169)Memory used [KB]: 7164
% 4.13/0.91  % (26169)Time elapsed: 0.507 s
% 4.13/0.91  % (26169)------------------------------
% 4.13/0.91  % (26169)------------------------------
% 4.39/0.92  % (26168)Time limit reached!
% 4.39/0.92  % (26168)------------------------------
% 4.39/0.92  % (26168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.92  % (26168)Termination reason: Time limit
% 4.39/0.92  
% 4.39/0.92  % (26168)Memory used [KB]: 9466
% 4.39/0.92  % (26168)Time elapsed: 0.505 s
% 4.39/0.92  % (26168)------------------------------
% 4.39/0.92  % (26168)------------------------------
% 4.39/0.96  % (26155)Time limit reached!
% 4.39/0.96  % (26155)------------------------------
% 4.39/0.96  % (26155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.97  % (26155)Termination reason: Time limit
% 4.39/0.97  
% 4.39/0.97  % (26155)Memory used [KB]: 17142
% 4.39/0.97  % (26155)Time elapsed: 0.530 s
% 4.39/0.97  % (26155)------------------------------
% 4.39/0.97  % (26155)------------------------------
% 4.39/1.00  % (26161)Time limit reached!
% 4.39/1.00  % (26161)------------------------------
% 4.39/1.00  % (26161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/1.00  % (26161)Termination reason: Time limit
% 4.39/1.00  % (26161)Termination phase: Saturation
% 4.39/1.00  
% 4.39/1.00  % (26161)Memory used [KB]: 12920
% 4.39/1.00  % (26161)Time elapsed: 0.600 s
% 4.39/1.00  % (26161)------------------------------
% 4.39/1.00  % (26161)------------------------------
% 6.82/1.31  % (26163)Time limit reached!
% 6.82/1.31  % (26163)------------------------------
% 6.82/1.31  % (26163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.82/1.32  % (26163)Termination reason: Time limit
% 6.82/1.32  
% 6.82/1.32  % (26163)Memory used [KB]: 9722
% 6.82/1.32  % (26163)Time elapsed: 0.906 s
% 6.82/1.32  % (26163)------------------------------
% 6.82/1.32  % (26163)------------------------------
% 8.21/1.41  % (26156)Time limit reached!
% 8.21/1.41  % (26156)------------------------------
% 8.21/1.41  % (26156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.21/1.41  % (26156)Termination reason: Time limit
% 8.21/1.41  % (26156)Termination phase: Saturation
% 8.21/1.41  
% 8.21/1.41  % (26156)Memory used [KB]: 23027
% 8.21/1.41  % (26156)Time elapsed: 1.0000 s
% 8.21/1.41  % (26156)------------------------------
% 8.21/1.41  % (26156)------------------------------
% 9.04/1.51  % (26159)Time limit reached!
% 9.04/1.51  % (26159)------------------------------
% 9.04/1.51  % (26159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.04/1.51  % (26159)Termination reason: Time limit
% 9.04/1.51  % (26159)Termination phase: Saturation
% 9.04/1.51  
% 9.04/1.51  % (26159)Memory used [KB]: 12920
% 9.04/1.51  % (26159)Time elapsed: 1.100 s
% 9.04/1.51  % (26159)------------------------------
% 9.04/1.51  % (26159)------------------------------
% 11.28/1.80  % (26162)Refutation found. Thanks to Tanya!
% 11.28/1.80  % SZS status Theorem for theBenchmark
% 11.28/1.80  % SZS output start Proof for theBenchmark
% 11.28/1.80  fof(f28683,plain,(
% 11.28/1.80    $false),
% 11.28/1.80    inference(subsumption_resolution,[],[f28682,f5566])).
% 11.28/1.80  fof(f5566,plain,(
% 11.28/1.80    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)))),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f45,f48,f43,f5357,f46])).
% 11.28/1.80  fof(f46,plain,(
% 11.28/1.80    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 11.28/1.80    inference(cnf_transformation,[],[f24])).
% 11.28/1.80  fof(f24,plain,(
% 11.28/1.80    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.28/1.80    inference(flattening,[],[f23])).
% 11.28/1.80  fof(f23,plain,(
% 11.28/1.80    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.28/1.80    inference(ennf_transformation,[],[f17])).
% 11.28/1.80  fof(f17,axiom,(
% 11.28/1.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 11.28/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).
% 11.28/1.80  fof(f5357,plain,(
% 11.28/1.80    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f5355,f59])).
% 11.28/1.80  fof(f59,plain,(
% 11.28/1.80    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.28/1.80    inference(cnf_transformation,[],[f15])).
% 11.28/1.80  fof(f15,axiom,(
% 11.28/1.80    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.28/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 11.28/1.80  fof(f5355,plain,(
% 11.28/1.80    r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0))),
% 11.28/1.80    inference(forward_demodulation,[],[f5348,f49])).
% 11.28/1.80  fof(f49,plain,(
% 11.28/1.80    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.28/1.80    inference(cnf_transformation,[],[f1])).
% 11.28/1.80  fof(f1,axiom,(
% 11.28/1.80    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.28/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 11.28/1.80  fof(f5348,plain,(
% 11.28/1.80    r1_tarski(k2_xboole_0(sK2,sK1),u1_struct_0(sK0))),
% 11.28/1.80    inference(superposition,[],[f2283,f84])).
% 11.28/1.80  fof(f84,plain,(
% 11.28/1.80    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0))),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f76,f51])).
% 11.28/1.80  fof(f51,plain,(
% 11.28/1.80    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 11.28/1.80    inference(cnf_transformation,[],[f27])).
% 11.28/1.80  fof(f27,plain,(
% 11.28/1.80    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.28/1.80    inference(ennf_transformation,[],[f4])).
% 11.28/1.80  fof(f4,axiom,(
% 11.28/1.80    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.28/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 11.28/1.80  fof(f76,plain,(
% 11.28/1.80    r1_tarski(sK2,u1_struct_0(sK0))),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f41,f60])).
% 11.28/1.80  fof(f60,plain,(
% 11.28/1.80    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 11.28/1.80    inference(cnf_transformation,[],[f15])).
% 11.28/1.80  fof(f41,plain,(
% 11.28/1.80    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.28/1.80    inference(cnf_transformation,[],[f22])).
% 11.28/1.80  fof(f22,plain,(
% 11.28/1.80    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.28/1.80    inference(flattening,[],[f21])).
% 11.28/1.80  fof(f21,plain,(
% 11.28/1.80    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.28/1.80    inference(ennf_transformation,[],[f20])).
% 11.28/1.80  fof(f20,negated_conjecture,(
% 11.28/1.80    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 11.28/1.80    inference(negated_conjecture,[],[f19])).
% 11.28/1.80  fof(f19,conjecture,(
% 11.28/1.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 11.28/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_1)).
% 11.28/1.80  fof(f2283,plain,(
% 11.28/1.80    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,u1_struct_0(sK0)))) )),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f597,f64])).
% 11.28/1.80  fof(f64,plain,(
% 11.28/1.80    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 11.28/1.80    inference(cnf_transformation,[],[f36])).
% 11.28/1.80  fof(f36,plain,(
% 11.28/1.80    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.28/1.80    inference(ennf_transformation,[],[f8])).
% 11.28/1.80  fof(f8,axiom,(
% 11.28/1.80    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.28/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 11.28/1.80  fof(f597,plain,(
% 11.28/1.80    ( ! [X0] : (r1_tarski(k4_xboole_0(k2_xboole_0(X0,sK1),X0),u1_struct_0(sK0))) )),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f77,f289,f65])).
% 11.28/1.80  fof(f65,plain,(
% 11.28/1.80    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 11.28/1.80    inference(cnf_transformation,[],[f38])).
% 11.28/1.80  fof(f38,plain,(
% 11.28/1.80    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.28/1.80    inference(flattening,[],[f37])).
% 11.28/1.80  fof(f37,plain,(
% 11.28/1.80    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.28/1.80    inference(ennf_transformation,[],[f5])).
% 11.28/1.80  fof(f5,axiom,(
% 11.28/1.80    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.28/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 11.28/1.80  fof(f289,plain,(
% 11.28/1.80    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1)) )),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f67,f63])).
% 11.28/1.80  fof(f63,plain,(
% 11.28/1.80    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 11.28/1.80    inference(cnf_transformation,[],[f35])).
% 11.28/1.80  fof(f35,plain,(
% 11.28/1.80    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.28/1.80    inference(ennf_transformation,[],[f7])).
% 11.28/1.80  fof(f7,axiom,(
% 11.28/1.80    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.28/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 11.28/1.80  fof(f67,plain,(
% 11.28/1.80    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.28/1.80    inference(equality_resolution,[],[f57])).
% 11.28/1.80  fof(f57,plain,(
% 11.28/1.80    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.28/1.80    inference(cnf_transformation,[],[f2])).
% 11.28/1.80  fof(f2,axiom,(
% 11.28/1.80    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.28/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 11.28/1.80  fof(f77,plain,(
% 11.28/1.80    r1_tarski(sK1,u1_struct_0(sK0))),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f43,f60])).
% 11.28/1.80  fof(f43,plain,(
% 11.28/1.80    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.28/1.80    inference(cnf_transformation,[],[f22])).
% 11.28/1.80  fof(f48,plain,(
% 11.28/1.80    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.28/1.80    inference(cnf_transformation,[],[f9])).
% 11.28/1.80  fof(f9,axiom,(
% 11.28/1.80    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.28/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 11.28/1.80  fof(f45,plain,(
% 11.28/1.80    l1_pre_topc(sK0)),
% 11.28/1.80    inference(cnf_transformation,[],[f22])).
% 11.28/1.80  fof(f28682,plain,(
% 11.28/1.80    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)))),
% 11.28/1.80    inference(forward_demodulation,[],[f28681,f49])).
% 11.28/1.80  fof(f28681,plain,(
% 11.28/1.80    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)))),
% 11.28/1.80    inference(forward_demodulation,[],[f28636,f50])).
% 11.28/1.80  fof(f50,plain,(
% 11.28/1.80    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.28/1.80    inference(cnf_transformation,[],[f6])).
% 11.28/1.80  fof(f6,axiom,(
% 11.28/1.80    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.28/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 11.28/1.80  fof(f28636,plain,(
% 11.28/1.80    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))),
% 11.28/1.80    inference(backward_demodulation,[],[f951,f28635])).
% 11.28/1.80  fof(f28635,plain,(
% 11.28/1.80    ( ! [X0] : (k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0)))) )),
% 11.28/1.80    inference(forward_demodulation,[],[f28616,f1572])).
% 11.28/1.80  fof(f1572,plain,(
% 11.28/1.80    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0)))) )),
% 11.28/1.80    inference(forward_demodulation,[],[f1481,f1545])).
% 11.28/1.80  fof(f1545,plain,(
% 11.28/1.80    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k4_xboole_0(sK1,X0))) )),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f41,f109,f66])).
% 11.28/1.80  fof(f66,plain,(
% 11.28/1.80    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 11.28/1.80    inference(cnf_transformation,[],[f40])).
% 11.28/1.80  fof(f40,plain,(
% 11.28/1.80    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.28/1.80    inference(flattening,[],[f39])).
% 11.28/1.80  fof(f39,plain,(
% 11.28/1.80    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.28/1.80    inference(ennf_transformation,[],[f13])).
% 11.28/1.80  fof(f13,axiom,(
% 11.28/1.80    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.28/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 11.28/1.80  fof(f109,plain,(
% 11.28/1.80    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f100,f59])).
% 11.28/1.80  fof(f100,plain,(
% 11.28/1.80    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0))) )),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f77,f61])).
% 11.28/1.80  fof(f61,plain,(
% 11.28/1.80    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 11.28/1.80    inference(cnf_transformation,[],[f33])).
% 11.28/1.80  fof(f33,plain,(
% 11.28/1.80    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 11.28/1.80    inference(ennf_transformation,[],[f3])).
% 11.28/1.80  fof(f3,axiom,(
% 11.28/1.80    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 11.28/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).
% 11.28/1.80  fof(f1481,plain,(
% 11.28/1.80    ( ! [X0] : (k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0)))) )),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f45,f44,f41,f109,f47])).
% 11.28/1.80  fof(f47,plain,(
% 11.28/1.80    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) )),
% 11.28/1.80    inference(cnf_transformation,[],[f26])).
% 11.28/1.80  fof(f26,plain,(
% 11.28/1.80    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.28/1.80    inference(flattening,[],[f25])).
% 11.28/1.80  fof(f25,plain,(
% 11.28/1.80    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.28/1.80    inference(ennf_transformation,[],[f18])).
% 11.28/1.80  fof(f18,axiom,(
% 11.28/1.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))))),
% 11.28/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_pre_topc)).
% 11.28/1.80  fof(f44,plain,(
% 11.28/1.80    v2_pre_topc(sK0)),
% 11.28/1.80    inference(cnf_transformation,[],[f22])).
% 11.28/1.80  fof(f28616,plain,(
% 11.28/1.80    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0)))) )),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f913,f1525,f66])).
% 11.28/1.80  fof(f1525,plain,(
% 11.28/1.80    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f45,f109,f55])).
% 11.28/1.80  fof(f55,plain,(
% 11.28/1.80    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.28/1.80    inference(cnf_transformation,[],[f32])).
% 11.28/1.80  fof(f32,plain,(
% 11.28/1.80    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.28/1.80    inference(flattening,[],[f31])).
% 11.28/1.80  fof(f31,plain,(
% 11.28/1.80    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.28/1.80    inference(ennf_transformation,[],[f16])).
% 11.28/1.80  fof(f16,axiom,(
% 11.28/1.80    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.28/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 11.28/1.80  fof(f913,plain,(
% 11.28/1.80    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f45,f41,f55])).
% 11.28/1.80  fof(f951,plain,(
% 11.28/1.80    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))))),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f950,f63])).
% 11.28/1.80  fof(f950,plain,(
% 11.28/1.80    ~r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))),
% 11.28/1.80    inference(backward_demodulation,[],[f776,f943])).
% 11.28/1.80  fof(f943,plain,(
% 11.28/1.80    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)) )),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f914,f62])).
% 11.28/1.80  fof(f62,plain,(
% 11.28/1.80    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 11.28/1.80    inference(cnf_transformation,[],[f34])).
% 11.28/1.80  fof(f34,plain,(
% 11.28/1.80    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.28/1.80    inference(ennf_transformation,[],[f14])).
% 11.28/1.80  fof(f14,axiom,(
% 11.28/1.80    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 11.28/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 11.28/1.80  fof(f914,plain,(
% 11.28/1.80    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f45,f43,f55])).
% 11.28/1.80  fof(f776,plain,(
% 11.28/1.80    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))),
% 11.28/1.80    inference(backward_demodulation,[],[f42,f775])).
% 11.28/1.80  fof(f775,plain,(
% 11.28/1.80    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) )),
% 11.28/1.80    inference(unit_resulting_resolution,[],[f43,f62])).
% 11.28/1.80  fof(f42,plain,(
% 11.28/1.80    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 11.28/1.80    inference(cnf_transformation,[],[f22])).
% 11.28/1.80  % SZS output end Proof for theBenchmark
% 11.28/1.80  % (26162)------------------------------
% 11.28/1.80  % (26162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.28/1.80  % (26162)Termination reason: Refutation
% 11.28/1.80  
% 11.28/1.80  % (26162)Memory used [KB]: 20212
% 11.28/1.80  % (26162)Time elapsed: 1.362 s
% 11.28/1.80  % (26162)------------------------------
% 11.28/1.80  % (26162)------------------------------
% 11.28/1.80  % (26154)Success in time 1.437 s
%------------------------------------------------------------------------------
