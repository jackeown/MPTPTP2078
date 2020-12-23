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
% DateTime   : Thu Dec  3 13:11:05 EST 2020

% Result     : Theorem 3.00s
% Output     : Refutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 400 expanded)
%              Number of leaves         :   12 ( 103 expanded)
%              Depth                    :   16
%              Number of atoms          :  148 ( 957 expanded)
%              Number of equality atoms :   23 (  88 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5344,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5342,f4223])).

fof(f4223,plain,(
    m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(backward_demodulation,[],[f4201,f4222])).

fof(f4222,plain,(
    k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4187,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f4187,plain,(
    k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) = k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f1278,f1280,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1280,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f447,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f447,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f28,f31,f297,f27,f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).

fof(f297,plain,(
    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f188,f265])).

fof(f265,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f25,f27,f42])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f188,plain,(
    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f27,f25,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f1278,plain,(
    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f444,f37])).

fof(f444,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f28,f45,f297,f25,f30])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f31,f32])).

fof(f4201,plain,(
    m1_subset_1(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f1278,f1280,f41])).

fof(f5342,plain,(
    ~ m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(backward_demodulation,[],[f424,f5248])).

fof(f5248,plain,(
    k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f3788,f3805,f42])).

fof(f3805,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f3792,f37])).

fof(f3792,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(superposition,[],[f3449,f64])).

fof(f64,plain,(
    u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f53,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f53,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f27,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3449,plain,(
    ! [X0] : r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f2905,f32])).

fof(f2905,plain,(
    ! [X0] : r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(X0,sK1)) ),
    inference(unit_resulting_resolution,[],[f2563,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f2563,plain,(
    ! [X38] : r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),X38),sK1) ),
    inference(superposition,[],[f2430,f150])).

fof(f150,plain,(
    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f144,f33])).

fof(f144,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f28,f27,f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f2430,plain,(
    ! [X28,X26,X25] : r1_tarski(k4_xboole_0(X25,X26),k2_xboole_0(X25,X28)) ),
    inference(subsumption_resolution,[],[f2340,f103])).

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f31,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f2340,plain,(
    ! [X28,X26,X27,X25] :
      ( ~ r1_tarski(k4_xboole_0(X27,X27),X28)
      | r1_tarski(k4_xboole_0(X25,X26),k2_xboole_0(X25,X28)) ) ),
    inference(superposition,[],[f40,f1671])).

fof(f1671,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(forward_demodulation,[],[f1645,f496])).

fof(f496,plain,(
    ! [X2,X3] : k2_xboole_0(X3,k4_xboole_0(X2,X2)) = X3 ),
    inference(superposition,[],[f110,f32])).

fof(f110,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X0),X1) = X1 ),
    inference(unit_resulting_resolution,[],[f103,f33])).

fof(f1645,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X0)),X2),X1) ),
    inference(unit_resulting_resolution,[],[f103,f117,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f117,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X0),X1) ),
    inference(unit_resulting_resolution,[],[f104,f39])).

fof(f104,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f45,f39])).

fof(f3788,plain,(
    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f3709,f37])).

fof(f3709,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    inference(superposition,[],[f3399,f63])).

fof(f63,plain,(
    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f52,f33])).

fof(f52,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f25,f38])).

fof(f3399,plain,(
    ! [X0] : r1_tarski(k1_tops_1(sK0,sK2),k2_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f2895,f32])).

fof(f2895,plain,(
    ! [X0] : r1_tarski(k1_tops_1(sK0,sK2),k2_xboole_0(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f2562,f40])).

fof(f2562,plain,(
    ! [X37] : r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK2),X37),sK2) ),
    inference(superposition,[],[f2430,f148])).

fof(f148,plain,(
    sK2 = k2_xboole_0(k1_tops_1(sK0,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f143,f33])).

fof(f143,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f28,f25,f29])).

fof(f424,plain,(
    ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f298,f38])).

fof(f298,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f26,f265])).

fof(f26,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (28663)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (28652)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (28665)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (28671)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (28656)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (28675)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (28654)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.52  % (28670)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (28662)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (28664)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (28655)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (28669)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (28678)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.52  % (28660)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.53  % (28676)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.53  % (28674)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (28668)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.53  % (28666)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  % (28657)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.53  % (28661)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.53  % (28659)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.54  % (28672)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.54  % (28673)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.54  % (28677)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.54  % (28653)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (28658)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.55  % (28658)Refutation not found, incomplete strategy% (28658)------------------------------
% 0.20/0.55  % (28658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (28658)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (28658)Memory used [KB]: 10618
% 0.20/0.55  % (28658)Time elapsed: 0.139 s
% 0.20/0.55  % (28658)------------------------------
% 0.20/0.55  % (28658)------------------------------
% 2.33/0.70  % (28661)Refutation not found, incomplete strategy% (28661)------------------------------
% 2.33/0.70  % (28661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.33/0.70  % (28661)Termination reason: Refutation not found, incomplete strategy
% 2.33/0.70  
% 2.33/0.70  % (28661)Memory used [KB]: 6140
% 2.33/0.70  % (28661)Time elapsed: 0.272 s
% 2.33/0.70  % (28661)------------------------------
% 2.33/0.70  % (28661)------------------------------
% 3.00/0.83  % (28659)Refutation found. Thanks to Tanya!
% 3.00/0.83  % SZS status Theorem for theBenchmark
% 3.00/0.83  % SZS output start Proof for theBenchmark
% 3.00/0.83  fof(f5344,plain,(
% 3.00/0.83    $false),
% 3.00/0.83    inference(subsumption_resolution,[],[f5342,f4223])).
% 3.00/0.83  fof(f4223,plain,(
% 3.00/0.83    m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 3.00/0.83    inference(backward_demodulation,[],[f4201,f4222])).
% 3.00/0.83  fof(f4222,plain,(
% 3.00/0.83    k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))),
% 3.00/0.83    inference(forward_demodulation,[],[f4187,f32])).
% 3.00/0.83  fof(f32,plain,(
% 3.00/0.83    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.00/0.83    inference(cnf_transformation,[],[f1])).
% 3.00/0.83  fof(f1,axiom,(
% 3.00/0.83    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.00/0.83  fof(f4187,plain,(
% 3.00/0.83    k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) = k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f1278,f1280,f42])).
% 3.00/0.83  fof(f42,plain,(
% 3.00/0.83    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 3.00/0.83    inference(cnf_transformation,[],[f24])).
% 3.00/0.83  fof(f24,plain,(
% 3.00/0.83    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.00/0.83    inference(flattening,[],[f23])).
% 3.00/0.83  fof(f23,plain,(
% 3.00/0.83    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.00/0.83    inference(ennf_transformation,[],[f8])).
% 3.00/0.83  fof(f8,axiom,(
% 3.00/0.83    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.00/0.83  fof(f1280,plain,(
% 3.00/0.83    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f447,f37])).
% 3.00/0.83  fof(f37,plain,(
% 3.00/0.83    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.00/0.83    inference(cnf_transformation,[],[f9])).
% 3.00/0.83  fof(f9,axiom,(
% 3.00/0.83    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.00/0.83  fof(f447,plain,(
% 3.00/0.83    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f28,f31,f297,f27,f30])).
% 3.00/0.83  fof(f30,plain,(
% 3.00/0.83    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 3.00/0.83    inference(cnf_transformation,[],[f17])).
% 3.00/0.83  fof(f17,plain,(
% 3.00/0.83    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.00/0.83    inference(flattening,[],[f16])).
% 3.00/0.83  fof(f16,plain,(
% 3.00/0.83    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.00/0.83    inference(ennf_transformation,[],[f11])).
% 3.00/0.83  fof(f11,axiom,(
% 3.00/0.83    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 3.00/0.83  fof(f27,plain,(
% 3.00/0.83    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.00/0.83    inference(cnf_transformation,[],[f14])).
% 3.00/0.83  fof(f14,plain,(
% 3.00/0.83    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.00/0.83    inference(ennf_transformation,[],[f13])).
% 3.00/0.83  fof(f13,negated_conjecture,(
% 3.00/0.83    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 3.00/0.83    inference(negated_conjecture,[],[f12])).
% 3.00/0.83  fof(f12,conjecture,(
% 3.00/0.83    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 3.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).
% 3.00/0.83  fof(f297,plain,(
% 3.00/0.83    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.00/0.83    inference(backward_demodulation,[],[f188,f265])).
% 3.00/0.83  fof(f265,plain,(
% 3.00/0.83    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f25,f27,f42])).
% 3.00/0.83  fof(f25,plain,(
% 3.00/0.83    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.00/0.83    inference(cnf_transformation,[],[f14])).
% 3.00/0.83  fof(f188,plain,(
% 3.00/0.83    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f27,f25,f41])).
% 3.00/0.83  fof(f41,plain,(
% 3.00/0.83    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.00/0.83    inference(cnf_transformation,[],[f22])).
% 3.00/0.83  fof(f22,plain,(
% 3.00/0.83    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.00/0.83    inference(flattening,[],[f21])).
% 3.00/0.83  fof(f21,plain,(
% 3.00/0.83    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.00/0.83    inference(ennf_transformation,[],[f7])).
% 3.00/0.83  fof(f7,axiom,(
% 3.00/0.83    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 3.00/0.83  fof(f31,plain,(
% 3.00/0.83    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.00/0.83    inference(cnf_transformation,[],[f6])).
% 3.00/0.83  fof(f6,axiom,(
% 3.00/0.83    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.00/0.83  fof(f28,plain,(
% 3.00/0.83    l1_pre_topc(sK0)),
% 3.00/0.83    inference(cnf_transformation,[],[f14])).
% 3.00/0.83  fof(f1278,plain,(
% 3.00/0.83    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f444,f37])).
% 3.00/0.83  fof(f444,plain,(
% 3.00/0.83    r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f28,f45,f297,f25,f30])).
% 3.00/0.83  fof(f45,plain,(
% 3.00/0.83    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 3.00/0.83    inference(superposition,[],[f31,f32])).
% 3.00/0.83  fof(f4201,plain,(
% 3.00/0.83    m1_subset_1(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f1278,f1280,f41])).
% 3.00/0.83  fof(f5342,plain,(
% 3.00/0.83    ~m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 3.00/0.83    inference(backward_demodulation,[],[f424,f5248])).
% 3.00/0.83  fof(f5248,plain,(
% 3.00/0.83    k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f3788,f3805,f42])).
% 3.00/0.83  fof(f3805,plain,(
% 3.00/0.83    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f3792,f37])).
% 3.00/0.83  fof(f3792,plain,(
% 3.00/0.83    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 3.00/0.83    inference(superposition,[],[f3449,f64])).
% 3.00/0.83  fof(f64,plain,(
% 3.00/0.83    u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0))),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f53,f33])).
% 3.00/0.83  fof(f33,plain,(
% 3.00/0.83    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 3.00/0.83    inference(cnf_transformation,[],[f18])).
% 3.00/0.83  fof(f18,plain,(
% 3.00/0.83    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.00/0.83    inference(ennf_transformation,[],[f3])).
% 3.00/0.83  fof(f3,axiom,(
% 3.00/0.83    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.00/0.83  fof(f53,plain,(
% 3.00/0.83    r1_tarski(sK1,u1_struct_0(sK0))),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f27,f38])).
% 3.00/0.83  fof(f38,plain,(
% 3.00/0.83    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.00/0.83    inference(cnf_transformation,[],[f9])).
% 3.00/0.83  fof(f3449,plain,(
% 3.00/0.83    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(sK1,X0))) )),
% 3.00/0.83    inference(superposition,[],[f2905,f32])).
% 3.00/0.83  fof(f2905,plain,(
% 3.00/0.83    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(X0,sK1))) )),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f2563,f40])).
% 3.00/0.83  fof(f40,plain,(
% 3.00/0.83    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.00/0.83    inference(cnf_transformation,[],[f20])).
% 3.00/0.83  fof(f20,plain,(
% 3.00/0.83    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.00/0.83    inference(ennf_transformation,[],[f5])).
% 3.00/0.83  fof(f5,axiom,(
% 3.00/0.83    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 3.00/0.83  fof(f2563,plain,(
% 3.00/0.83    ( ! [X38] : (r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),X38),sK1)) )),
% 3.00/0.83    inference(superposition,[],[f2430,f150])).
% 3.00/0.83  fof(f150,plain,(
% 3.00/0.83    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f144,f33])).
% 3.00/0.83  fof(f144,plain,(
% 3.00/0.83    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f28,f27,f29])).
% 3.00/0.83  fof(f29,plain,(
% 3.00/0.83    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 3.00/0.83    inference(cnf_transformation,[],[f15])).
% 3.00/0.83  fof(f15,plain,(
% 3.00/0.83    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.00/0.83    inference(ennf_transformation,[],[f10])).
% 3.00/0.83  fof(f10,axiom,(
% 3.00/0.83    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 3.00/0.83  fof(f2430,plain,(
% 3.00/0.83    ( ! [X28,X26,X25] : (r1_tarski(k4_xboole_0(X25,X26),k2_xboole_0(X25,X28))) )),
% 3.00/0.83    inference(subsumption_resolution,[],[f2340,f103])).
% 3.00/0.83  fof(f103,plain,(
% 3.00/0.83    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f31,f39])).
% 3.00/0.83  fof(f39,plain,(
% 3.00/0.83    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.00/0.83    inference(cnf_transformation,[],[f19])).
% 3.00/0.83  fof(f19,plain,(
% 3.00/0.83    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.00/0.83    inference(ennf_transformation,[],[f4])).
% 3.00/0.83  fof(f4,axiom,(
% 3.00/0.83    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 3.00/0.83  fof(f2340,plain,(
% 3.00/0.83    ( ! [X28,X26,X27,X25] : (~r1_tarski(k4_xboole_0(X27,X27),X28) | r1_tarski(k4_xboole_0(X25,X26),k2_xboole_0(X25,X28))) )),
% 3.00/0.83    inference(superposition,[],[f40,f1671])).
% 3.00/0.83  fof(f1671,plain,(
% 3.00/0.83    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 3.00/0.83    inference(forward_demodulation,[],[f1645,f496])).
% 3.00/0.83  fof(f496,plain,(
% 3.00/0.83    ( ! [X2,X3] : (k2_xboole_0(X3,k4_xboole_0(X2,X2)) = X3) )),
% 3.00/0.83    inference(superposition,[],[f110,f32])).
% 3.00/0.83  fof(f110,plain,(
% 3.00/0.83    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X0),X1) = X1) )),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f103,f33])).
% 3.00/0.83  fof(f1645,plain,(
% 3.00/0.83    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X0)),X2),X1)) )),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f103,f117,f36])).
% 3.00/0.83  fof(f36,plain,(
% 3.00/0.83    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 3.00/0.83    inference(cnf_transformation,[],[f2])).
% 3.00/0.83  fof(f2,axiom,(
% 3.00/0.83    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.00/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.00/0.83  fof(f117,plain,(
% 3.00/0.83    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X0),X1)) )),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f104,f39])).
% 3.00/0.83  fof(f104,plain,(
% 3.00/0.83    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f45,f39])).
% 3.00/0.83  fof(f3788,plain,(
% 3.00/0.83    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f3709,f37])).
% 3.00/0.83  fof(f3709,plain,(
% 3.00/0.83    r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))),
% 3.00/0.83    inference(superposition,[],[f3399,f63])).
% 3.00/0.83  fof(f63,plain,(
% 3.00/0.83    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0))),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f52,f33])).
% 3.00/0.83  fof(f52,plain,(
% 3.00/0.83    r1_tarski(sK2,u1_struct_0(sK0))),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f25,f38])).
% 3.00/0.83  fof(f3399,plain,(
% 3.00/0.83    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK2),k2_xboole_0(sK2,X0))) )),
% 3.00/0.83    inference(superposition,[],[f2895,f32])).
% 3.00/0.83  fof(f2895,plain,(
% 3.00/0.83    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK2),k2_xboole_0(X0,sK2))) )),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f2562,f40])).
% 3.00/0.83  fof(f2562,plain,(
% 3.00/0.83    ( ! [X37] : (r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK2),X37),sK2)) )),
% 3.00/0.83    inference(superposition,[],[f2430,f148])).
% 3.00/0.83  fof(f148,plain,(
% 3.00/0.83    sK2 = k2_xboole_0(k1_tops_1(sK0,sK2),sK2)),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f143,f33])).
% 3.00/0.83  fof(f143,plain,(
% 3.00/0.83    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f28,f25,f29])).
% 3.00/0.83  fof(f424,plain,(
% 3.00/0.83    ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK1,sK2))))),
% 3.00/0.83    inference(unit_resulting_resolution,[],[f298,f38])).
% 3.00/0.83  fof(f298,plain,(
% 3.00/0.83    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))),
% 3.00/0.83    inference(backward_demodulation,[],[f26,f265])).
% 3.00/0.83  fof(f26,plain,(
% 3.00/0.83    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 3.00/0.83    inference(cnf_transformation,[],[f14])).
% 3.00/0.83  % SZS output end Proof for theBenchmark
% 3.00/0.83  % (28659)------------------------------
% 3.00/0.83  % (28659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.00/0.83  % (28659)Termination reason: Refutation
% 3.00/0.83  
% 3.00/0.83  % (28659)Memory used [KB]: 4349
% 3.00/0.83  % (28659)Time elapsed: 0.386 s
% 3.00/0.83  % (28659)------------------------------
% 3.00/0.83  % (28659)------------------------------
% 3.00/0.83  % (28651)Success in time 0.47 s
%------------------------------------------------------------------------------
