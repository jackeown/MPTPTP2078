%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:52 EST 2020

% Result     : Theorem 12.57s
% Output     : Refutation 12.57s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 244 expanded)
%              Number of leaves         :   17 (  59 expanded)
%              Depth                    :   16
%              Number of atoms          :  180 ( 687 expanded)
%              Number of equality atoms :   31 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30716,plain,(
    $false ),
    inference(subsumption_resolution,[],[f30715,f5445])).

fof(f5445,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f38,f43,f36,f5354,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f5354,plain,(
    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f5327,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f5327,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f5322,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f5322,plain,(
    r1_tarski(k2_xboole_0(sK2,sK1),u1_struct_0(sK0)) ),
    inference(superposition,[],[f2628,f405])).

fof(f405,plain,(
    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f404,f40])).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f404,plain,(
    k2_xboole_0(u1_struct_0(sK0),k1_xboole_0) = k2_xboole_0(sK2,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f402,f45])).

fof(f402,plain,(
    k2_xboole_0(u1_struct_0(sK0),k1_xboole_0) = k2_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(superposition,[],[f46,f328])).

fof(f328,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f39,f184,f50])).

fof(f50,plain,(
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

fof(f184,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK2,u1_struct_0(sK0)),X0) ),
    inference(unit_resulting_resolution,[],[f134,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f134,plain,(
    ! [X0] : r1_tarski(sK2,k2_xboole_0(u1_struct_0(sK0),X0)) ),
    inference(unit_resulting_resolution,[],[f81,f43,f56])).

fof(f56,plain,(
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

fof(f81,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_1)).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2628,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f807,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f807,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k2_xboole_0(X0,sK1),X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f82,f188,f56])).

fof(f188,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) ),
    inference(unit_resulting_resolution,[],[f58,f54])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f82,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f52])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f30715,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f30714,f45])).

fof(f30714,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(forward_demodulation,[],[f30667,f46])).

fof(f30667,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) ),
    inference(backward_demodulation,[],[f447,f30666])).

fof(f30666,plain,(
    ! [X0] : k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f30646,f2472])).

fof(f2472,plain,(
    ! [X0] : k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f2402,f2442])).

fof(f2442,plain,(
    ! [X0] : k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k4_xboole_0(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f34,f293,f57])).

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f293,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f148,f51])).

fof(f148,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f44,f82,f56])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2402,plain,(
    ! [X0] : k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f38,f37,f34,f293,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
    inference(cnf_transformation,[],[f20])).

fof(f30646,plain,(
    ! [X0] : k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f393,f2423,f57])).

fof(f2423,plain,(
    ! [X0] : m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f38,f293,f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f393,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f38,f34,f47])).

fof(f447,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f439,f54])).

fof(f439,plain,(
    ~ r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f304,f432])).

fof(f432,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(unit_resulting_resolution,[],[f394,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f394,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f38,f36,f47])).

fof(f304,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f35,f297])).

fof(f297,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(unit_resulting_resolution,[],[f36,f53])).

fof(f35,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (3376)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (3374)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (3375)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (3377)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (3396)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (3386)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (3383)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (3387)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (3378)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (3388)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (3373)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (3382)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (3379)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (3391)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (3381)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (3380)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (3385)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (3390)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (3384)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (3393)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (3395)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (3392)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.55  % (3394)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.55  % (3389)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.55  % (3397)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.57  % (3398)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 4.53/0.94  % (3386)Time limit reached!
% 4.53/0.94  % (3386)------------------------------
% 4.53/0.94  % (3386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.53/0.94  % (3386)Termination reason: Time limit
% 4.53/0.94  
% 4.53/0.94  % (3386)Memory used [KB]: 9338
% 4.53/0.94  % (3386)Time elapsed: 0.521 s
% 4.53/0.94  % (3386)------------------------------
% 4.53/0.94  % (3386)------------------------------
% 4.61/0.95  % (3373)Time limit reached!
% 4.61/0.95  % (3373)------------------------------
% 4.61/0.95  % (3373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.61/0.95  % (3373)Termination reason: Time limit
% 4.61/0.95  
% 4.61/0.95  % (3373)Memory used [KB]: 16119
% 4.61/0.95  % (3373)Time elapsed: 0.514 s
% 4.61/0.95  % (3373)------------------------------
% 4.61/0.95  % (3373)------------------------------
% 5.09/1.02  % (3379)Time limit reached!
% 5.09/1.02  % (3379)------------------------------
% 5.09/1.02  % (3379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.09/1.02  % (3379)Termination reason: Time limit
% 5.09/1.02  
% 5.09/1.02  % (3379)Memory used [KB]: 14072
% 5.09/1.02  % (3379)Time elapsed: 0.606 s
% 5.09/1.02  % (3379)------------------------------
% 5.09/1.02  % (3379)------------------------------
% 5.50/1.09  % (3387)Time limit reached!
% 5.50/1.09  % (3387)------------------------------
% 5.50/1.09  % (3387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.50/1.10  % (3387)Termination reason: Time limit
% 5.50/1.10  
% 5.50/1.10  % (3387)Memory used [KB]: 10874
% 5.50/1.10  % (3387)Time elapsed: 0.674 s
% 5.50/1.10  % (3387)------------------------------
% 5.50/1.10  % (3387)------------------------------
% 7.43/1.31  % (3381)Time limit reached!
% 7.43/1.31  % (3381)------------------------------
% 7.43/1.31  % (3381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.43/1.31  % (3381)Termination reason: Time limit
% 7.43/1.31  
% 7.43/1.31  % (3381)Memory used [KB]: 7547
% 7.43/1.31  % (3381)Time elapsed: 0.910 s
% 7.43/1.31  % (3381)------------------------------
% 7.43/1.31  % (3381)------------------------------
% 7.86/1.44  % (3374)Time limit reached!
% 7.86/1.44  % (3374)------------------------------
% 7.86/1.44  % (3374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.86/1.44  % (3374)Termination reason: Time limit
% 7.86/1.44  % (3374)Termination phase: Saturation
% 7.86/1.44  
% 7.86/1.44  % (3374)Memory used [KB]: 23794
% 7.86/1.44  % (3374)Time elapsed: 1.0000 s
% 7.86/1.44  % (3374)------------------------------
% 7.86/1.44  % (3374)------------------------------
% 9.01/1.52  % (3377)Time limit reached!
% 9.01/1.52  % (3377)------------------------------
% 9.01/1.52  % (3377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.01/1.52  % (3377)Termination reason: Time limit
% 9.01/1.52  % (3377)Termination phase: Saturation
% 9.01/1.52  
% 9.01/1.52  % (3377)Memory used [KB]: 12025
% 9.01/1.52  % (3377)Time elapsed: 1.100 s
% 9.01/1.52  % (3377)------------------------------
% 9.01/1.52  % (3377)------------------------------
% 12.57/1.95  % (3380)Refutation found. Thanks to Tanya!
% 12.57/1.95  % SZS status Theorem for theBenchmark
% 12.57/1.96  % SZS output start Proof for theBenchmark
% 12.57/1.96  fof(f30716,plain,(
% 12.57/1.96    $false),
% 12.57/1.96    inference(subsumption_resolution,[],[f30715,f5445])).
% 12.57/1.96  fof(f5445,plain,(
% 12.57/1.96    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)))),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f38,f43,f36,f5354,f41])).
% 12.57/1.96  fof(f41,plain,(
% 12.57/1.96    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 12.57/1.96    inference(cnf_transformation,[],[f22])).
% 12.57/1.96  fof(f22,plain,(
% 12.57/1.96    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.57/1.96    inference(flattening,[],[f21])).
% 12.57/1.96  fof(f21,plain,(
% 12.57/1.96    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.57/1.96    inference(ennf_transformation,[],[f15])).
% 12.57/1.96  fof(f15,axiom,(
% 12.57/1.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 12.57/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).
% 12.57/1.96  fof(f5354,plain,(
% 12.57/1.96    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f5327,f51])).
% 12.57/1.96  fof(f51,plain,(
% 12.57/1.96    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 12.57/1.96    inference(cnf_transformation,[],[f13])).
% 12.57/1.96  fof(f13,axiom,(
% 12.57/1.96    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 12.57/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 12.57/1.96  fof(f5327,plain,(
% 12.57/1.96    r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0))),
% 12.57/1.96    inference(forward_demodulation,[],[f5322,f45])).
% 12.57/1.96  fof(f45,plain,(
% 12.57/1.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 12.57/1.96    inference(cnf_transformation,[],[f1])).
% 12.57/1.96  fof(f1,axiom,(
% 12.57/1.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 12.57/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 12.57/1.96  fof(f5322,plain,(
% 12.57/1.96    r1_tarski(k2_xboole_0(sK2,sK1),u1_struct_0(sK0))),
% 12.57/1.96    inference(superposition,[],[f2628,f405])).
% 12.57/1.96  fof(f405,plain,(
% 12.57/1.96    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0))),
% 12.57/1.96    inference(forward_demodulation,[],[f404,f40])).
% 12.57/1.96  fof(f40,plain,(
% 12.57/1.96    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.57/1.96    inference(cnf_transformation,[],[f3])).
% 12.57/1.96  fof(f3,axiom,(
% 12.57/1.96    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 12.57/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 12.57/1.96  fof(f404,plain,(
% 12.57/1.96    k2_xboole_0(u1_struct_0(sK0),k1_xboole_0) = k2_xboole_0(sK2,u1_struct_0(sK0))),
% 12.57/1.96    inference(forward_demodulation,[],[f402,f45])).
% 12.57/1.96  fof(f402,plain,(
% 12.57/1.96    k2_xboole_0(u1_struct_0(sK0),k1_xboole_0) = k2_xboole_0(u1_struct_0(sK0),sK2)),
% 12.57/1.96    inference(superposition,[],[f46,f328])).
% 12.57/1.96  fof(f328,plain,(
% 12.57/1.96    k1_xboole_0 = k4_xboole_0(sK2,u1_struct_0(sK0))),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f39,f184,f50])).
% 12.57/1.96  fof(f50,plain,(
% 12.57/1.96    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 12.57/1.96    inference(cnf_transformation,[],[f2])).
% 12.57/1.96  fof(f2,axiom,(
% 12.57/1.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 12.57/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 12.57/1.96  fof(f184,plain,(
% 12.57/1.96    ( ! [X0] : (r1_tarski(k4_xboole_0(sK2,u1_struct_0(sK0)),X0)) )),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f134,f54])).
% 12.57/1.96  fof(f54,plain,(
% 12.57/1.96    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 12.57/1.96    inference(cnf_transformation,[],[f28])).
% 12.57/1.96  fof(f28,plain,(
% 12.57/1.96    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 12.57/1.96    inference(ennf_transformation,[],[f8])).
% 12.57/1.96  fof(f8,axiom,(
% 12.57/1.96    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 12.57/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 12.57/1.96  fof(f134,plain,(
% 12.57/1.96    ( ! [X0] : (r1_tarski(sK2,k2_xboole_0(u1_struct_0(sK0),X0))) )),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f81,f43,f56])).
% 12.57/1.96  fof(f56,plain,(
% 12.57/1.96    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 12.57/1.96    inference(cnf_transformation,[],[f31])).
% 12.57/1.96  fof(f31,plain,(
% 12.57/1.96    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 12.57/1.96    inference(flattening,[],[f30])).
% 12.57/1.96  fof(f30,plain,(
% 12.57/1.96    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 12.57/1.96    inference(ennf_transformation,[],[f4])).
% 12.57/1.96  fof(f4,axiom,(
% 12.57/1.96    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 12.57/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 12.57/1.96  fof(f81,plain,(
% 12.57/1.96    r1_tarski(sK2,u1_struct_0(sK0))),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f34,f52])).
% 12.57/1.96  fof(f52,plain,(
% 12.57/1.96    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 12.57/1.96    inference(cnf_transformation,[],[f13])).
% 12.57/1.96  fof(f34,plain,(
% 12.57/1.96    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.57/1.96    inference(cnf_transformation,[],[f20])).
% 12.57/1.96  fof(f20,plain,(
% 12.57/1.96    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 12.57/1.96    inference(flattening,[],[f19])).
% 12.57/1.96  fof(f19,plain,(
% 12.57/1.96    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 12.57/1.96    inference(ennf_transformation,[],[f18])).
% 12.57/1.96  fof(f18,negated_conjecture,(
% 12.57/1.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 12.57/1.96    inference(negated_conjecture,[],[f17])).
% 12.57/1.96  fof(f17,conjecture,(
% 12.57/1.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 12.57/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_1)).
% 12.57/1.96  fof(f39,plain,(
% 12.57/1.96    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 12.57/1.96    inference(cnf_transformation,[],[f5])).
% 12.57/1.96  fof(f5,axiom,(
% 12.57/1.96    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 12.57/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 12.57/1.96  fof(f46,plain,(
% 12.57/1.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 12.57/1.96    inference(cnf_transformation,[],[f7])).
% 12.57/1.96  fof(f7,axiom,(
% 12.57/1.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 12.57/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 12.57/1.96  fof(f2628,plain,(
% 12.57/1.96    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,u1_struct_0(sK0)))) )),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f807,f55])).
% 12.57/1.96  fof(f55,plain,(
% 12.57/1.96    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 12.57/1.96    inference(cnf_transformation,[],[f29])).
% 12.57/1.96  fof(f29,plain,(
% 12.57/1.96    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 12.57/1.96    inference(ennf_transformation,[],[f9])).
% 12.57/1.96  fof(f9,axiom,(
% 12.57/1.96    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 12.57/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 12.57/1.96  fof(f807,plain,(
% 12.57/1.96    ( ! [X0] : (r1_tarski(k4_xboole_0(k2_xboole_0(X0,sK1),X0),u1_struct_0(sK0))) )),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f82,f188,f56])).
% 12.57/1.96  fof(f188,plain,(
% 12.57/1.96    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1)) )),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f58,f54])).
% 12.57/1.96  fof(f58,plain,(
% 12.57/1.96    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 12.57/1.96    inference(equality_resolution,[],[f49])).
% 12.57/1.96  fof(f49,plain,(
% 12.57/1.96    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 12.57/1.96    inference(cnf_transformation,[],[f2])).
% 12.57/1.96  fof(f82,plain,(
% 12.57/1.96    r1_tarski(sK1,u1_struct_0(sK0))),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f36,f52])).
% 12.57/1.96  fof(f36,plain,(
% 12.57/1.96    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.57/1.96    inference(cnf_transformation,[],[f20])).
% 12.57/1.96  fof(f43,plain,(
% 12.57/1.96    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 12.57/1.96    inference(cnf_transformation,[],[f10])).
% 12.57/1.96  fof(f10,axiom,(
% 12.57/1.96    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 12.57/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 12.57/1.96  fof(f38,plain,(
% 12.57/1.96    l1_pre_topc(sK0)),
% 12.57/1.96    inference(cnf_transformation,[],[f20])).
% 12.57/1.96  fof(f30715,plain,(
% 12.57/1.96    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)))),
% 12.57/1.96    inference(forward_demodulation,[],[f30714,f45])).
% 12.57/1.96  fof(f30714,plain,(
% 12.57/1.96    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)))),
% 12.57/1.96    inference(forward_demodulation,[],[f30667,f46])).
% 12.57/1.96  fof(f30667,plain,(
% 12.57/1.96    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))),
% 12.57/1.96    inference(backward_demodulation,[],[f447,f30666])).
% 12.57/1.96  fof(f30666,plain,(
% 12.57/1.96    ( ! [X0] : (k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0)))) )),
% 12.57/1.96    inference(forward_demodulation,[],[f30646,f2472])).
% 12.57/1.96  fof(f2472,plain,(
% 12.57/1.96    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0)))) )),
% 12.57/1.96    inference(forward_demodulation,[],[f2402,f2442])).
% 12.57/1.96  fof(f2442,plain,(
% 12.57/1.96    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k4_xboole_0(sK1,X0))) )),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f34,f293,f57])).
% 12.57/1.96  fof(f57,plain,(
% 12.57/1.96    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 12.57/1.96    inference(cnf_transformation,[],[f33])).
% 12.57/1.96  fof(f33,plain,(
% 12.57/1.96    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.57/1.96    inference(flattening,[],[f32])).
% 12.57/1.96  fof(f32,plain,(
% 12.57/1.96    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 12.57/1.96    inference(ennf_transformation,[],[f11])).
% 12.57/1.96  fof(f11,axiom,(
% 12.57/1.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 12.57/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 12.57/1.96  fof(f293,plain,(
% 12.57/1.96    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f148,f51])).
% 12.57/1.96  fof(f148,plain,(
% 12.57/1.96    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0))) )),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f44,f82,f56])).
% 12.57/1.96  fof(f44,plain,(
% 12.57/1.96    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 12.57/1.96    inference(cnf_transformation,[],[f6])).
% 12.57/1.96  fof(f6,axiom,(
% 12.57/1.96    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 12.57/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 12.57/1.96  fof(f2402,plain,(
% 12.57/1.96    ( ! [X0] : (k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0)))) )),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f38,f37,f34,f293,f42])).
% 12.57/1.96  fof(f42,plain,(
% 12.57/1.96    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) )),
% 12.57/1.96    inference(cnf_transformation,[],[f24])).
% 12.57/1.96  fof(f24,plain,(
% 12.57/1.96    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.57/1.96    inference(flattening,[],[f23])).
% 12.57/1.96  fof(f23,plain,(
% 12.57/1.96    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 12.57/1.96    inference(ennf_transformation,[],[f16])).
% 12.57/1.96  fof(f16,axiom,(
% 12.57/1.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))))),
% 12.57/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_pre_topc)).
% 12.57/1.96  fof(f37,plain,(
% 12.57/1.96    v2_pre_topc(sK0)),
% 12.57/1.96    inference(cnf_transformation,[],[f20])).
% 12.57/1.96  fof(f30646,plain,(
% 12.57/1.96    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0)))) )),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f393,f2423,f57])).
% 12.57/1.96  fof(f2423,plain,(
% 12.57/1.96    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f38,f293,f47])).
% 12.57/1.96  fof(f47,plain,(
% 12.57/1.96    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 12.57/1.96    inference(cnf_transformation,[],[f26])).
% 12.57/1.96  fof(f26,plain,(
% 12.57/1.96    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 12.57/1.96    inference(flattening,[],[f25])).
% 12.57/1.96  fof(f25,plain,(
% 12.57/1.96    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 12.57/1.96    inference(ennf_transformation,[],[f14])).
% 12.57/1.96  fof(f14,axiom,(
% 12.57/1.96    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 12.57/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 12.57/1.96  fof(f393,plain,(
% 12.57/1.96    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f38,f34,f47])).
% 12.57/1.96  fof(f447,plain,(
% 12.57/1.96    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))))),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f439,f54])).
% 12.57/1.96  fof(f439,plain,(
% 12.57/1.96    ~r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))),
% 12.57/1.96    inference(backward_demodulation,[],[f304,f432])).
% 12.57/1.96  fof(f432,plain,(
% 12.57/1.96    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)) )),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f394,f53])).
% 12.57/1.96  fof(f53,plain,(
% 12.57/1.96    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 12.57/1.96    inference(cnf_transformation,[],[f27])).
% 12.57/1.96  fof(f27,plain,(
% 12.57/1.96    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.57/1.96    inference(ennf_transformation,[],[f12])).
% 12.57/1.96  fof(f12,axiom,(
% 12.57/1.96    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 12.57/1.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 12.57/1.96  fof(f394,plain,(
% 12.57/1.96    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f38,f36,f47])).
% 12.57/1.96  fof(f304,plain,(
% 12.57/1.96    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))),
% 12.57/1.96    inference(backward_demodulation,[],[f35,f297])).
% 12.57/1.96  fof(f297,plain,(
% 12.57/1.96    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) )),
% 12.57/1.96    inference(unit_resulting_resolution,[],[f36,f53])).
% 12.57/1.96  fof(f35,plain,(
% 12.57/1.96    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 12.57/1.96    inference(cnf_transformation,[],[f20])).
% 12.57/1.96  % SZS output end Proof for theBenchmark
% 12.57/1.96  % (3380)------------------------------
% 12.57/1.96  % (3380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.57/1.96  % (3380)Termination reason: Refutation
% 12.57/1.96  
% 12.57/1.96  % (3380)Memory used [KB]: 21492
% 12.57/1.96  % (3380)Time elapsed: 1.476 s
% 12.57/1.96  % (3380)------------------------------
% 12.57/1.96  % (3380)------------------------------
% 12.57/1.96  % (3372)Success in time 1.601 s
%------------------------------------------------------------------------------
