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
% DateTime   : Thu Dec  3 13:10:53 EST 2020

% Result     : Theorem 14.71s
% Output     : Refutation 14.71s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 304 expanded)
%              Number of leaves         :   13 (  63 expanded)
%              Depth                    :   17
%              Number of atoms          :  202 ( 954 expanded)
%              Number of equality atoms :   37 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18241,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18240,f8594])).

fof(f8594,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f42,f932])).

fof(f932,plain,(
    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f931,f71])).

fof(f71,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f58,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_1)).

fof(f58,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f32,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f931,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f923,f89])).

fof(f89,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f76,f36])).

fof(f76,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f34,f45])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f923,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f292,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f292,plain,(
    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f287,f180])).

fof(f180,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f63,f34])).

fof(f63,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_xboole_0(X6,sK2) = k4_subset_1(u1_struct_0(sK0),X6,sK2) ) ),
    inference(resolution,[],[f32,f47])).

fof(f287,plain,(
    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f68,f34])).

fof(f68,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X0,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f67,f36])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X0,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f56,f35])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X0,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK2)) ) ),
    inference(resolution,[],[f32,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_pre_topc)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f18240,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f18239,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f18239,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(forward_demodulation,[],[f18232,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f18232,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) ),
    inference(backward_demodulation,[],[f156,f18231])).

fof(f18231,plain,(
    ! [X40] : k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X40))) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X40))) ),
    inference(forward_demodulation,[],[f18230,f1768])).

fof(f1768,plain,(
    ! [X7] : k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(sK1,X7)),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X7))) ),
    inference(forward_demodulation,[],[f1757,f782])).

fof(f782,plain,(
    ! [X7] : k4_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X7),sK2) = k2_xboole_0(sK2,k4_xboole_0(sK1,X7)) ),
    inference(forward_demodulation,[],[f774,f50])).

fof(f774,plain,(
    ! [X7] : k4_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X7),sK2) = k2_xboole_0(k4_xboole_0(sK1,X7),sK2) ),
    inference(resolution,[],[f175,f353])).

fof(f353,plain,(
    ! [X5] : r1_tarski(k4_xboole_0(sK1,X5),u1_struct_0(sK0)) ),
    inference(resolution,[],[f103,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f103,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | r1_tarski(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f84,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f84,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f34,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f175,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f63,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1757,plain,(
    ! [X7] : k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X7),sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(sK1,X7)),k2_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f282,f353])).

fof(f282,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X0,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK2)) ) ),
    inference(resolution,[],[f68,f39])).

fof(f18230,plain,(
    ! [X40] : k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(sK1,X40)),k2_pre_topc(sK0,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X40))) ),
    inference(forward_demodulation,[],[f18204,f50])).

fof(f18204,plain,(
    ! [X40] : k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(sK1,X40)),k2_pre_topc(sK0,sK2)) = k2_xboole_0(k2_pre_topc(sK0,k4_xboole_0(sK1,X40)),k2_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f7911,f1251])).

fof(f1251,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | k4_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2)) = k2_xboole_0(X0,k2_pre_topc(sK0,sK2)) ) ),
    inference(resolution,[],[f112,f39])).

fof(f112,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_xboole_0(X6,k2_pre_topc(sK0,sK2)) = k4_subset_1(u1_struct_0(sK0),X6,k2_pre_topc(sK0,sK2)) ) ),
    inference(resolution,[],[f71,f47])).

fof(f7911,plain,(
    ! [X10] : r1_tarski(k2_pre_topc(sK0,k4_xboole_0(sK1,X10)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f1536,f133])).

fof(f133,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f89,f40])).

fof(f1536,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(k2_pre_topc(sK0,sK1),X9)
      | r1_tarski(k2_pre_topc(sK0,k4_xboole_0(sK1,X8)),X9) ) ),
    inference(subsumption_resolution,[],[f1534,f555])).

fof(f555,plain,(
    ! [X2] : m1_subset_1(k4_xboole_0(sK1,X2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f353,f39])).

fof(f1534,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(k4_xboole_0(sK1,X8),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k2_pre_topc(sK0,sK1),X9)
      | r1_tarski(k2_pre_topc(sK0,k4_xboole_0(sK1,X8)),X9) ) ),
    inference(resolution,[],[f263,f41])).

fof(f263,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k2_pre_topc(sK0,sK1),X6)
      | r1_tarski(k2_pre_topc(sK0,X5),X6) ) ),
    inference(resolution,[],[f90,f37])).

fof(f90,plain,(
    ! [X2] :
      ( r1_tarski(k2_pre_topc(sK0,X2),k2_pre_topc(sK0,sK1))
      | ~ r1_tarski(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f77,f36])).

fof(f77,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X2,sK1)
      | r1_tarski(k2_pre_topc(sK0,X2),k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f34,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f156,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f96,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f96,plain,(
    ~ r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f95,f89])).

fof(f95,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f92,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f92,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f33,f83])).

fof(f83,plain,(
    ! [X8] : k7_subset_1(u1_struct_0(sK0),sK1,X8) = k4_xboole_0(sK1,X8) ),
    inference(resolution,[],[f34,f44])).

fof(f33,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:57:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (8039)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (8044)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.52  % (8047)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % (8036)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.53  % (8045)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.53  % (8035)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.53  % (8040)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.53  % (8038)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.54  % (8037)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.43/0.55  % (8041)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.43/0.55  % (8046)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.43/0.55  % (8051)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.43/0.56  % (8056)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.43/0.56  % (8052)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.43/0.56  % (8057)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.43/0.56  % (8043)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.43/0.57  % (8058)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.43/0.57  % (8050)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.67/0.58  % (8048)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.67/0.58  % (8055)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.67/0.59  % (8042)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.67/0.59  % (8054)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.67/0.60  % (8053)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.67/0.60  % (8049)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 4.00/0.95  % (8047)Time limit reached!
% 4.00/0.95  % (8047)------------------------------
% 4.00/0.95  % (8047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.00/0.95  % (8047)Termination reason: Time limit
% 4.00/0.95  
% 4.00/0.95  % (8047)Memory used [KB]: 20596
% 4.00/0.95  % (8047)Time elapsed: 0.516 s
% 4.00/0.95  % (8047)------------------------------
% 4.00/0.95  % (8047)------------------------------
% 4.78/1.00  % (8042)Time limit reached!
% 4.78/1.00  % (8042)------------------------------
% 4.78/1.00  % (8042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.13/1.02  % (8042)Termination reason: Time limit
% 5.13/1.02  
% 5.13/1.02  % (8042)Memory used [KB]: 13304
% 5.13/1.02  % (8042)Time elapsed: 0.523 s
% 5.13/1.02  % (8042)------------------------------
% 5.13/1.02  % (8042)------------------------------
% 14.24/2.17  % (8045)Time limit reached!
% 14.24/2.17  % (8045)------------------------------
% 14.24/2.17  % (8045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.24/2.17  % (8045)Termination reason: Time limit
% 14.24/2.17  % (8045)Termination phase: Saturation
% 14.24/2.17  
% 14.24/2.17  % (8045)Memory used [KB]: 17398
% 14.24/2.17  % (8045)Time elapsed: 1.700 s
% 14.24/2.17  % (8045)------------------------------
% 14.24/2.17  % (8045)------------------------------
% 14.71/2.24  % (8056)Refutation found. Thanks to Tanya!
% 14.71/2.24  % SZS status Theorem for theBenchmark
% 14.71/2.24  % SZS output start Proof for theBenchmark
% 14.71/2.24  fof(f18241,plain,(
% 14.71/2.24    $false),
% 14.71/2.24    inference(subsumption_resolution,[],[f18240,f8594])).
% 14.71/2.24  fof(f8594,plain,(
% 14.71/2.24    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)))),
% 14.71/2.24    inference(superposition,[],[f42,f932])).
% 14.71/2.24  fof(f932,plain,(
% 14.71/2.24    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),
% 14.71/2.24    inference(subsumption_resolution,[],[f931,f71])).
% 14.71/2.24  fof(f71,plain,(
% 14.71/2.24    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 14.71/2.24    inference(subsumption_resolution,[],[f58,f36])).
% 14.71/2.24  fof(f36,plain,(
% 14.71/2.24    l1_pre_topc(sK0)),
% 14.71/2.24    inference(cnf_transformation,[],[f17])).
% 14.71/2.24  fof(f17,plain,(
% 14.71/2.24    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 14.71/2.24    inference(flattening,[],[f16])).
% 14.71/2.24  fof(f16,plain,(
% 14.71/2.24    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 14.71/2.24    inference(ennf_transformation,[],[f15])).
% 14.71/2.24  fof(f15,negated_conjecture,(
% 14.71/2.24    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 14.71/2.24    inference(negated_conjecture,[],[f14])).
% 14.71/2.24  fof(f14,conjecture,(
% 14.71/2.24    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 14.71/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_1)).
% 14.71/2.24  fof(f58,plain,(
% 14.71/2.24    ~l1_pre_topc(sK0) | m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 14.71/2.24    inference(resolution,[],[f32,f45])).
% 14.71/2.24  fof(f45,plain,(
% 14.71/2.24    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 14.71/2.24    inference(cnf_transformation,[],[f25])).
% 14.71/2.24  fof(f25,plain,(
% 14.71/2.24    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 14.71/2.24    inference(flattening,[],[f24])).
% 14.71/2.24  fof(f24,plain,(
% 14.71/2.24    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 14.71/2.24    inference(ennf_transformation,[],[f11])).
% 14.71/2.24  fof(f11,axiom,(
% 14.71/2.24    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 14.71/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 14.71/2.24  fof(f32,plain,(
% 14.71/2.24    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 14.71/2.24    inference(cnf_transformation,[],[f17])).
% 14.71/2.24  fof(f931,plain,(
% 14.71/2.24    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) | ~m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 14.71/2.24    inference(subsumption_resolution,[],[f923,f89])).
% 14.71/2.24  fof(f89,plain,(
% 14.71/2.24    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 14.71/2.24    inference(subsumption_resolution,[],[f76,f36])).
% 14.71/2.24  fof(f76,plain,(
% 14.71/2.24    ~l1_pre_topc(sK0) | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 14.71/2.24    inference(resolution,[],[f34,f45])).
% 14.71/2.24  fof(f34,plain,(
% 14.71/2.24    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 14.71/2.24    inference(cnf_transformation,[],[f17])).
% 14.71/2.24  fof(f923,plain,(
% 14.71/2.24    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 14.71/2.24    inference(superposition,[],[f292,f47])).
% 14.71/2.24  fof(f47,plain,(
% 14.71/2.24    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 14.71/2.24    inference(cnf_transformation,[],[f29])).
% 14.71/2.24  fof(f29,plain,(
% 14.71/2.24    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 14.71/2.24    inference(flattening,[],[f28])).
% 14.71/2.24  fof(f28,plain,(
% 14.71/2.24    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 14.71/2.24    inference(ennf_transformation,[],[f8])).
% 14.71/2.24  fof(f8,axiom,(
% 14.71/2.24    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 14.71/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 14.71/2.24  fof(f292,plain,(
% 14.71/2.24    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))),
% 14.71/2.24    inference(forward_demodulation,[],[f287,f180])).
% 14.71/2.24  fof(f180,plain,(
% 14.71/2.24    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 14.71/2.24    inference(resolution,[],[f63,f34])).
% 14.71/2.24  fof(f63,plain,(
% 14.71/2.24    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(X6,sK2) = k4_subset_1(u1_struct_0(sK0),X6,sK2)) )),
% 14.71/2.24    inference(resolution,[],[f32,f47])).
% 14.71/2.24  fof(f287,plain,(
% 14.71/2.24    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),
% 14.71/2.24    inference(resolution,[],[f68,f34])).
% 14.71/2.24  fof(f68,plain,(
% 14.71/2.24    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X0,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK2))) )),
% 14.71/2.24    inference(subsumption_resolution,[],[f67,f36])).
% 14.71/2.24  fof(f67,plain,(
% 14.71/2.24    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X0,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK2))) )),
% 14.71/2.24    inference(subsumption_resolution,[],[f56,f35])).
% 14.71/2.24  fof(f35,plain,(
% 14.71/2.24    v2_pre_topc(sK0)),
% 14.71/2.24    inference(cnf_transformation,[],[f17])).
% 14.71/2.24  fof(f56,plain,(
% 14.71/2.24    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X0,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK2))) )),
% 14.71/2.24    inference(resolution,[],[f32,f46])).
% 14.71/2.24  fof(f46,plain,(
% 14.71/2.24    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) )),
% 14.71/2.24    inference(cnf_transformation,[],[f27])).
% 14.71/2.24  fof(f27,plain,(
% 14.71/2.24    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 14.71/2.24    inference(flattening,[],[f26])).
% 14.71/2.24  fof(f26,plain,(
% 14.71/2.24    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 14.71/2.24    inference(ennf_transformation,[],[f13])).
% 14.71/2.24  fof(f13,axiom,(
% 14.71/2.24    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))))),
% 14.71/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_pre_topc)).
% 14.71/2.24  fof(f42,plain,(
% 14.71/2.24    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 14.71/2.24    inference(cnf_transformation,[],[f6])).
% 14.71/2.24  fof(f6,axiom,(
% 14.71/2.24    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 14.71/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 14.71/2.24  fof(f18240,plain,(
% 14.71/2.24    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)))),
% 14.71/2.24    inference(forward_demodulation,[],[f18239,f50])).
% 14.71/2.24  fof(f50,plain,(
% 14.71/2.24    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 14.71/2.24    inference(cnf_transformation,[],[f1])).
% 14.71/2.24  fof(f1,axiom,(
% 14.71/2.24    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 14.71/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 14.71/2.24  fof(f18239,plain,(
% 14.71/2.24    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)))),
% 14.71/2.24    inference(forward_demodulation,[],[f18232,f49])).
% 14.71/2.24  fof(f49,plain,(
% 14.71/2.24    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 14.71/2.24    inference(cnf_transformation,[],[f4])).
% 14.71/2.24  fof(f4,axiom,(
% 14.71/2.24    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 14.71/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 14.71/2.24  fof(f18232,plain,(
% 14.71/2.24    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))),
% 14.71/2.24    inference(backward_demodulation,[],[f156,f18231])).
% 14.71/2.24  fof(f18231,plain,(
% 14.71/2.24    ( ! [X40] : (k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X40))) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X40)))) )),
% 14.71/2.24    inference(forward_demodulation,[],[f18230,f1768])).
% 14.71/2.24  fof(f1768,plain,(
% 14.71/2.24    ( ! [X7] : (k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(sK1,X7)),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X7)))) )),
% 14.71/2.24    inference(forward_demodulation,[],[f1757,f782])).
% 14.71/2.24  fof(f782,plain,(
% 14.71/2.24    ( ! [X7] : (k4_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X7),sK2) = k2_xboole_0(sK2,k4_xboole_0(sK1,X7))) )),
% 14.71/2.24    inference(forward_demodulation,[],[f774,f50])).
% 14.71/2.24  fof(f774,plain,(
% 14.71/2.24    ( ! [X7] : (k4_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X7),sK2) = k2_xboole_0(k4_xboole_0(sK1,X7),sK2)) )),
% 14.71/2.24    inference(resolution,[],[f175,f353])).
% 14.71/2.24  fof(f353,plain,(
% 14.71/2.24    ( ! [X5] : (r1_tarski(k4_xboole_0(sK1,X5),u1_struct_0(sK0))) )),
% 14.71/2.24    inference(resolution,[],[f103,f41])).
% 14.71/2.24  fof(f41,plain,(
% 14.71/2.24    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 14.71/2.24    inference(cnf_transformation,[],[f3])).
% 14.71/2.24  fof(f3,axiom,(
% 14.71/2.24    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 14.71/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 14.71/2.24  fof(f103,plain,(
% 14.71/2.24    ( ! [X1] : (~r1_tarski(X1,sK1) | r1_tarski(X1,u1_struct_0(sK0))) )),
% 14.71/2.24    inference(resolution,[],[f84,f37])).
% 14.71/2.24  fof(f37,plain,(
% 14.71/2.24    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 14.71/2.24    inference(cnf_transformation,[],[f19])).
% 14.71/2.24  fof(f19,plain,(
% 14.71/2.24    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 14.71/2.24    inference(flattening,[],[f18])).
% 14.71/2.24  fof(f18,plain,(
% 14.71/2.24    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 14.71/2.24    inference(ennf_transformation,[],[f2])).
% 14.71/2.24  fof(f2,axiom,(
% 14.71/2.24    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 14.71/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 14.71/2.24  fof(f84,plain,(
% 14.71/2.24    r1_tarski(sK1,u1_struct_0(sK0))),
% 14.71/2.24    inference(resolution,[],[f34,f40])).
% 14.71/2.24  fof(f40,plain,(
% 14.71/2.24    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 14.71/2.24    inference(cnf_transformation,[],[f10])).
% 14.71/2.24  fof(f10,axiom,(
% 14.71/2.24    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 14.71/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 14.71/2.24  fof(f175,plain,(
% 14.71/2.24    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2)) )),
% 14.71/2.24    inference(resolution,[],[f63,f39])).
% 14.71/2.24  fof(f39,plain,(
% 14.71/2.24    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 14.71/2.24    inference(cnf_transformation,[],[f10])).
% 14.71/2.24  fof(f1757,plain,(
% 14.71/2.24    ( ! [X7] : (k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X7),sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(sK1,X7)),k2_pre_topc(sK0,sK2))) )),
% 14.71/2.24    inference(resolution,[],[f282,f353])).
% 14.71/2.24  fof(f282,plain,(
% 14.71/2.24    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X0,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK2))) )),
% 14.71/2.24    inference(resolution,[],[f68,f39])).
% 14.71/2.24  fof(f18230,plain,(
% 14.71/2.24    ( ! [X40] : (k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(sK1,X40)),k2_pre_topc(sK0,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X40)))) )),
% 14.71/2.24    inference(forward_demodulation,[],[f18204,f50])).
% 14.71/2.24  fof(f18204,plain,(
% 14.71/2.24    ( ! [X40] : (k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(sK1,X40)),k2_pre_topc(sK0,sK2)) = k2_xboole_0(k2_pre_topc(sK0,k4_xboole_0(sK1,X40)),k2_pre_topc(sK0,sK2))) )),
% 14.71/2.24    inference(resolution,[],[f7911,f1251])).
% 14.71/2.24  fof(f1251,plain,(
% 14.71/2.24    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | k4_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2)) = k2_xboole_0(X0,k2_pre_topc(sK0,sK2))) )),
% 14.71/2.24    inference(resolution,[],[f112,f39])).
% 14.71/2.24  fof(f112,plain,(
% 14.71/2.24    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(X6,k2_pre_topc(sK0,sK2)) = k4_subset_1(u1_struct_0(sK0),X6,k2_pre_topc(sK0,sK2))) )),
% 14.71/2.24    inference(resolution,[],[f71,f47])).
% 14.71/2.24  fof(f7911,plain,(
% 14.71/2.24    ( ! [X10] : (r1_tarski(k2_pre_topc(sK0,k4_xboole_0(sK1,X10)),u1_struct_0(sK0))) )),
% 14.71/2.24    inference(resolution,[],[f1536,f133])).
% 14.71/2.24  fof(f133,plain,(
% 14.71/2.24    r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))),
% 14.71/2.24    inference(resolution,[],[f89,f40])).
% 14.71/2.24  fof(f1536,plain,(
% 14.71/2.24    ( ! [X8,X9] : (~r1_tarski(k2_pre_topc(sK0,sK1),X9) | r1_tarski(k2_pre_topc(sK0,k4_xboole_0(sK1,X8)),X9)) )),
% 14.71/2.24    inference(subsumption_resolution,[],[f1534,f555])).
% 14.71/2.24  fof(f555,plain,(
% 14.71/2.24    ( ! [X2] : (m1_subset_1(k4_xboole_0(sK1,X2),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 14.71/2.24    inference(resolution,[],[f353,f39])).
% 14.71/2.24  fof(f1534,plain,(
% 14.71/2.24    ( ! [X8,X9] : (~m1_subset_1(k4_xboole_0(sK1,X8),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k2_pre_topc(sK0,sK1),X9) | r1_tarski(k2_pre_topc(sK0,k4_xboole_0(sK1,X8)),X9)) )),
% 14.71/2.24    inference(resolution,[],[f263,f41])).
% 14.71/2.24  fof(f263,plain,(
% 14.71/2.24    ( ! [X6,X5] : (~r1_tarski(X5,sK1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k2_pre_topc(sK0,sK1),X6) | r1_tarski(k2_pre_topc(sK0,X5),X6)) )),
% 14.71/2.24    inference(resolution,[],[f90,f37])).
% 14.71/2.24  fof(f90,plain,(
% 14.71/2.24    ( ! [X2] : (r1_tarski(k2_pre_topc(sK0,X2),k2_pre_topc(sK0,sK1)) | ~r1_tarski(X2,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 14.71/2.24    inference(subsumption_resolution,[],[f77,f36])).
% 14.71/2.24  fof(f77,plain,(
% 14.71/2.24    ( ! [X2] : (~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1) | r1_tarski(k2_pre_topc(sK0,X2),k2_pre_topc(sK0,sK1))) )),
% 14.71/2.24    inference(resolution,[],[f34,f43])).
% 14.71/2.24  fof(f43,plain,(
% 14.71/2.24    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) )),
% 14.71/2.24    inference(cnf_transformation,[],[f22])).
% 14.71/2.24  fof(f22,plain,(
% 14.71/2.24    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 14.71/2.24    inference(flattening,[],[f21])).
% 14.71/2.24  fof(f21,plain,(
% 14.71/2.24    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 14.71/2.24    inference(ennf_transformation,[],[f12])).
% 14.71/2.24  fof(f12,axiom,(
% 14.71/2.24    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 14.71/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).
% 14.71/2.24  fof(f156,plain,(
% 14.71/2.24    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))))),
% 14.71/2.24    inference(resolution,[],[f96,f38])).
% 14.71/2.24  fof(f38,plain,(
% 14.71/2.24    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 14.71/2.24    inference(cnf_transformation,[],[f20])).
% 14.71/2.24  fof(f20,plain,(
% 14.71/2.24    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 14.71/2.24    inference(ennf_transformation,[],[f5])).
% 14.71/2.24  fof(f5,axiom,(
% 14.71/2.24    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 14.71/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 14.71/2.24  fof(f96,plain,(
% 14.71/2.24    ~r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))),
% 14.71/2.24    inference(subsumption_resolution,[],[f95,f89])).
% 14.71/2.24  fof(f95,plain,(
% 14.71/2.24    ~r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 14.71/2.24    inference(superposition,[],[f92,f44])).
% 14.71/2.24  fof(f44,plain,(
% 14.71/2.24    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 14.71/2.24    inference(cnf_transformation,[],[f23])).
% 14.71/2.24  fof(f23,plain,(
% 14.71/2.24    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 14.71/2.24    inference(ennf_transformation,[],[f9])).
% 14.71/2.24  fof(f9,axiom,(
% 14.71/2.24    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 14.71/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 14.71/2.24  fof(f92,plain,(
% 14.71/2.24    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))),
% 14.71/2.24    inference(backward_demodulation,[],[f33,f83])).
% 14.71/2.24  fof(f83,plain,(
% 14.71/2.24    ( ! [X8] : (k7_subset_1(u1_struct_0(sK0),sK1,X8) = k4_xboole_0(sK1,X8)) )),
% 14.71/2.24    inference(resolution,[],[f34,f44])).
% 14.71/2.24  fof(f33,plain,(
% 14.71/2.24    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 14.71/2.24    inference(cnf_transformation,[],[f17])).
% 14.71/2.24  % SZS output end Proof for theBenchmark
% 14.71/2.24  % (8056)------------------------------
% 14.71/2.24  % (8056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.71/2.24  % (8056)Termination reason: Refutation
% 14.71/2.24  
% 14.71/2.24  % (8056)Memory used [KB]: 18549
% 14.71/2.24  % (8056)Time elapsed: 1.788 s
% 14.71/2.24  % (8056)------------------------------
% 14.71/2.24  % (8056)------------------------------
% 14.71/2.25  % (8034)Success in time 1.878 s
%------------------------------------------------------------------------------
