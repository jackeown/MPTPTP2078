%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:46 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 460 expanded)
%              Number of leaves         :   15 (  90 expanded)
%              Depth                    :   20
%              Number of atoms          :  252 (1563 expanded)
%              Number of equality atoms :   68 ( 318 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1794,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1769,f1453])).

fof(f1453,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f1443])).

fof(f1443,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f109,f1426])).

fof(f1426,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(resolution,[],[f542,f104])).

fof(f104,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f86,f83])).

fof(f83,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f38,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
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
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f86,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f38,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f542,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ) ),
    inference(subsumption_resolution,[],[f541,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f541,plain,(
    ! [X0] :
      ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f236,f39])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f235,f145])).

fof(f145,plain,
    ( v3_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f36,f127])).

fof(f127,plain,(
    ! [X8] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X8) = k4_xboole_0(k2_pre_topc(sK0,sK1),X8) ),
    inference(resolution,[],[f97,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f97,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f78,f40])).

fof(f78,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f38,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f36,plain,
    ( v3_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f235,plain,(
    ! [X0,X1] :
      ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(forward_demodulation,[],[f234,f127])).

fof(f234,plain,(
    ! [X0,X1] :
      ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f233,f38])).

fof(f233,plain,(
    ! [X0,X1] :
      ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f230,f40])).

fof(f230,plain,(
    ! [X0,X1] :
      ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(superposition,[],[f95,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f95,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f76,f40])).

fof(f76,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f38,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f109,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f108,f97])).

fof(f108,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f37,f41])).

fof(f37,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f1769,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f100,f1765])).

fof(f1765,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f198,f1764])).

fof(f1764,plain,(
    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1763,f157])).

fof(f157,plain,(
    ! [X3] : k9_subset_1(k2_pre_topc(sK0,sK1),X3,X3) = X3 ),
    inference(resolution,[],[f111,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f111,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f98,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f98,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f79,f40])).

fof(f79,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f38,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f1763,plain,(
    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1) ),
    inference(forward_demodulation,[],[f1760,f1445])).

fof(f1445,plain,(
    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f159,f1426])).

fof(f159,plain,(
    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) ),
    inference(backward_demodulation,[],[f152,f153])).

fof(f153,plain,(
    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    inference(resolution,[],[f111,f43])).

fof(f152,plain,(
    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) ),
    inference(resolution,[],[f111,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1760,plain,(
    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f160,f773])).

fof(f773,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f406,f55])).

fof(f406,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[],[f52,f237])).

fof(f237,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f231,f97])).

fof(f231,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f95,f41])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f160,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
      | k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),X1)) = k4_xboole_0(sK1,X1) ) ),
    inference(forward_demodulation,[],[f154,f151])).

fof(f151,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X0) ),
    inference(resolution,[],[f111,f41])).

fof(f154,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
      | k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X1) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),X1)) ) ),
    inference(resolution,[],[f111,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f198,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f197,f38])).

fof(f197,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f195,f40])).

fof(f195,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f81,f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f81,plain,(
    ! [X8] : k7_subset_1(u1_struct_0(sK0),sK1,X8) = k4_xboole_0(sK1,X8) ),
    inference(resolution,[],[f38,f41])).

fof(f100,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f99,f40])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f80,f39])).

fof(f80,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(resolution,[],[f38,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (3823)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.49  % (3819)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (3832)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.50  % (3835)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.50  % (3822)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (3825)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (3820)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (3836)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.50  % (3840)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.50  % (3839)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (3838)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (3841)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (3821)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (3831)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (3821)Refutation not found, incomplete strategy% (3821)------------------------------
% 0.21/0.51  % (3821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3821)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (3821)Memory used [KB]: 10618
% 0.21/0.51  % (3821)Time elapsed: 0.092 s
% 0.21/0.51  % (3821)------------------------------
% 0.21/0.51  % (3821)------------------------------
% 0.21/0.51  % (3827)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (3830)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (3826)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % (3833)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.52  % (3824)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (3818)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.52  % (3837)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.53  % (3842)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.53  % (3834)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.53  % (3828)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.53  % (3828)Refutation not found, incomplete strategy% (3828)------------------------------
% 0.21/0.53  % (3828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3828)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3828)Memory used [KB]: 10618
% 0.21/0.53  % (3828)Time elapsed: 0.127 s
% 0.21/0.53  % (3828)------------------------------
% 0.21/0.53  % (3828)------------------------------
% 0.21/0.55  % (3842)Refutation not found, incomplete strategy% (3842)------------------------------
% 0.21/0.55  % (3842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3842)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3842)Memory used [KB]: 10618
% 0.21/0.55  % (3842)Time elapsed: 0.138 s
% 0.21/0.55  % (3842)------------------------------
% 0.21/0.55  % (3842)------------------------------
% 1.74/0.57  % (3840)Refutation found. Thanks to Tanya!
% 1.74/0.57  % SZS status Theorem for theBenchmark
% 1.74/0.57  % SZS output start Proof for theBenchmark
% 1.74/0.57  fof(f1794,plain,(
% 1.74/0.57    $false),
% 1.74/0.57    inference(subsumption_resolution,[],[f1769,f1453])).
% 1.74/0.57  fof(f1453,plain,(
% 1.74/0.57    ~v3_pre_topc(sK1,sK0)),
% 1.74/0.57    inference(trivial_inequality_removal,[],[f1443])).
% 1.74/0.57  fof(f1443,plain,(
% 1.74/0.57    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.74/0.57    inference(backward_demodulation,[],[f109,f1426])).
% 1.74/0.57  fof(f1426,plain,(
% 1.74/0.57    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 1.74/0.57    inference(resolution,[],[f542,f104])).
% 1.74/0.57  fof(f104,plain,(
% 1.74/0.57    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.74/0.57    inference(forward_demodulation,[],[f86,f83])).
% 1.74/0.57  fof(f83,plain,(
% 1.74/0.57    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 1.74/0.57    inference(resolution,[],[f38,f43])).
% 1.74/0.57  fof(f43,plain,(
% 1.74/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.74/0.57    inference(cnf_transformation,[],[f23])).
% 1.74/0.57  fof(f23,plain,(
% 1.74/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.74/0.57    inference(ennf_transformation,[],[f2])).
% 1.74/0.57  fof(f2,axiom,(
% 1.74/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.74/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.74/0.57  fof(f38,plain,(
% 1.74/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.74/0.57    inference(cnf_transformation,[],[f20])).
% 1.74/0.57  fof(f20,plain,(
% 1.74/0.57    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.74/0.57    inference(flattening,[],[f19])).
% 1.74/0.57  fof(f19,plain,(
% 1.74/0.57    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.74/0.57    inference(ennf_transformation,[],[f18])).
% 1.74/0.57  fof(f18,negated_conjecture,(
% 1.74/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.74/0.57    inference(negated_conjecture,[],[f17])).
% 1.74/0.57  fof(f17,conjecture,(
% 1.74/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.74/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 1.74/0.57  fof(f86,plain,(
% 1.74/0.57    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.74/0.57    inference(resolution,[],[f38,f53])).
% 1.74/0.57  fof(f53,plain,(
% 1.74/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.74/0.57    inference(cnf_transformation,[],[f34])).
% 1.74/0.57  fof(f34,plain,(
% 1.74/0.57    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.74/0.57    inference(ennf_transformation,[],[f3])).
% 1.74/0.57  fof(f3,axiom,(
% 1.74/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.74/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.74/0.57  fof(f542,plain,(
% 1.74/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) )),
% 1.74/0.57    inference(subsumption_resolution,[],[f541,f40])).
% 1.74/0.57  fof(f40,plain,(
% 1.74/0.57    l1_pre_topc(sK0)),
% 1.74/0.57    inference(cnf_transformation,[],[f20])).
% 1.74/0.57  fof(f541,plain,(
% 1.74/0.57    ( ! [X0] : (k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.74/0.57    inference(resolution,[],[f236,f39])).
% 1.74/0.57  fof(f39,plain,(
% 1.74/0.57    v2_pre_topc(sK0)),
% 1.74/0.57    inference(cnf_transformation,[],[f20])).
% 1.74/0.57  fof(f236,plain,(
% 1.74/0.57    ( ! [X0,X1] : (~v2_pre_topc(X0) | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.74/0.57    inference(subsumption_resolution,[],[f235,f145])).
% 1.74/0.57  fof(f145,plain,(
% 1.74/0.57    v3_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 1.74/0.57    inference(backward_demodulation,[],[f36,f127])).
% 1.74/0.57  fof(f127,plain,(
% 1.74/0.57    ( ! [X8] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X8) = k4_xboole_0(k2_pre_topc(sK0,sK1),X8)) )),
% 1.74/0.57    inference(resolution,[],[f97,f41])).
% 1.74/0.57  fof(f41,plain,(
% 1.74/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.74/0.57    inference(cnf_transformation,[],[f21])).
% 1.74/0.57  fof(f21,plain,(
% 1.74/0.57    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.74/0.57    inference(ennf_transformation,[],[f6])).
% 1.74/0.57  fof(f6,axiom,(
% 1.74/0.57    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.74/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.74/0.57  fof(f97,plain,(
% 1.74/0.57    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.74/0.57    inference(subsumption_resolution,[],[f78,f40])).
% 1.74/0.57  fof(f78,plain,(
% 1.74/0.57    ~l1_pre_topc(sK0) | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.74/0.57    inference(resolution,[],[f38,f49])).
% 1.74/0.57  fof(f49,plain,(
% 1.74/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.74/0.57    inference(cnf_transformation,[],[f30])).
% 1.74/0.57  fof(f30,plain,(
% 1.74/0.57    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.74/0.57    inference(flattening,[],[f29])).
% 1.74/0.57  fof(f29,plain,(
% 1.74/0.57    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.74/0.57    inference(ennf_transformation,[],[f11])).
% 1.74/0.57  fof(f11,axiom,(
% 1.74/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.74/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.74/0.57  fof(f36,plain,(
% 1.74/0.57    v3_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 1.74/0.57    inference(cnf_transformation,[],[f20])).
% 1.74/0.57  fof(f235,plain,(
% 1.74/0.57    ( ! [X0,X1] : (k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(sK1,sK0)) )),
% 1.74/0.57    inference(forward_demodulation,[],[f234,f127])).
% 1.74/0.57  fof(f234,plain,(
% 1.74/0.57    ( ! [X0,X1] : (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(sK1,sK0)) )),
% 1.74/0.57    inference(subsumption_resolution,[],[f233,f38])).
% 1.74/0.57  fof(f233,plain,(
% 1.74/0.57    ( ! [X0,X1] : (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)) )),
% 1.74/0.57    inference(subsumption_resolution,[],[f230,f40])).
% 1.74/0.57  fof(f230,plain,(
% 1.74/0.57    ( ! [X0,X1] : (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)) )),
% 1.74/0.57    inference(superposition,[],[f95,f45])).
% 1.74/0.57  fof(f45,plain,(
% 1.74/0.57    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3) )),
% 1.74/0.57    inference(cnf_transformation,[],[f25])).
% 1.74/0.57  fof(f25,plain,(
% 1.74/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.74/0.57    inference(flattening,[],[f24])).
% 1.74/0.57  fof(f24,plain,(
% 1.74/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.74/0.57    inference(ennf_transformation,[],[f15])).
% 1.74/0.57  fof(f15,axiom,(
% 1.74/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.74/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 1.74/0.57  fof(f95,plain,(
% 1.74/0.57    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 1.74/0.57    inference(subsumption_resolution,[],[f76,f40])).
% 1.74/0.57  fof(f76,plain,(
% 1.74/0.57    ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 1.74/0.57    inference(resolution,[],[f38,f46])).
% 1.74/0.57  fof(f46,plain,(
% 1.74/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 1.74/0.57    inference(cnf_transformation,[],[f26])).
% 1.74/0.57  fof(f26,plain,(
% 1.74/0.57    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.74/0.57    inference(ennf_transformation,[],[f14])).
% 1.74/0.57  fof(f14,axiom,(
% 1.74/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.74/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 1.74/0.57  fof(f109,plain,(
% 1.74/0.57    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.74/0.57    inference(subsumption_resolution,[],[f108,f97])).
% 1.74/0.57  fof(f108,plain,(
% 1.74/0.57    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.74/0.57    inference(superposition,[],[f37,f41])).
% 1.74/0.57  fof(f37,plain,(
% 1.74/0.57    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.74/0.57    inference(cnf_transformation,[],[f20])).
% 1.74/0.57  fof(f1769,plain,(
% 1.74/0.57    v3_pre_topc(sK1,sK0)),
% 1.74/0.57    inference(backward_demodulation,[],[f100,f1765])).
% 1.74/0.57  fof(f1765,plain,(
% 1.74/0.57    sK1 = k1_tops_1(sK0,sK1)),
% 1.74/0.57    inference(backward_demodulation,[],[f198,f1764])).
% 1.74/0.57  fof(f1764,plain,(
% 1.74/0.57    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.74/0.57    inference(forward_demodulation,[],[f1763,f157])).
% 1.74/0.57  fof(f157,plain,(
% 1.74/0.57    ( ! [X3] : (k9_subset_1(k2_pre_topc(sK0,sK1),X3,X3) = X3) )),
% 1.74/0.57    inference(resolution,[],[f111,f54])).
% 1.74/0.57  fof(f54,plain,(
% 1.74/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X1) = X1) )),
% 1.74/0.57    inference(cnf_transformation,[],[f35])).
% 1.74/0.57  fof(f35,plain,(
% 1.74/0.57    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.74/0.57    inference(ennf_transformation,[],[f4])).
% 1.74/0.57  fof(f4,axiom,(
% 1.74/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 1.74/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 1.74/0.57  fof(f111,plain,(
% 1.74/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 1.74/0.57    inference(resolution,[],[f98,f55])).
% 1.74/0.57  fof(f55,plain,(
% 1.74/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.74/0.57    inference(cnf_transformation,[],[f9])).
% 1.74/0.57  fof(f9,axiom,(
% 1.74/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.74/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.74/0.57  fof(f98,plain,(
% 1.74/0.57    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 1.74/0.57    inference(subsumption_resolution,[],[f79,f40])).
% 1.74/0.57  fof(f79,plain,(
% 1.74/0.57    ~l1_pre_topc(sK0) | r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 1.74/0.57    inference(resolution,[],[f38,f50])).
% 1.74/0.57  fof(f50,plain,(
% 1.74/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 1.74/0.57    inference(cnf_transformation,[],[f31])).
% 1.74/0.57  fof(f31,plain,(
% 1.74/0.57    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.74/0.57    inference(ennf_transformation,[],[f12])).
% 1.74/0.57  fof(f12,axiom,(
% 1.74/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 1.74/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 1.74/0.57  fof(f1763,plain,(
% 1.74/0.57    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1)),
% 1.74/0.57    inference(forward_demodulation,[],[f1760,f1445])).
% 1.74/0.57  fof(f1445,plain,(
% 1.74/0.57    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 1.74/0.57    inference(backward_demodulation,[],[f159,f1426])).
% 1.74/0.57  fof(f159,plain,(
% 1.74/0.57    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1))),
% 1.74/0.57    inference(backward_demodulation,[],[f152,f153])).
% 1.74/0.57  fof(f153,plain,(
% 1.74/0.57    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 1.74/0.57    inference(resolution,[],[f111,f43])).
% 1.74/0.57  fof(f152,plain,(
% 1.74/0.57    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))),
% 1.74/0.57    inference(resolution,[],[f111,f42])).
% 1.74/0.57  fof(f42,plain,(
% 1.74/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.74/0.57    inference(cnf_transformation,[],[f22])).
% 1.74/0.57  fof(f22,plain,(
% 1.74/0.57    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.74/0.57    inference(ennf_transformation,[],[f5])).
% 1.74/0.57  fof(f5,axiom,(
% 1.74/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.74/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.74/0.57  fof(f1760,plain,(
% 1.74/0.57    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))),
% 1.74/0.57    inference(resolution,[],[f160,f773])).
% 1.74/0.57  fof(f773,plain,(
% 1.74/0.57    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 1.74/0.57    inference(resolution,[],[f406,f55])).
% 1.74/0.57  fof(f406,plain,(
% 1.74/0.57    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 1.74/0.57    inference(superposition,[],[f52,f237])).
% 1.74/0.57  fof(f237,plain,(
% 1.74/0.57    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 1.74/0.57    inference(subsumption_resolution,[],[f231,f97])).
% 1.74/0.57  fof(f231,plain,(
% 1.74/0.57    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.74/0.57    inference(superposition,[],[f95,f41])).
% 1.74/0.57  fof(f52,plain,(
% 1.74/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.74/0.57    inference(cnf_transformation,[],[f1])).
% 1.74/0.57  fof(f1,axiom,(
% 1.74/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.74/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.74/0.57  fof(f160,plain,(
% 1.74/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),X1)) = k4_xboole_0(sK1,X1)) )),
% 1.74/0.57    inference(forward_demodulation,[],[f154,f151])).
% 1.74/0.57  fof(f151,plain,(
% 1.74/0.57    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X0)) )),
% 1.74/0.57    inference(resolution,[],[f111,f41])).
% 1.74/0.57  fof(f154,plain,(
% 1.74/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X1) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),X1))) )),
% 1.74/0.57    inference(resolution,[],[f111,f48])).
% 1.74/0.57  fof(f48,plain,(
% 1.74/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))) )),
% 1.74/0.57    inference(cnf_transformation,[],[f28])).
% 1.74/0.57  fof(f28,plain,(
% 1.74/0.57    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.74/0.57    inference(ennf_transformation,[],[f7])).
% 1.74/0.57  fof(f7,axiom,(
% 1.74/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.74/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 1.74/0.57  fof(f198,plain,(
% 1.74/0.57    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.74/0.57    inference(subsumption_resolution,[],[f197,f38])).
% 1.74/0.57  fof(f197,plain,(
% 1.74/0.57    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.74/0.57    inference(subsumption_resolution,[],[f195,f40])).
% 1.74/0.57  fof(f195,plain,(
% 1.74/0.57    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.74/0.57    inference(superposition,[],[f81,f47])).
% 1.74/0.57  fof(f47,plain,(
% 1.74/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 1.74/0.57    inference(cnf_transformation,[],[f27])).
% 1.74/0.57  fof(f27,plain,(
% 1.74/0.57    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.74/0.57    inference(ennf_transformation,[],[f16])).
% 1.74/0.57  fof(f16,axiom,(
% 1.74/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.74/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 1.74/0.57  fof(f81,plain,(
% 1.74/0.57    ( ! [X8] : (k7_subset_1(u1_struct_0(sK0),sK1,X8) = k4_xboole_0(sK1,X8)) )),
% 1.74/0.57    inference(resolution,[],[f38,f41])).
% 1.74/0.57  fof(f100,plain,(
% 1.74/0.57    v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.74/0.57    inference(subsumption_resolution,[],[f99,f40])).
% 1.74/0.57  fof(f99,plain,(
% 1.74/0.57    ~l1_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.74/0.57    inference(subsumption_resolution,[],[f80,f39])).
% 1.74/0.57  fof(f80,plain,(
% 1.74/0.57    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.74/0.57    inference(resolution,[],[f38,f51])).
% 1.74/0.57  fof(f51,plain,(
% 1.74/0.57    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 1.74/0.57    inference(cnf_transformation,[],[f33])).
% 1.74/0.57  fof(f33,plain,(
% 1.74/0.57    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.74/0.57    inference(flattening,[],[f32])).
% 1.74/0.57  fof(f32,plain,(
% 1.74/0.57    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.74/0.57    inference(ennf_transformation,[],[f13])).
% 1.74/0.57  fof(f13,axiom,(
% 1.74/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.74/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.74/0.57  % SZS output end Proof for theBenchmark
% 1.74/0.57  % (3840)------------------------------
% 1.74/0.57  % (3840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.57  % (3840)Termination reason: Refutation
% 1.74/0.57  
% 1.74/0.57  % (3840)Memory used [KB]: 2686
% 1.74/0.57  % (3840)Time elapsed: 0.164 s
% 1.74/0.57  % (3840)------------------------------
% 1.74/0.57  % (3840)------------------------------
% 1.74/0.58  % (3813)Success in time 0.22 s
%------------------------------------------------------------------------------
