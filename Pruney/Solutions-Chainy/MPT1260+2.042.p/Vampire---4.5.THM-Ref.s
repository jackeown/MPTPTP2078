%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:40 EST 2020

% Result     : Theorem 5.43s
% Output     : Refutation 5.43s
% Verified   : 
% Statistics : Number of formulae       :  158 (3767 expanded)
%              Number of leaves         :   25 ( 996 expanded)
%              Depth                    :   34
%              Number of atoms          :  388 (18650 expanded)
%              Number of equality atoms :  130 (5228 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6702,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6701,f70])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f60,f62,f61])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f6701,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f6698,f6654])).

fof(f6654,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f6624])).

fof(f6624,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f485,f6623])).

fof(f6623,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f483,f6507])).

fof(f6507,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f1764,f6453])).

fof(f6453,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f6452,f868])).

fof(f868,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f656,f431])).

fof(f431,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f428,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f428,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f85,f424])).

fof(f424,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f283,f118])).

fof(f118,plain,(
    ! [X2] : k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2) ),
    inference(resolution,[],[f70,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f283,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f111,f70])).

fof(f111,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X4) = k7_subset_1(u1_struct_0(sK0),X4,k2_tops_1(sK0,X4)) ) ),
    inference(resolution,[],[f69,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f656,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | k1_xboole_0 != k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f91,f429])).

fof(f429,plain,(
    k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f84,f424])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f91,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f6452,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f6451,f405])).

fof(f405,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f404,f354])).

fof(f354,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f350,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f350,plain,(
    r1_tarski(k1_xboole_0,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f85,f346])).

fof(f346,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f332,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f332,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f325,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f325,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f324,f69])).

fof(f324,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f323,f145])).

fof(f145,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f144,f70])).

fof(f144,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f89,f117])).

fof(f117,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f70,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f323,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f77,f233])).

fof(f233,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f226,f119])).

fof(f119,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f114,f117])).

fof(f114,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f70,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f226,plain,(
    k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f109,f145])).

fof(f109,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,X2) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X2)) ) ),
    inference(resolution,[],[f69,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f404,plain,(
    k3_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f403,f101])).

fof(f101,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f403,plain,(
    k3_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0) = k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f84,f353])).

fof(f353,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f351,f343])).

fof(f343,plain,(
    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f332,f98])).

fof(f351,plain,(
    k3_xboole_0(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = k4_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f84,f346])).

fof(f6451,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f6450,f101])).

fof(f6450,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(superposition,[],[f84,f822])).

fof(f822,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f821,f70])).

fof(f821,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f815,f105])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f815,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f487,f431])).

fof(f487,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k1_tops_1(sK0,X0))
      | ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ) ),
    inference(backward_demodulation,[],[f376,f483])).

fof(f376,plain,(
    ! [X0] :
      ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
      | ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(sK1,k1_tops_1(sK0,X0)) ) ),
    inference(backward_demodulation,[],[f322,f372])).

fof(f372,plain,(
    ! [X2] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X2) = k4_xboole_0(k2_pre_topc(sK0,sK1),X2) ),
    inference(resolution,[],[f360,f73])).

fof(f360,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f359,f70])).

fof(f359,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f358,f325])).

fof(f358,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f87,f263])).

fof(f263,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f110,f70])).

fof(f110,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X3) = k4_subset_1(u1_struct_0(sK0),X3,k2_tops_1(sK0,X3)) ) ),
    inference(resolution,[],[f69,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f322,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(sK1,k1_tops_1(sK0,X0))
      | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ) ),
    inference(subsumption_resolution,[],[f320,f70])).

fof(f320,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(sK1,k1_tops_1(sK0,X0))
      | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ) ),
    inference(resolution,[],[f108,f71])).

fof(f71,plain,
    ( v3_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X0,k1_tops_1(sK0,X1)) ) ),
    inference(resolution,[],[f69,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f1764,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f372,f305])).

fof(f305,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f112,f70])).

fof(f112,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,X5) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X5),k1_tops_1(sK0,X5)) ) ),
    inference(resolution,[],[f69,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f483,plain,(
    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f83,f472])).

fof(f472,plain,(
    k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f464,f340])).

fof(f340,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f338,f339])).

fof(f339,plain,(
    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f331,f263])).

fof(f331,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f325,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_xboole_0(sK1,X0) = k4_subset_1(u1_struct_0(sK0),sK1,X0) ) ),
    inference(resolution,[],[f70,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f338,plain,(
    k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f330,f99])).

fof(f99,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f330,plain,(
    k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f325,f116])).

fof(f116,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_xboole_0(X1,sK1) = k4_subset_1(u1_struct_0(sK0),X1,sK1) ) ),
    inference(resolution,[],[f70,f86])).

fof(f464,plain,(
    k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f201,f332])).

fof(f201,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | k2_xboole_0(X0,sK1) = k4_subset_1(u1_struct_0(sK0),X0,sK1) ) ),
    inference(resolution,[],[f116,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f485,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) != k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f378,f483])).

fof(f378,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f72,f372])).

fof(f72,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f6698,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f107,f6453])).

fof(f107,plain,(
    ! [X0] :
      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f106,f69])).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ) ),
    inference(resolution,[],[f68,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f68,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:52:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (26724)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (26729)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.50  % (26705)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (26715)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (26703)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (26706)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (26712)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (26710)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (26728)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (26713)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (26721)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (26725)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (26704)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (26701)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (26707)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (26716)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (26719)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (26722)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (26726)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (26727)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (26717)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (26730)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (26709)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (26711)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (26718)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (26702)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (26714)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (26723)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (26708)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (26731)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 3.29/0.82  % (26726)Time limit reached!
% 3.29/0.82  % (26726)------------------------------
% 3.29/0.82  % (26726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.82  % (26726)Termination reason: Time limit
% 3.29/0.82  % (26726)Termination phase: Saturation
% 3.29/0.82  
% 3.29/0.82  % (26726)Memory used [KB]: 13176
% 3.29/0.82  % (26726)Time elapsed: 0.420 s
% 3.29/0.82  % (26726)------------------------------
% 3.29/0.82  % (26726)------------------------------
% 3.29/0.84  % (26703)Time limit reached!
% 3.29/0.84  % (26703)------------------------------
% 3.29/0.84  % (26703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.84  % (26703)Termination reason: Time limit
% 3.29/0.84  
% 3.29/0.84  % (26703)Memory used [KB]: 6652
% 3.29/0.84  % (26703)Time elapsed: 0.437 s
% 3.29/0.84  % (26703)------------------------------
% 3.29/0.84  % (26703)------------------------------
% 4.18/0.89  % (26731)Time limit reached!
% 4.18/0.89  % (26731)------------------------------
% 4.18/0.89  % (26731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.89  % (26731)Termination reason: Time limit
% 4.18/0.89  % (26731)Termination phase: Saturation
% 4.18/0.89  
% 4.18/0.89  % (26731)Memory used [KB]: 3582
% 4.18/0.89  % (26731)Time elapsed: 0.500 s
% 4.18/0.89  % (26731)------------------------------
% 4.18/0.89  % (26731)------------------------------
% 4.46/0.94  % (26707)Time limit reached!
% 4.46/0.94  % (26707)------------------------------
% 4.46/0.94  % (26707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/0.94  % (26707)Termination reason: Time limit
% 4.46/0.94  % (26707)Termination phase: Saturation
% 4.46/0.94  
% 4.46/0.94  % (26707)Memory used [KB]: 15479
% 4.46/0.94  % (26707)Time elapsed: 0.500 s
% 4.46/0.94  % (26707)------------------------------
% 4.46/0.94  % (26707)------------------------------
% 4.46/0.96  % (26817)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 4.46/0.98  % (26818)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.46/1.00  % (26708)Time limit reached!
% 4.46/1.00  % (26708)------------------------------
% 4.46/1.00  % (26708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/1.00  % (26708)Termination reason: Time limit
% 4.46/1.00  % (26708)Termination phase: Saturation
% 4.46/1.00  
% 4.46/1.00  % (26708)Memory used [KB]: 5884
% 4.46/1.00  % (26708)Time elapsed: 0.600 s
% 4.46/1.00  % (26708)------------------------------
% 4.46/1.00  % (26708)------------------------------
% 4.97/1.01  % (26715)Time limit reached!
% 4.97/1.01  % (26715)------------------------------
% 4.97/1.01  % (26715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.03  % (26819)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.97/1.03  % (26715)Termination reason: Time limit
% 4.97/1.03  % (26715)Termination phase: Saturation
% 4.97/1.03  
% 4.97/1.03  % (26715)Memory used [KB]: 8315
% 4.97/1.03  % (26715)Time elapsed: 0.500 s
% 4.97/1.03  % (26715)------------------------------
% 4.97/1.03  % (26715)------------------------------
% 5.43/1.08  % (26820)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 5.43/1.12  % (26821)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.43/1.15  % (26822)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.43/1.17  % (26719)Refutation found. Thanks to Tanya!
% 5.43/1.17  % SZS status Theorem for theBenchmark
% 5.43/1.17  % SZS output start Proof for theBenchmark
% 5.43/1.17  fof(f6702,plain,(
% 5.43/1.17    $false),
% 5.43/1.17    inference(subsumption_resolution,[],[f6701,f70])).
% 5.43/1.17  fof(f70,plain,(
% 5.43/1.17    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.43/1.17    inference(cnf_transformation,[],[f63])).
% 5.43/1.17  fof(f63,plain,(
% 5.43/1.17    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 5.43/1.17    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f60,f62,f61])).
% 5.43/1.17  fof(f61,plain,(
% 5.43/1.17    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 5.43/1.17    introduced(choice_axiom,[])).
% 5.43/1.17  fof(f62,plain,(
% 5.43/1.17    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 5.43/1.17    introduced(choice_axiom,[])).
% 5.43/1.17  fof(f60,plain,(
% 5.43/1.17    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 5.43/1.17    inference(flattening,[],[f59])).
% 5.43/1.17  fof(f59,plain,(
% 5.43/1.17    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 5.43/1.17    inference(nnf_transformation,[],[f36])).
% 5.43/1.17  fof(f36,plain,(
% 5.43/1.17    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 5.43/1.17    inference(flattening,[],[f35])).
% 5.43/1.17  fof(f35,plain,(
% 5.43/1.17    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 5.43/1.17    inference(ennf_transformation,[],[f34])).
% 5.43/1.17  fof(f34,negated_conjecture,(
% 5.43/1.17    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 5.43/1.17    inference(negated_conjecture,[],[f33])).
% 5.43/1.17  fof(f33,conjecture,(
% 5.43/1.17    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 5.43/1.17  fof(f6701,plain,(
% 5.43/1.17    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.43/1.17    inference(subsumption_resolution,[],[f6698,f6654])).
% 5.43/1.17  fof(f6654,plain,(
% 5.43/1.17    ~v3_pre_topc(sK1,sK0)),
% 5.43/1.17    inference(trivial_inequality_removal,[],[f6624])).
% 5.43/1.17  fof(f6624,plain,(
% 5.43/1.17    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 5.43/1.17    inference(backward_demodulation,[],[f485,f6623])).
% 5.43/1.17  fof(f6623,plain,(
% 5.43/1.17    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 5.43/1.17    inference(backward_demodulation,[],[f483,f6507])).
% 5.43/1.17  fof(f6507,plain,(
% 5.43/1.17    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 5.43/1.17    inference(backward_demodulation,[],[f1764,f6453])).
% 5.43/1.17  fof(f6453,plain,(
% 5.43/1.17    sK1 = k1_tops_1(sK0,sK1)),
% 5.43/1.17    inference(subsumption_resolution,[],[f6452,f868])).
% 5.43/1.17  fof(f868,plain,(
% 5.43/1.17    k1_xboole_0 != k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1)),
% 5.43/1.17    inference(resolution,[],[f656,f431])).
% 5.43/1.17  fof(f431,plain,(
% 5.43/1.17    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1)),
% 5.43/1.17    inference(resolution,[],[f428,f97])).
% 5.43/1.17  fof(f97,plain,(
% 5.43/1.17    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 5.43/1.17    inference(cnf_transformation,[],[f67])).
% 5.43/1.17  fof(f67,plain,(
% 5.43/1.17    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 5.43/1.17    inference(flattening,[],[f66])).
% 5.43/1.17  fof(f66,plain,(
% 5.43/1.17    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 5.43/1.17    inference(nnf_transformation,[],[f3])).
% 5.43/1.17  fof(f3,axiom,(
% 5.43/1.17    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 5.43/1.17  fof(f428,plain,(
% 5.43/1.17    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 5.43/1.17    inference(superposition,[],[f85,f424])).
% 5.43/1.17  fof(f424,plain,(
% 5.43/1.17    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 5.43/1.17    inference(superposition,[],[f283,f118])).
% 5.43/1.17  fof(f118,plain,(
% 5.43/1.17    ( ! [X2] : (k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2)) )),
% 5.43/1.17    inference(resolution,[],[f70,f73])).
% 5.43/1.17  fof(f73,plain,(
% 5.43/1.17    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 5.43/1.17    inference(cnf_transformation,[],[f37])).
% 5.43/1.17  fof(f37,plain,(
% 5.43/1.17    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.43/1.17    inference(ennf_transformation,[],[f20])).
% 5.43/1.17  fof(f20,axiom,(
% 5.43/1.17    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 5.43/1.17  fof(f283,plain,(
% 5.43/1.17    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 5.43/1.17    inference(resolution,[],[f111,f70])).
% 5.43/1.17  fof(f111,plain,(
% 5.43/1.17    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X4) = k7_subset_1(u1_struct_0(sK0),X4,k2_tops_1(sK0,X4))) )),
% 5.43/1.17    inference(resolution,[],[f69,f75])).
% 5.43/1.17  fof(f75,plain,(
% 5.43/1.17    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 5.43/1.17    inference(cnf_transformation,[],[f39])).
% 5.43/1.17  fof(f39,plain,(
% 5.43/1.17    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.43/1.17    inference(ennf_transformation,[],[f32])).
% 5.43/1.17  fof(f32,axiom,(
% 5.43/1.17    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 5.43/1.17  fof(f69,plain,(
% 5.43/1.17    l1_pre_topc(sK0)),
% 5.43/1.17    inference(cnf_transformation,[],[f63])).
% 5.43/1.17  fof(f85,plain,(
% 5.43/1.17    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 5.43/1.17    inference(cnf_transformation,[],[f9])).
% 5.43/1.17  fof(f9,axiom,(
% 5.43/1.17    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 5.43/1.17  fof(f656,plain,(
% 5.43/1.17    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | k1_xboole_0 != k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 5.43/1.17    inference(superposition,[],[f91,f429])).
% 5.43/1.17  fof(f429,plain,(
% 5.43/1.17    k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 5.43/1.17    inference(superposition,[],[f84,f424])).
% 5.43/1.17  fof(f84,plain,(
% 5.43/1.17    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.43/1.17    inference(cnf_transformation,[],[f12])).
% 5.43/1.17  fof(f12,axiom,(
% 5.43/1.17    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.43/1.17  fof(f91,plain,(
% 5.43/1.17    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 5.43/1.17    inference(cnf_transformation,[],[f64])).
% 5.43/1.17  fof(f64,plain,(
% 5.43/1.17    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 5.43/1.17    inference(nnf_transformation,[],[f4])).
% 5.43/1.17  fof(f4,axiom,(
% 5.43/1.17    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 5.43/1.17  fof(f6452,plain,(
% 5.43/1.17    k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1)),
% 5.43/1.17    inference(forward_demodulation,[],[f6451,f405])).
% 5.43/1.17  fof(f405,plain,(
% 5.43/1.17    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 5.43/1.17    inference(forward_demodulation,[],[f404,f354])).
% 5.43/1.17  fof(f354,plain,(
% 5.43/1.17    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1))),
% 5.43/1.17    inference(resolution,[],[f350,f98])).
% 5.43/1.17  fof(f98,plain,(
% 5.43/1.17    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 5.43/1.17    inference(cnf_transformation,[],[f58])).
% 5.43/1.17  fof(f58,plain,(
% 5.43/1.17    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 5.43/1.17    inference(ennf_transformation,[],[f8])).
% 5.43/1.17  fof(f8,axiom,(
% 5.43/1.17    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 5.43/1.17  fof(f350,plain,(
% 5.43/1.17    r1_tarski(k1_xboole_0,k2_tops_1(sK0,sK1))),
% 5.43/1.17    inference(superposition,[],[f85,f346])).
% 5.43/1.17  fof(f346,plain,(
% 5.43/1.17    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 5.43/1.17    inference(resolution,[],[f332,f92])).
% 5.43/1.17  fof(f92,plain,(
% 5.43/1.17    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 5.43/1.17    inference(cnf_transformation,[],[f64])).
% 5.43/1.17  fof(f332,plain,(
% 5.43/1.17    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 5.43/1.17    inference(resolution,[],[f325,f93])).
% 5.43/1.17  fof(f93,plain,(
% 5.43/1.17    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 5.43/1.17    inference(cnf_transformation,[],[f65])).
% 5.43/1.17  fof(f65,plain,(
% 5.43/1.17    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 5.43/1.17    inference(nnf_transformation,[],[f24])).
% 5.43/1.17  fof(f24,axiom,(
% 5.43/1.17    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 5.43/1.17  fof(f325,plain,(
% 5.43/1.17    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.43/1.17    inference(subsumption_resolution,[],[f324,f69])).
% 5.43/1.17  fof(f324,plain,(
% 5.43/1.17    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 5.43/1.17    inference(subsumption_resolution,[],[f323,f145])).
% 5.43/1.17  fof(f145,plain,(
% 5.43/1.17    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.43/1.17    inference(subsumption_resolution,[],[f144,f70])).
% 5.43/1.17  fof(f144,plain,(
% 5.43/1.17    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.43/1.17    inference(superposition,[],[f89,f117])).
% 5.43/1.17  fof(f117,plain,(
% 5.43/1.17    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 5.43/1.17    inference(resolution,[],[f70,f82])).
% 5.43/1.17  fof(f82,plain,(
% 5.43/1.17    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 5.43/1.17    inference(cnf_transformation,[],[f49])).
% 5.43/1.17  fof(f49,plain,(
% 5.43/1.17    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.43/1.17    inference(ennf_transformation,[],[f14])).
% 5.43/1.17  fof(f14,axiom,(
% 5.43/1.17    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 5.43/1.17  fof(f89,plain,(
% 5.43/1.17    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.43/1.17    inference(cnf_transformation,[],[f55])).
% 5.43/1.17  fof(f55,plain,(
% 5.43/1.17    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.43/1.17    inference(ennf_transformation,[],[f15])).
% 5.43/1.17  fof(f15,axiom,(
% 5.43/1.17    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 5.43/1.17  fof(f323,plain,(
% 5.43/1.17    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 5.43/1.17    inference(superposition,[],[f77,f233])).
% 5.43/1.17  fof(f233,plain,(
% 5.43/1.17    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 5.43/1.17    inference(forward_demodulation,[],[f226,f119])).
% 5.43/1.17  fof(f119,plain,(
% 5.43/1.17    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 5.43/1.17    inference(backward_demodulation,[],[f114,f117])).
% 5.43/1.17  fof(f114,plain,(
% 5.43/1.17    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 5.43/1.17    inference(resolution,[],[f70,f88])).
% 5.43/1.17  fof(f88,plain,(
% 5.43/1.17    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 5.43/1.17    inference(cnf_transformation,[],[f54])).
% 5.43/1.17  fof(f54,plain,(
% 5.43/1.17    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.43/1.17    inference(ennf_transformation,[],[f18])).
% 5.43/1.17  fof(f18,axiom,(
% 5.43/1.17    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 5.43/1.17  fof(f226,plain,(
% 5.43/1.17    k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)))),
% 5.43/1.17    inference(resolution,[],[f109,f145])).
% 5.43/1.17  fof(f109,plain,(
% 5.43/1.17    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X2) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X2))) )),
% 5.43/1.17    inference(resolution,[],[f69,f78])).
% 5.43/1.17  fof(f78,plain,(
% 5.43/1.17    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) )),
% 5.43/1.17    inference(cnf_transformation,[],[f43])).
% 5.43/1.17  fof(f43,plain,(
% 5.43/1.17    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.43/1.17    inference(ennf_transformation,[],[f30])).
% 5.43/1.17  fof(f30,axiom,(
% 5.43/1.17    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).
% 5.43/1.17  fof(f77,plain,(
% 5.43/1.17    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.43/1.17    inference(cnf_transformation,[],[f42])).
% 5.43/1.17  fof(f42,plain,(
% 5.43/1.17    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 5.43/1.17    inference(flattening,[],[f41])).
% 5.43/1.17  fof(f41,plain,(
% 5.43/1.17    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 5.43/1.17    inference(ennf_transformation,[],[f26])).
% 5.43/1.17  fof(f26,axiom,(
% 5.43/1.17    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 5.43/1.17  fof(f404,plain,(
% 5.43/1.17    k3_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 5.43/1.17    inference(forward_demodulation,[],[f403,f101])).
% 5.43/1.17  fof(f101,plain,(
% 5.43/1.17    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.43/1.17    inference(cnf_transformation,[],[f2])).
% 5.43/1.17  fof(f2,axiom,(
% 5.43/1.17    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.43/1.17  fof(f403,plain,(
% 5.43/1.17    k3_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0) = k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 5.43/1.17    inference(superposition,[],[f84,f353])).
% 5.43/1.17  fof(f353,plain,(
% 5.43/1.17    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0)),
% 5.43/1.17    inference(forward_demodulation,[],[f351,f343])).
% 5.43/1.17  fof(f343,plain,(
% 5.43/1.17    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 5.43/1.17    inference(resolution,[],[f332,f98])).
% 5.43/1.17  fof(f351,plain,(
% 5.43/1.17    k3_xboole_0(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = k4_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0)),
% 5.43/1.17    inference(superposition,[],[f84,f346])).
% 5.43/1.17  fof(f6451,plain,(
% 5.43/1.17    k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1)),
% 5.43/1.17    inference(forward_demodulation,[],[f6450,f101])).
% 5.43/1.17  fof(f6450,plain,(
% 5.43/1.17    k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | sK1 = k1_tops_1(sK0,sK1)),
% 5.43/1.17    inference(superposition,[],[f84,f822])).
% 5.43/1.17  fof(f822,plain,(
% 5.43/1.17    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | sK1 = k1_tops_1(sK0,sK1)),
% 5.43/1.17    inference(subsumption_resolution,[],[f821,f70])).
% 5.43/1.17  fof(f821,plain,(
% 5.43/1.17    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | sK1 = k1_tops_1(sK0,sK1)),
% 5.43/1.17    inference(subsumption_resolution,[],[f815,f105])).
% 5.43/1.17  fof(f105,plain,(
% 5.43/1.17    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 5.43/1.17    inference(equality_resolution,[],[f95])).
% 5.43/1.17  fof(f95,plain,(
% 5.43/1.17    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 5.43/1.17    inference(cnf_transformation,[],[f67])).
% 5.43/1.17  fof(f815,plain,(
% 5.43/1.17    ~r1_tarski(sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | sK1 = k1_tops_1(sK0,sK1)),
% 5.43/1.17    inference(resolution,[],[f487,f431])).
% 5.43/1.17  fof(f487,plain,(
% 5.43/1.17    ( ! [X0] : (r1_tarski(sK1,k1_tops_1(sK0,X0)) | ~r1_tarski(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) )),
% 5.43/1.17    inference(backward_demodulation,[],[f376,f483])).
% 5.43/1.17  fof(f376,plain,(
% 5.43/1.17    ( ! [X0] : (k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~r1_tarski(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,X0))) )),
% 5.43/1.17    inference(backward_demodulation,[],[f322,f372])).
% 5.43/1.17  fof(f372,plain,(
% 5.43/1.17    ( ! [X2] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X2) = k4_xboole_0(k2_pre_topc(sK0,sK1),X2)) )),
% 5.43/1.17    inference(resolution,[],[f360,f73])).
% 5.43/1.17  fof(f360,plain,(
% 5.43/1.17    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.43/1.17    inference(subsumption_resolution,[],[f359,f70])).
% 5.43/1.17  fof(f359,plain,(
% 5.43/1.17    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.43/1.17    inference(subsumption_resolution,[],[f358,f325])).
% 5.43/1.17  fof(f358,plain,(
% 5.43/1.17    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.43/1.17    inference(superposition,[],[f87,f263])).
% 5.43/1.17  fof(f263,plain,(
% 5.43/1.17    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 5.43/1.17    inference(resolution,[],[f110,f70])).
% 5.43/1.17  fof(f110,plain,(
% 5.43/1.17    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X3) = k4_subset_1(u1_struct_0(sK0),X3,k2_tops_1(sK0,X3))) )),
% 5.43/1.17    inference(resolution,[],[f69,f76])).
% 5.43/1.17  fof(f76,plain,(
% 5.43/1.17    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 5.43/1.17    inference(cnf_transformation,[],[f40])).
% 5.43/1.17  fof(f40,plain,(
% 5.43/1.17    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.43/1.17    inference(ennf_transformation,[],[f31])).
% 5.43/1.17  fof(f31,axiom,(
% 5.43/1.17    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 5.43/1.17  fof(f87,plain,(
% 5.43/1.17    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.43/1.17    inference(cnf_transformation,[],[f53])).
% 5.43/1.17  fof(f53,plain,(
% 5.43/1.17    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.43/1.17    inference(flattening,[],[f52])).
% 5.43/1.17  fof(f52,plain,(
% 5.43/1.17    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 5.43/1.17    inference(ennf_transformation,[],[f16])).
% 5.43/1.17  fof(f16,axiom,(
% 5.43/1.17    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 5.43/1.17  fof(f322,plain,(
% 5.43/1.17    ( ! [X0] : (~r1_tarski(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,X0)) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)) )),
% 5.43/1.17    inference(subsumption_resolution,[],[f320,f70])).
% 5.43/1.17  fof(f320,plain,(
% 5.43/1.17    ( ! [X0] : (~r1_tarski(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,X0)) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)) )),
% 5.43/1.17    inference(resolution,[],[f108,f71])).
% 5.43/1.17  fof(f71,plain,(
% 5.43/1.17    v3_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 5.43/1.17    inference(cnf_transformation,[],[f63])).
% 5.43/1.17  fof(f108,plain,(
% 5.43/1.17    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k1_tops_1(sK0,X1))) )),
% 5.43/1.17    inference(resolution,[],[f69,f80])).
% 5.43/1.17  fof(f80,plain,(
% 5.43/1.17    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 5.43/1.17    inference(cnf_transformation,[],[f47])).
% 5.43/1.17  fof(f47,plain,(
% 5.43/1.17    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.43/1.17    inference(flattening,[],[f46])).
% 5.43/1.17  fof(f46,plain,(
% 5.43/1.17    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.43/1.17    inference(ennf_transformation,[],[f29])).
% 5.43/1.17  fof(f29,axiom,(
% 5.43/1.17    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 5.43/1.17  fof(f1764,plain,(
% 5.43/1.17    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 5.43/1.17    inference(superposition,[],[f372,f305])).
% 5.43/1.17  fof(f305,plain,(
% 5.43/1.17    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 5.43/1.17    inference(resolution,[],[f112,f70])).
% 5.43/1.17  fof(f112,plain,(
% 5.43/1.17    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X5) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X5),k1_tops_1(sK0,X5))) )),
% 5.43/1.17    inference(resolution,[],[f69,f74])).
% 5.43/1.17  fof(f74,plain,(
% 5.43/1.17    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 5.43/1.17    inference(cnf_transformation,[],[f38])).
% 5.43/1.17  fof(f38,plain,(
% 5.43/1.17    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.43/1.17    inference(ennf_transformation,[],[f28])).
% 5.43/1.17  fof(f28,axiom,(
% 5.43/1.17    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 5.43/1.17  fof(f483,plain,(
% 5.43/1.17    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 5.43/1.17    inference(superposition,[],[f83,f472])).
% 5.43/1.17  fof(f472,plain,(
% 5.43/1.17    k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 5.43/1.17    inference(forward_demodulation,[],[f464,f340])).
% 5.43/1.17  fof(f340,plain,(
% 5.43/1.17    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)),
% 5.43/1.17    inference(backward_demodulation,[],[f338,f339])).
% 5.43/1.17  fof(f339,plain,(
% 5.43/1.17    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 5.43/1.17    inference(forward_demodulation,[],[f331,f263])).
% 5.43/1.17  fof(f331,plain,(
% 5.43/1.17    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 5.43/1.17    inference(resolution,[],[f325,f115])).
% 5.43/1.17  fof(f115,plain,(
% 5.43/1.17    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(sK1,X0) = k4_subset_1(u1_struct_0(sK0),sK1,X0)) )),
% 5.43/1.17    inference(resolution,[],[f70,f86])).
% 5.43/1.17  fof(f86,plain,(
% 5.43/1.17    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 5.43/1.17    inference(cnf_transformation,[],[f51])).
% 5.43/1.17  fof(f51,plain,(
% 5.43/1.17    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.43/1.17    inference(flattening,[],[f50])).
% 5.43/1.17  fof(f50,plain,(
% 5.43/1.17    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 5.43/1.17    inference(ennf_transformation,[],[f19])).
% 5.43/1.17  fof(f19,axiom,(
% 5.43/1.17    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 5.43/1.17  fof(f338,plain,(
% 5.43/1.17    k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 5.43/1.17    inference(forward_demodulation,[],[f330,f99])).
% 5.43/1.17  fof(f99,plain,(
% 5.43/1.17    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 5.43/1.17    inference(cnf_transformation,[],[f1])).
% 5.43/1.17  fof(f1,axiom,(
% 5.43/1.17    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 5.43/1.17  fof(f330,plain,(
% 5.43/1.17    k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)),
% 5.43/1.17    inference(resolution,[],[f325,f116])).
% 5.43/1.17  fof(f116,plain,(
% 5.43/1.17    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(X1,sK1) = k4_subset_1(u1_struct_0(sK0),X1,sK1)) )),
% 5.43/1.17    inference(resolution,[],[f70,f86])).
% 5.43/1.17  fof(f464,plain,(
% 5.43/1.17    k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)),
% 5.43/1.17    inference(resolution,[],[f201,f332])).
% 5.43/1.17  fof(f201,plain,(
% 5.43/1.17    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | k2_xboole_0(X0,sK1) = k4_subset_1(u1_struct_0(sK0),X0,sK1)) )),
% 5.43/1.17    inference(resolution,[],[f116,f94])).
% 5.43/1.17  fof(f94,plain,(
% 5.43/1.17    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 5.43/1.17    inference(cnf_transformation,[],[f65])).
% 5.43/1.17  fof(f83,plain,(
% 5.43/1.17    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 5.43/1.17    inference(cnf_transformation,[],[f10])).
% 5.43/1.17  fof(f10,axiom,(
% 5.43/1.17    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 5.43/1.17  fof(f485,plain,(
% 5.43/1.17    ~v3_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) != k4_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 5.43/1.17    inference(backward_demodulation,[],[f378,f483])).
% 5.43/1.17  fof(f378,plain,(
% 5.43/1.17    ~v3_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 5.43/1.17    inference(backward_demodulation,[],[f72,f372])).
% 5.43/1.17  fof(f72,plain,(
% 5.43/1.17    ~v3_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 5.43/1.17    inference(cnf_transformation,[],[f63])).
% 5.43/1.17  fof(f6698,plain,(
% 5.43/1.17    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.43/1.17    inference(superposition,[],[f107,f6453])).
% 5.43/1.17  fof(f107,plain,(
% 5.43/1.17    ( ! [X0] : (v3_pre_topc(k1_tops_1(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 5.43/1.17    inference(subsumption_resolution,[],[f106,f69])).
% 5.43/1.17  fof(f106,plain,(
% 5.43/1.17    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,X0),sK0)) )),
% 5.43/1.17    inference(resolution,[],[f68,f79])).
% 5.43/1.17  fof(f79,plain,(
% 5.43/1.17    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 5.43/1.17    inference(cnf_transformation,[],[f45])).
% 5.43/1.17  fof(f45,plain,(
% 5.43/1.17    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 5.43/1.17    inference(flattening,[],[f44])).
% 5.43/1.17  fof(f44,plain,(
% 5.43/1.17    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 5.43/1.17    inference(ennf_transformation,[],[f27])).
% 5.43/1.17  fof(f27,axiom,(
% 5.43/1.17    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 5.43/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 5.43/1.17  fof(f68,plain,(
% 5.43/1.17    v2_pre_topc(sK0)),
% 5.43/1.17    inference(cnf_transformation,[],[f63])).
% 5.43/1.17  % SZS output end Proof for theBenchmark
% 5.43/1.17  % (26719)------------------------------
% 5.43/1.17  % (26719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.43/1.17  % (26719)Termination reason: Refutation
% 5.43/1.17  
% 5.43/1.17  % (26719)Memory used [KB]: 5884
% 5.43/1.17  % (26719)Time elapsed: 0.774 s
% 5.43/1.17  % (26719)------------------------------
% 5.43/1.17  % (26719)------------------------------
% 5.43/1.17  % (26694)Success in time 0.808 s
%------------------------------------------------------------------------------
