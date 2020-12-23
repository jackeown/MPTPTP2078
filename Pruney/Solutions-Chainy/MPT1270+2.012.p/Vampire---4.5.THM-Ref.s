%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:37 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 515 expanded)
%              Number of leaves         :   18 ( 137 expanded)
%              Depth                    :   18
%              Number of atoms          :  287 (1964 expanded)
%              Number of equality atoms :   57 ( 207 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f863,plain,(
    $false ),
    inference(subsumption_resolution,[],[f862,f717])).

fof(f717,plain,(
    v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f716,f45])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
            | ~ v2_tops_1(X1,sK0) )
          & ( r1_tarski(X1,k2_tops_1(sK0,X1))
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
          | ~ v2_tops_1(X1,sK0) )
        & ( r1_tarski(X1,k2_tops_1(sK0,X1))
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | ~ v2_tops_1(sK1,sK0) )
      & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(f716,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f715,f46])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f715,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f711,f72])).

fof(f72,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f64,f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f711,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f112,f689])).

fof(f689,plain,(
    k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f688,f187])).

fof(f187,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f109,f46])).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tops_1(X0,sK0)
      | k1_xboole_0 = k1_tops_1(sK0,X0) ) ),
    inference(resolution,[],[f54,f45])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = k1_tops_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f688,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f687,f286])).

fof(f286,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f256,f134])).

fof(f134,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(resolution,[],[f91,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f91,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2) ) ),
    inference(resolution,[],[f56,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f256,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(superposition,[],[f95,f224])).

fof(f224,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(superposition,[],[f125,f210])).

fof(f210,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f126,f125])).

fof(f126,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X3)) ),
    inference(resolution,[],[f76,f72])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0 ) ),
    inference(resolution,[],[f66,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f125,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(resolution,[],[f76,f70])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f92,f89])).

fof(f89,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f56,f49])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f57,f49])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f687,plain,
    ( v2_tops_1(sK1,sK0)
    | k1_tops_1(sK0,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f660,f62])).

fof(f660,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(superposition,[],[f345,f434])).

fof(f434,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f237,f46])).

fof(f237,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k4_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f103,f45])).

fof(f103,plain,(
    ! [X4,X3] :
      ( ~ l1_pre_topc(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
      | k1_tops_1(X4,X3) = k4_xboole_0(k1_tops_1(X4,X3),k2_tops_1(X4,X3)) ) ),
    inference(resolution,[],[f52,f62])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).

fof(f345,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(X0,k2_tops_1(sK0,sK1)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(resolution,[],[f163,f122])).

fof(f122,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f98,f46])).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f51,f45])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f163,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,sK1)
      | r1_xboole_0(X12,k4_xboole_0(X13,k2_tops_1(sK0,sK1)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(resolution,[],[f85,f47])).

fof(f47,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,X2)
      | ~ r1_tarski(X0,X3)
      | r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f69,f66])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tops_1(X0,X1),k1_xboole_0)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f110,f72])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tops_1(X0,X1),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_tops_1(X0,X1))
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(extensionality_resolution,[],[f61,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f862,plain,(
    ~ v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f848,f117])).

fof(f117,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f97,f46])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f50,f45])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f848,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(superposition,[],[f48,f839])).

fof(f839,plain,(
    k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f825,f224])).

fof(f825,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f682,f689])).

fof(f682,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f467,f234])).

fof(f234,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f113,f46])).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f53,f45])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f467,plain,(
    ! [X5] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X5) = k4_xboole_0(k2_pre_topc(sK0,sK1),X5) ),
    inference(resolution,[],[f240,f46])).

fof(f240,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1) = k4_xboole_0(k2_pre_topc(sK0,X0),X1) ) ),
    inference(resolution,[],[f104,f45])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),X2) = k4_xboole_0(k2_pre_topc(X1,X0),X2) ) ),
    inference(resolution,[],[f58,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f48,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 17:07:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.52  % (23066)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (23059)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (23070)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (23069)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (23057)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (23081)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % (23079)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (23071)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (23078)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (23063)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (23062)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (23064)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (23072)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.28/0.53  % (23067)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.28/0.53  % (23075)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.28/0.54  % (23061)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.28/0.54  % (23060)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.28/0.54  % (23065)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.28/0.54  % (23058)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.54  % (23077)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.28/0.55  % (23082)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.28/0.55  % (23080)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.28/0.55  % (23073)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.28/0.56  % (23074)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.51/0.56  % (23068)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.51/0.56  % (23076)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.51/0.59  % (23073)Refutation found. Thanks to Tanya!
% 1.51/0.59  % SZS status Theorem for theBenchmark
% 1.51/0.59  % SZS output start Proof for theBenchmark
% 1.51/0.59  fof(f863,plain,(
% 1.51/0.59    $false),
% 1.51/0.59    inference(subsumption_resolution,[],[f862,f717])).
% 1.51/0.59  fof(f717,plain,(
% 1.51/0.59    v2_tops_1(sK1,sK0)),
% 1.51/0.59    inference(subsumption_resolution,[],[f716,f45])).
% 1.51/0.59  fof(f45,plain,(
% 1.51/0.59    l1_pre_topc(sK0)),
% 1.51/0.59    inference(cnf_transformation,[],[f39])).
% 1.51/0.59  fof(f39,plain,(
% 1.51/0.59    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.51/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 1.51/0.59  fof(f37,plain,(
% 1.51/0.59    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.51/0.59    introduced(choice_axiom,[])).
% 1.51/0.59  fof(f38,plain,(
% 1.51/0.59    ? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.51/0.59    introduced(choice_axiom,[])).
% 1.51/0.59  fof(f36,plain,(
% 1.51/0.59    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.51/0.59    inference(flattening,[],[f35])).
% 1.51/0.59  fof(f35,plain,(
% 1.51/0.59    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.51/0.59    inference(nnf_transformation,[],[f19])).
% 1.51/0.59  fof(f19,plain,(
% 1.51/0.59    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.51/0.59    inference(ennf_transformation,[],[f18])).
% 1.51/0.59  fof(f18,negated_conjecture,(
% 1.51/0.59    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 1.51/0.59    inference(negated_conjecture,[],[f17])).
% 1.51/0.59  fof(f17,conjecture,(
% 1.51/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).
% 1.51/0.59  fof(f716,plain,(
% 1.51/0.59    v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.51/0.59    inference(subsumption_resolution,[],[f715,f46])).
% 1.51/0.59  fof(f46,plain,(
% 1.51/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.51/0.59    inference(cnf_transformation,[],[f39])).
% 1.51/0.59  fof(f715,plain,(
% 1.51/0.59    v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.51/0.59    inference(subsumption_resolution,[],[f711,f72])).
% 1.51/0.59  fof(f72,plain,(
% 1.51/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.51/0.59    inference(resolution,[],[f64,f49])).
% 1.51/0.59  fof(f49,plain,(
% 1.51/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.51/0.59    inference(cnf_transformation,[],[f8])).
% 1.51/0.59  fof(f8,axiom,(
% 1.51/0.59    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.51/0.59  fof(f64,plain,(
% 1.51/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f44])).
% 1.51/0.59  fof(f44,plain,(
% 1.51/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.51/0.59    inference(nnf_transformation,[],[f9])).
% 1.51/0.59  fof(f9,axiom,(
% 1.51/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.51/0.59  fof(f711,plain,(
% 1.51/0.59    ~r1_tarski(k1_xboole_0,k1_xboole_0) | v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.51/0.59    inference(superposition,[],[f112,f689])).
% 1.51/0.59  fof(f689,plain,(
% 1.51/0.59    k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.51/0.59    inference(subsumption_resolution,[],[f688,f187])).
% 1.51/0.59  fof(f187,plain,(
% 1.51/0.59    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.51/0.59    inference(resolution,[],[f109,f46])).
% 1.51/0.59  fof(f109,plain,(
% 1.51/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(X0,sK0) | k1_xboole_0 = k1_tops_1(sK0,X0)) )),
% 1.51/0.59    inference(resolution,[],[f54,f45])).
% 1.51/0.59  fof(f54,plain,(
% 1.51/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = k1_tops_1(X0,X1)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f40])).
% 1.51/0.59  fof(f40,plain,(
% 1.51/0.59    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.51/0.59    inference(nnf_transformation,[],[f24])).
% 1.51/0.59  fof(f24,plain,(
% 1.51/0.59    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.51/0.59    inference(ennf_transformation,[],[f16])).
% 1.51/0.59  fof(f16,axiom,(
% 1.51/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 1.51/0.59  fof(f688,plain,(
% 1.51/0.59    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 1.51/0.59    inference(forward_demodulation,[],[f687,f286])).
% 1.51/0.59  fof(f286,plain,(
% 1.51/0.59    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.51/0.59    inference(superposition,[],[f256,f134])).
% 1.51/0.59  fof(f134,plain,(
% 1.51/0.59    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 1.51/0.59    inference(resolution,[],[f91,f70])).
% 1.51/0.59  fof(f70,plain,(
% 1.51/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.51/0.59    inference(equality_resolution,[],[f60])).
% 1.51/0.59  fof(f60,plain,(
% 1.51/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.51/0.59    inference(cnf_transformation,[],[f42])).
% 1.51/0.59  fof(f42,plain,(
% 1.51/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.59    inference(flattening,[],[f41])).
% 1.51/0.59  fof(f41,plain,(
% 1.51/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.59    inference(nnf_transformation,[],[f1])).
% 1.51/0.59  fof(f1,axiom,(
% 1.51/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.51/0.59  fof(f91,plain,(
% 1.51/0.59    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2)) )),
% 1.51/0.59    inference(resolution,[],[f56,f65])).
% 1.51/0.59  fof(f65,plain,(
% 1.51/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f44])).
% 1.51/0.59  fof(f56,plain,(
% 1.51/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f25])).
% 1.51/0.59  fof(f25,plain,(
% 1.51/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.51/0.59    inference(ennf_transformation,[],[f5])).
% 1.51/0.59  fof(f5,axiom,(
% 1.51/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.51/0.59  fof(f256,plain,(
% 1.51/0.59    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.51/0.59    inference(superposition,[],[f95,f224])).
% 1.51/0.59  fof(f224,plain,(
% 1.51/0.59    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 1.51/0.59    inference(superposition,[],[f125,f210])).
% 1.51/0.59  fof(f210,plain,(
% 1.51/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.51/0.59    inference(superposition,[],[f126,f125])).
% 1.51/0.59  fof(f126,plain,(
% 1.51/0.59    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X3))) )),
% 1.51/0.59    inference(resolution,[],[f76,f72])).
% 1.51/0.59  fof(f76,plain,(
% 1.51/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0) )),
% 1.51/0.59    inference(resolution,[],[f66,f62])).
% 1.51/0.59  fof(f62,plain,(
% 1.51/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.51/0.59    inference(cnf_transformation,[],[f43])).
% 1.51/0.59  fof(f43,plain,(
% 1.51/0.59    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.51/0.59    inference(nnf_transformation,[],[f3])).
% 1.51/0.59  fof(f3,axiom,(
% 1.51/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.51/0.59  fof(f66,plain,(
% 1.51/0.59    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f29])).
% 1.51/0.59  fof(f29,plain,(
% 1.51/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.51/0.59    inference(ennf_transformation,[],[f4])).
% 1.51/0.59  fof(f4,axiom,(
% 1.51/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.51/0.59  fof(f125,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 1.51/0.59    inference(resolution,[],[f76,f70])).
% 1.51/0.59  fof(f95,plain,(
% 1.51/0.59    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.51/0.59    inference(forward_demodulation,[],[f92,f89])).
% 1.51/0.59  fof(f89,plain,(
% 1.51/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.51/0.59    inference(resolution,[],[f56,f49])).
% 1.51/0.59  fof(f92,plain,(
% 1.51/0.59    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 1.51/0.59    inference(resolution,[],[f57,f49])).
% 1.51/0.59  fof(f57,plain,(
% 1.51/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.51/0.59    inference(cnf_transformation,[],[f26])).
% 1.51/0.59  fof(f26,plain,(
% 1.51/0.59    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.51/0.59    inference(ennf_transformation,[],[f6])).
% 1.51/0.59  fof(f6,axiom,(
% 1.51/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.51/0.59  fof(f687,plain,(
% 1.51/0.59    v2_tops_1(sK1,sK0) | k1_tops_1(sK0,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),
% 1.51/0.59    inference(resolution,[],[f660,f62])).
% 1.51/0.59  fof(f660,plain,(
% 1.51/0.59    r1_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 1.51/0.59    inference(superposition,[],[f345,f434])).
% 1.51/0.59  fof(f434,plain,(
% 1.51/0.59    k1_tops_1(sK0,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 1.51/0.59    inference(resolution,[],[f237,f46])).
% 1.51/0.59  fof(f237,plain,(
% 1.51/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k4_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0))) )),
% 1.51/0.59    inference(resolution,[],[f103,f45])).
% 1.51/0.59  fof(f103,plain,(
% 1.51/0.59    ( ! [X4,X3] : (~l1_pre_topc(X4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4))) | k1_tops_1(X4,X3) = k4_xboole_0(k1_tops_1(X4,X3),k2_tops_1(X4,X3))) )),
% 1.51/0.59    inference(resolution,[],[f52,f62])).
% 1.51/0.59  fof(f52,plain,(
% 1.51/0.59    ( ! [X0,X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f22])).
% 1.51/0.59  fof(f22,plain,(
% 1.51/0.59    ! [X0] : (! [X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.51/0.59    inference(ennf_transformation,[],[f15])).
% 1.51/0.59  fof(f15,axiom,(
% 1.51/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).
% 1.51/0.59  fof(f345,plain,(
% 1.51/0.59    ( ! [X0] : (r1_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(X0,k2_tops_1(sK0,sK1))) | v2_tops_1(sK1,sK0)) )),
% 1.51/0.59    inference(resolution,[],[f163,f122])).
% 1.51/0.59  fof(f122,plain,(
% 1.51/0.59    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.51/0.59    inference(resolution,[],[f98,f46])).
% 1.51/0.59  fof(f98,plain,(
% 1.51/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 1.51/0.59    inference(resolution,[],[f51,f45])).
% 1.51/0.59  fof(f51,plain,(
% 1.51/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f21])).
% 1.51/0.59  fof(f21,plain,(
% 1.51/0.59    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.51/0.59    inference(ennf_transformation,[],[f14])).
% 1.51/0.59  fof(f14,axiom,(
% 1.51/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.51/0.59  fof(f163,plain,(
% 1.51/0.59    ( ! [X12,X13] : (~r1_tarski(X12,sK1) | r1_xboole_0(X12,k4_xboole_0(X13,k2_tops_1(sK0,sK1))) | v2_tops_1(sK1,sK0)) )),
% 1.51/0.59    inference(resolution,[],[f85,f47])).
% 1.51/0.59  fof(f47,plain,(
% 1.51/0.59    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 1.51/0.59    inference(cnf_transformation,[],[f39])).
% 1.51/0.59  fof(f85,plain,(
% 1.51/0.59    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,X2) | ~r1_tarski(X0,X3) | r1_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 1.51/0.59    inference(resolution,[],[f69,f66])).
% 1.51/0.59  fof(f69,plain,(
% 1.51/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f34])).
% 1.51/0.59  fof(f34,plain,(
% 1.51/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.51/0.59    inference(flattening,[],[f33])).
% 1.51/0.59  fof(f33,plain,(
% 1.51/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.51/0.59    inference(ennf_transformation,[],[f2])).
% 1.51/0.59  fof(f2,axiom,(
% 1.51/0.59    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.51/0.59  fof(f112,plain,(
% 1.51/0.59    ( ! [X0,X1] : (~r1_tarski(k1_tops_1(X0,X1),k1_xboole_0) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.51/0.59    inference(subsumption_resolution,[],[f110,f72])).
% 1.51/0.59  fof(f110,plain,(
% 1.51/0.59    ( ! [X0,X1] : (~r1_tarski(k1_tops_1(X0,X1),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_tops_1(X0,X1)) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.51/0.59    inference(extensionality_resolution,[],[f61,f55])).
% 1.51/0.59  fof(f55,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f40])).
% 1.51/0.59  fof(f61,plain,(
% 1.51/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f42])).
% 1.51/0.59  fof(f862,plain,(
% 1.51/0.59    ~v2_tops_1(sK1,sK0)),
% 1.51/0.59    inference(subsumption_resolution,[],[f848,f117])).
% 1.51/0.59  fof(f117,plain,(
% 1.51/0.59    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 1.51/0.59    inference(resolution,[],[f97,f46])).
% 1.51/0.59  fof(f97,plain,(
% 1.51/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0))) )),
% 1.51/0.59    inference(resolution,[],[f50,f45])).
% 1.51/0.59  fof(f50,plain,(
% 1.51/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 1.51/0.59    inference(cnf_transformation,[],[f20])).
% 1.51/0.59  fof(f20,plain,(
% 1.51/0.59    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.51/0.59    inference(ennf_transformation,[],[f12])).
% 1.51/0.59  fof(f12,axiom,(
% 1.51/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 1.51/0.59  fof(f848,plain,(
% 1.51/0.59    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 1.51/0.59    inference(superposition,[],[f48,f839])).
% 1.51/0.59  fof(f839,plain,(
% 1.51/0.59    k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1)),
% 1.51/0.59    inference(forward_demodulation,[],[f825,f224])).
% 1.51/0.59  fof(f825,plain,(
% 1.51/0.59    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0)),
% 1.51/0.59    inference(superposition,[],[f682,f689])).
% 1.51/0.59  fof(f682,plain,(
% 1.51/0.59    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 1.51/0.59    inference(superposition,[],[f467,f234])).
% 1.51/0.59  fof(f234,plain,(
% 1.51/0.59    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 1.51/0.59    inference(resolution,[],[f113,f46])).
% 1.51/0.59  fof(f113,plain,(
% 1.51/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) )),
% 1.51/0.59    inference(resolution,[],[f53,f45])).
% 1.51/0.59  fof(f53,plain,(
% 1.51/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 1.51/0.59    inference(cnf_transformation,[],[f23])).
% 1.51/0.59  fof(f23,plain,(
% 1.51/0.59    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.51/0.59    inference(ennf_transformation,[],[f13])).
% 1.51/0.59  fof(f13,axiom,(
% 1.51/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 1.51/0.59  fof(f467,plain,(
% 1.51/0.59    ( ! [X5] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X5) = k4_xboole_0(k2_pre_topc(sK0,sK1),X5)) )),
% 1.51/0.59    inference(resolution,[],[f240,f46])).
% 1.51/0.59  fof(f240,plain,(
% 1.51/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1) = k4_xboole_0(k2_pre_topc(sK0,X0),X1)) )),
% 1.51/0.59    inference(resolution,[],[f104,f45])).
% 1.51/0.59  fof(f104,plain,(
% 1.51/0.59    ( ! [X2,X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),X2) = k4_xboole_0(k2_pre_topc(X1,X0),X2)) )),
% 1.51/0.59    inference(resolution,[],[f58,f67])).
% 1.51/0.59  fof(f67,plain,(
% 1.51/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f30])).
% 1.51/0.59  fof(f30,plain,(
% 1.51/0.59    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.51/0.59    inference(ennf_transformation,[],[f7])).
% 1.51/0.59  fof(f7,axiom,(
% 1.51/0.59    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.51/0.59  fof(f58,plain,(
% 1.51/0.59    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f28])).
% 1.51/0.59  fof(f28,plain,(
% 1.51/0.59    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.51/0.59    inference(flattening,[],[f27])).
% 1.51/0.59  fof(f27,plain,(
% 1.51/0.59    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.51/0.59    inference(ennf_transformation,[],[f11])).
% 1.51/0.59  fof(f11,axiom,(
% 1.51/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.51/0.59  fof(f48,plain,(
% 1.51/0.59    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 1.51/0.59    inference(cnf_transformation,[],[f39])).
% 1.51/0.59  % SZS output end Proof for theBenchmark
% 1.51/0.59  % (23073)------------------------------
% 1.51/0.59  % (23073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.59  % (23073)Termination reason: Refutation
% 1.51/0.59  
% 1.51/0.59  % (23073)Memory used [KB]: 1918
% 1.51/0.59  % (23073)Time elapsed: 0.158 s
% 1.51/0.59  % (23073)------------------------------
% 1.51/0.59  % (23073)------------------------------
% 1.51/0.59  % (23057)Refutation not found, incomplete strategy% (23057)------------------------------
% 1.51/0.59  % (23057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.59  % (23057)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.59  
% 1.51/0.59  % (23057)Memory used [KB]: 11129
% 1.51/0.59  % (23057)Time elapsed: 0.166 s
% 1.51/0.59  % (23057)------------------------------
% 1.51/0.59  % (23057)------------------------------
% 1.51/0.60  % (23056)Success in time 0.223 s
%------------------------------------------------------------------------------
