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
% DateTime   : Thu Dec  3 12:44:14 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 532 expanded)
%              Number of leaves         :   23 ( 160 expanded)
%              Depth                    :   21
%              Number of atoms          :  225 ( 893 expanded)
%              Number of equality atoms :   58 ( 340 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1702,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1701,f1492])).

fof(f1492,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f1491,f42])).

fof(f42,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f1491,plain,(
    r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f1488,f133])).

fof(f133,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f131,f89])).

fof(f89,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f131,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f127,f45])).

fof(f45,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f127,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f61,f44])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f1488,plain,
    ( ~ r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f1469,f403])).

fof(f403,plain,(
    r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f402,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f402,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f401,f371])).

fof(f371,plain,(
    ! [X3] :
      ( r1_xboole_0(k3_subset_1(sK0,sK2),X3)
      | ~ r1_tarski(X3,sK2) ) ),
    inference(superposition,[],[f194,f360])).

fof(f360,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f83,f43])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f84,f63])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f56])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f401,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK2),sK1)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f388,f41])).

fof(f41,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f388,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k3_subset_1(sK0,sK1))
      | r1_xboole_0(X1,sK1) ) ),
    inference(superposition,[],[f85,f361])).

fof(f361,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f83,f44])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f71,f56])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f1469,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k3_subset_1(sK0,sK2))
      | ~ r1_tarski(X0,sK0)
      | r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f88,f1458])).

fof(f1458,plain,(
    sK0 = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f807,f1457])).

fof(f1457,plain,(
    sK0 = k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) ),
    inference(backward_demodulation,[],[f372,f1456])).

fof(f1456,plain,(
    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK2)) ),
    inference(forward_demodulation,[],[f1443,f292])).

fof(f292,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f290,f77])).

fof(f77,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f47,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f290,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f81,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f81,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f55,f75,f56])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1443,plain,(
    k3_tarski(k1_enumset1(sK0,sK0,sK2)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f288,f323])).

fof(f323,plain,(
    k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f319,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f319,plain,(
    v1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f314,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f314,plain,(
    v1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))) ),
    inference(resolution,[],[f167,f78])).

fof(f78,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f49,f56])).

fof(f49,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f167,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,X2)),sK0)
      | v1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,X2))) ) ),
    inference(resolution,[],[f153,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f153,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X0)),sK0) ),
    inference(resolution,[],[f150,f79])).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f50,f56])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f150,plain,(
    ! [X9] :
      ( ~ r1_tarski(X9,sK2)
      | r1_tarski(X9,sK0) ) ),
    inference(resolution,[],[f73,f132])).

fof(f132,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f130,f89])).

fof(f130,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f126,f45])).

fof(f126,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f61,f43])).

fof(f73,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f288,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X1,X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
    inference(superposition,[],[f81,f51])).

fof(f372,plain,(
    k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) = k3_tarski(k1_enumset1(sK0,sK0,sK2)) ),
    inference(forward_demodulation,[],[f366,f80])).

fof(f80,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f52,f53,f53])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f366,plain,(
    k3_tarski(k1_enumset1(sK2,sK2,sK0)) = k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) ),
    inference(superposition,[],[f81,f360])).

fof(f807,plain,(
    k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f806,f372])).

fof(f806,plain,(
    k3_tarski(k1_enumset1(sK0,sK0,sK2)) = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f801,f80])).

fof(f801,plain,(
    k3_tarski(k1_enumset1(sK2,sK2,sK0)) = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2))) ),
    inference(superposition,[],[f82,f360])).

fof(f82,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f57,f75,f56,f75])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f1701,plain,(
    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1697,f365])).

fof(f365,plain,(
    r1_tarski(k3_subset_1(sK0,sK2),sK0) ),
    inference(superposition,[],[f79,f360])).

fof(f1697,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK0)
    | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f1671,f402])).

fof(f1671,plain,(
    ! [X11] :
      ( ~ r1_xboole_0(X11,sK1)
      | ~ r1_tarski(X11,sK0)
      | r1_tarski(X11,k3_subset_1(sK0,sK1)) ) ),
    inference(superposition,[],[f533,f1454])).

fof(f1454,plain,(
    sK0 = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f809,f1453])).

fof(f1453,plain,(
    sK0 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f392,f1452])).

fof(f1452,plain,(
    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f1442,f292])).

fof(f1442,plain,(
    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f288,f254])).

fof(f254,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f250,f48])).

fof(f250,plain,(
    v1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f245,f51])).

fof(f245,plain,(
    v1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) ),
    inference(resolution,[],[f159,f78])).

fof(f159,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X2)),sK0)
      | v1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X2))) ) ),
    inference(resolution,[],[f151,f62])).

fof(f151,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK0) ),
    inference(resolution,[],[f149,f79])).

fof(f149,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,sK1)
      | r1_tarski(X8,sK0) ) ),
    inference(resolution,[],[f73,f133])).

fof(f392,plain,(
    k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f386,f80])).

fof(f386,plain,(
    k3_tarski(k1_enumset1(sK1,sK1,sK0)) = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f81,f361])).

fof(f809,plain,(
    k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f808,f392])).

fof(f808,plain,(
    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f802,f80])).

fof(f802,plain,(
    k3_tarski(k1_enumset1(sK1,sK1,sK0)) = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) ),
    inference(superposition,[],[f82,f361])).

fof(f533,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0)))
      | ~ r1_xboole_0(X2,X1)
      | r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f88,f80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:22:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (11243)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (11237)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (11240)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (11238)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (11239)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (11244)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (11253)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (11250)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (11252)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (11260)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (11257)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (11259)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (11249)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (11245)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (11251)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (11241)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (11247)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.53  % (11242)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.45/0.53  % (11265)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.45/0.54  % (11263)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.54  % (11262)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.54  % (11264)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.54  % (11261)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.54  % (11255)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.54  % (11266)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.45/0.54  % (11256)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.55  % (11246)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.45/0.55  % (11258)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.55  % (11248)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.55  % (11254)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.55/0.62  % (11243)Refutation found. Thanks to Tanya!
% 1.55/0.62  % SZS status Theorem for theBenchmark
% 1.55/0.62  % SZS output start Proof for theBenchmark
% 1.55/0.62  fof(f1702,plain,(
% 1.55/0.62    $false),
% 1.55/0.62    inference(subsumption_resolution,[],[f1701,f1492])).
% 1.55/0.62  fof(f1492,plain,(
% 1.55/0.62    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 1.55/0.62    inference(resolution,[],[f1491,f42])).
% 1.55/0.62  fof(f42,plain,(
% 1.55/0.62    ~r1_tarski(sK1,sK2) | ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 1.55/0.62    inference(cnf_transformation,[],[f26])).
% 1.55/0.62  fof(f26,plain,(
% 1.55/0.62    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.62    inference(ennf_transformation,[],[f25])).
% 1.55/0.62  fof(f25,negated_conjecture,(
% 1.55/0.62    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.55/0.62    inference(negated_conjecture,[],[f24])).
% 1.55/0.62  fof(f24,conjecture,(
% 1.55/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.55/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 1.55/0.62  fof(f1491,plain,(
% 1.55/0.62    r1_tarski(sK1,sK2)),
% 1.55/0.62    inference(subsumption_resolution,[],[f1488,f133])).
% 1.55/0.62  fof(f133,plain,(
% 1.55/0.62    r1_tarski(sK1,sK0)),
% 1.55/0.62    inference(resolution,[],[f131,f89])).
% 1.55/0.62  fof(f89,plain,(
% 1.55/0.62    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.55/0.62    inference(equality_resolution,[],[f66])).
% 2.16/0.62  fof(f66,plain,(
% 2.16/0.62    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.16/0.62    inference(cnf_transformation,[],[f19])).
% 2.16/0.62  fof(f19,axiom,(
% 2.16/0.62    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.16/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.16/0.62  fof(f131,plain,(
% 2.16/0.62    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.16/0.62    inference(subsumption_resolution,[],[f127,f45])).
% 2.16/0.62  fof(f45,plain,(
% 2.16/0.62    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.16/0.62    inference(cnf_transformation,[],[f23])).
% 2.16/0.63  fof(f23,axiom,(
% 2.16/0.63    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.16/0.63  fof(f127,plain,(
% 2.16/0.63    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.16/0.63    inference(resolution,[],[f61,f44])).
% 2.16/0.63  fof(f44,plain,(
% 2.16/0.63    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.16/0.63    inference(cnf_transformation,[],[f26])).
% 2.16/0.63  fof(f61,plain,(
% 2.16/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f28,plain,(
% 2.16/0.63    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.16/0.63    inference(ennf_transformation,[],[f21])).
% 2.16/0.63  fof(f21,axiom,(
% 2.16/0.63    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.16/0.63  fof(f1488,plain,(
% 2.16/0.63    ~r1_tarski(sK1,sK0) | r1_tarski(sK1,sK2)),
% 2.16/0.63    inference(resolution,[],[f1469,f403])).
% 2.16/0.63  fof(f403,plain,(
% 2.16/0.63    r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 2.16/0.63    inference(resolution,[],[f402,f63])).
% 2.16/0.63  fof(f63,plain,(
% 2.16/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f31])).
% 2.16/0.63  fof(f31,plain,(
% 2.16/0.63    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.16/0.63    inference(ennf_transformation,[],[f3])).
% 2.16/0.63  fof(f3,axiom,(
% 2.16/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.16/0.63  fof(f402,plain,(
% 2.16/0.63    r1_xboole_0(k3_subset_1(sK0,sK2),sK1)),
% 2.16/0.63    inference(subsumption_resolution,[],[f401,f371])).
% 2.16/0.63  fof(f371,plain,(
% 2.16/0.63    ( ! [X3] : (r1_xboole_0(k3_subset_1(sK0,sK2),X3) | ~r1_tarski(X3,sK2)) )),
% 2.16/0.63    inference(superposition,[],[f194,f360])).
% 2.16/0.63  fof(f360,plain,(
% 2.16/0.63    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 2.16/0.63    inference(resolution,[],[f83,f43])).
% 2.16/0.63  fof(f43,plain,(
% 2.16/0.63    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.16/0.63    inference(cnf_transformation,[],[f26])).
% 2.16/0.63  fof(f83,plain,(
% 2.16/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 2.16/0.63    inference(definition_unfolding,[],[f64,f56])).
% 2.16/0.63  fof(f56,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.16/0.63    inference(cnf_transformation,[],[f4])).
% 2.16/0.63  fof(f4,axiom,(
% 2.16/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.16/0.63  fof(f64,plain,(
% 2.16/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f32])).
% 2.16/0.63  fof(f32,plain,(
% 2.16/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.16/0.63    inference(ennf_transformation,[],[f22])).
% 2.16/0.63  fof(f22,axiom,(
% 2.16/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.16/0.63  fof(f194,plain,(
% 2.16/0.63    ( ! [X2,X0,X1] : (r1_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X0) | ~r1_tarski(X0,X1)) )),
% 2.16/0.63    inference(resolution,[],[f84,f63])).
% 2.16/0.63  fof(f84,plain,(
% 2.16/0.63    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.16/0.63    inference(definition_unfolding,[],[f69,f56])).
% 2.16/0.63  fof(f69,plain,(
% 2.16/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 2.16/0.63    inference(cnf_transformation,[],[f33])).
% 2.16/0.63  fof(f33,plain,(
% 2.16/0.63    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.16/0.63    inference(ennf_transformation,[],[f14])).
% 2.16/0.63  fof(f14,axiom,(
% 2.16/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 2.16/0.63  fof(f401,plain,(
% 2.16/0.63    r1_xboole_0(k3_subset_1(sK0,sK2),sK1) | r1_tarski(sK1,sK2)),
% 2.16/0.63    inference(resolution,[],[f388,f41])).
% 2.16/0.63  fof(f41,plain,(
% 2.16/0.63    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 2.16/0.63    inference(cnf_transformation,[],[f26])).
% 2.16/0.63  fof(f388,plain,(
% 2.16/0.63    ( ! [X1] : (~r1_tarski(X1,k3_subset_1(sK0,sK1)) | r1_xboole_0(X1,sK1)) )),
% 2.16/0.63    inference(superposition,[],[f85,f361])).
% 2.16/0.63  fof(f361,plain,(
% 2.16/0.63    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 2.16/0.63    inference(resolution,[],[f83,f44])).
% 2.16/0.63  fof(f85,plain,(
% 2.16/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | r1_xboole_0(X0,X2)) )),
% 2.16/0.63    inference(definition_unfolding,[],[f71,f56])).
% 2.16/0.63  fof(f71,plain,(
% 2.16/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f34])).
% 2.16/0.63  fof(f34,plain,(
% 2.16/0.63    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.16/0.63    inference(ennf_transformation,[],[f5])).
% 2.16/0.63  fof(f5,axiom,(
% 2.16/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.16/0.63  fof(f1469,plain,(
% 2.16/0.63    ( ! [X0] : (~r1_xboole_0(X0,k3_subset_1(sK0,sK2)) | ~r1_tarski(X0,sK0) | r1_tarski(X0,sK2)) )),
% 2.16/0.63    inference(superposition,[],[f88,f1458])).
% 2.16/0.63  fof(f1458,plain,(
% 2.16/0.63    sK0 = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2)))),
% 2.16/0.63    inference(backward_demodulation,[],[f807,f1457])).
% 2.16/0.63  fof(f1457,plain,(
% 2.16/0.63    sK0 = k5_xboole_0(sK2,k3_subset_1(sK0,sK2))),
% 2.16/0.63    inference(backward_demodulation,[],[f372,f1456])).
% 2.16/0.63  fof(f1456,plain,(
% 2.16/0.63    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK2))),
% 2.16/0.63    inference(forward_demodulation,[],[f1443,f292])).
% 2.16/0.63  fof(f292,plain,(
% 2.16/0.63    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.16/0.63    inference(forward_demodulation,[],[f290,f77])).
% 2.16/0.63  fof(f77,plain,(
% 2.16/0.63    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 2.16/0.63    inference(definition_unfolding,[],[f47,f75])).
% 2.16/0.63  fof(f75,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.16/0.63    inference(definition_unfolding,[],[f54,f53])).
% 2.16/0.63  fof(f53,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f18])).
% 2.16/0.63  fof(f18,axiom,(
% 2.16/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.16/0.63  fof(f54,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.16/0.63    inference(cnf_transformation,[],[f20])).
% 2.16/0.63  fof(f20,axiom,(
% 2.16/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.16/0.63  fof(f47,plain,(
% 2.16/0.63    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.16/0.63    inference(cnf_transformation,[],[f6])).
% 2.16/0.63  fof(f6,axiom,(
% 2.16/0.63    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.16/0.63  fof(f290,plain,(
% 2.16/0.63    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0)) )),
% 2.16/0.63    inference(superposition,[],[f81,f76])).
% 2.16/0.63  fof(f76,plain,(
% 2.16/0.63    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 2.16/0.63    inference(definition_unfolding,[],[f46,f56])).
% 2.16/0.63  fof(f46,plain,(
% 2.16/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f10])).
% 2.16/0.63  fof(f10,axiom,(
% 2.16/0.63    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 2.16/0.63  fof(f81,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.16/0.63    inference(definition_unfolding,[],[f55,f75,f56])).
% 2.16/0.63  fof(f55,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.16/0.63    inference(cnf_transformation,[],[f16])).
% 2.16/0.63  fof(f16,axiom,(
% 2.16/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.16/0.63  fof(f1443,plain,(
% 2.16/0.63    k3_tarski(k1_enumset1(sK0,sK0,sK2)) = k5_xboole_0(sK0,k1_xboole_0)),
% 2.16/0.63    inference(superposition,[],[f288,f323])).
% 2.16/0.63  fof(f323,plain,(
% 2.16/0.63    k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK0,sK2))),
% 2.16/0.63    inference(resolution,[],[f319,f48])).
% 2.16/0.63  fof(f48,plain,(
% 2.16/0.63    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.16/0.63    inference(cnf_transformation,[],[f27])).
% 2.16/0.63  fof(f27,plain,(
% 2.16/0.63    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.16/0.63    inference(ennf_transformation,[],[f2])).
% 2.16/0.63  fof(f2,axiom,(
% 2.16/0.63    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.16/0.63  fof(f319,plain,(
% 2.16/0.63    v1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK0,sK2)))),
% 2.16/0.63    inference(forward_demodulation,[],[f314,f51])).
% 2.16/0.63  fof(f51,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f1])).
% 2.16/0.63  fof(f1,axiom,(
% 2.16/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.16/0.63  fof(f314,plain,(
% 2.16/0.63    v1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)))),
% 2.16/0.63    inference(resolution,[],[f167,f78])).
% 2.16/0.63  fof(f78,plain,(
% 2.16/0.63    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.16/0.63    inference(definition_unfolding,[],[f49,f56])).
% 2.16/0.63  fof(f49,plain,(
% 2.16/0.63    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f13])).
% 2.16/0.63  fof(f13,axiom,(
% 2.16/0.63    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.16/0.63  fof(f167,plain,(
% 2.16/0.63    ( ! [X2] : (~r1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,X2)),sK0) | v1_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,X2)))) )),
% 2.16/0.63    inference(resolution,[],[f153,f62])).
% 2.16/0.63  fof(f62,plain,(
% 2.16/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_xboole_0(X1) | ~r1_xboole_0(X1,X0)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f30])).
% 2.16/0.63  fof(f30,plain,(
% 2.16/0.63    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.16/0.63    inference(flattening,[],[f29])).
% 2.16/0.63  fof(f29,plain,(
% 2.16/0.63    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.16/0.63    inference(ennf_transformation,[],[f11])).
% 2.16/0.63  fof(f11,axiom,(
% 2.16/0.63    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 2.16/0.63  fof(f153,plain,(
% 2.16/0.63    ( ! [X0] : (r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X0)),sK0)) )),
% 2.16/0.63    inference(resolution,[],[f150,f79])).
% 2.16/0.63  fof(f79,plain,(
% 2.16/0.63    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 2.16/0.63    inference(definition_unfolding,[],[f50,f56])).
% 2.16/0.63  fof(f50,plain,(
% 2.16/0.63    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f8])).
% 2.16/0.63  fof(f8,axiom,(
% 2.16/0.63    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.16/0.63  fof(f150,plain,(
% 2.16/0.63    ( ! [X9] : (~r1_tarski(X9,sK2) | r1_tarski(X9,sK0)) )),
% 2.16/0.63    inference(resolution,[],[f73,f132])).
% 2.16/0.63  fof(f132,plain,(
% 2.16/0.63    r1_tarski(sK2,sK0)),
% 2.16/0.63    inference(resolution,[],[f130,f89])).
% 2.16/0.63  fof(f130,plain,(
% 2.16/0.63    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 2.16/0.63    inference(subsumption_resolution,[],[f126,f45])).
% 2.16/0.63  fof(f126,plain,(
% 2.16/0.63    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.16/0.63    inference(resolution,[],[f61,f43])).
% 2.16/0.63  fof(f73,plain,(
% 2.16/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f38])).
% 2.16/0.63  fof(f38,plain,(
% 2.16/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.16/0.63    inference(flattening,[],[f37])).
% 2.16/0.63  fof(f37,plain,(
% 2.16/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.16/0.63    inference(ennf_transformation,[],[f7])).
% 2.16/0.63  fof(f7,axiom,(
% 2.16/0.63    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.16/0.63  fof(f288,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X1,X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) )),
% 2.16/0.63    inference(superposition,[],[f81,f51])).
% 2.16/0.63  fof(f372,plain,(
% 2.16/0.63    k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) = k3_tarski(k1_enumset1(sK0,sK0,sK2))),
% 2.16/0.63    inference(forward_demodulation,[],[f366,f80])).
% 2.16/0.63  fof(f80,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.16/0.63    inference(definition_unfolding,[],[f52,f53,f53])).
% 2.16/0.63  fof(f52,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f17])).
% 2.16/0.63  fof(f17,axiom,(
% 2.16/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.16/0.63  fof(f366,plain,(
% 2.16/0.63    k3_tarski(k1_enumset1(sK2,sK2,sK0)) = k5_xboole_0(sK2,k3_subset_1(sK0,sK2))),
% 2.16/0.63    inference(superposition,[],[f81,f360])).
% 2.16/0.63  fof(f807,plain,(
% 2.16/0.63    k5_xboole_0(sK2,k3_subset_1(sK0,sK2)) = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2)))),
% 2.16/0.63    inference(forward_demodulation,[],[f806,f372])).
% 2.16/0.63  fof(f806,plain,(
% 2.16/0.63    k3_tarski(k1_enumset1(sK0,sK0,sK2)) = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2)))),
% 2.16/0.63    inference(forward_demodulation,[],[f801,f80])).
% 2.16/0.63  fof(f801,plain,(
% 2.16/0.63    k3_tarski(k1_enumset1(sK2,sK2,sK0)) = k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK0,sK2)))),
% 2.16/0.63    inference(superposition,[],[f82,f360])).
% 2.16/0.63  fof(f82,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 2.16/0.63    inference(definition_unfolding,[],[f57,f75,f56,f75])).
% 2.16/0.63  fof(f57,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f9])).
% 2.16/0.63  fof(f9,axiom,(
% 2.16/0.63    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.16/0.63  fof(f88,plain,(
% 2.16/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 2.16/0.63    inference(definition_unfolding,[],[f74,f75])).
% 2.16/0.63  fof(f74,plain,(
% 2.16/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f40])).
% 2.16/0.63  fof(f40,plain,(
% 2.16/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.16/0.63    inference(flattening,[],[f39])).
% 2.16/0.63  fof(f39,plain,(
% 2.16/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.16/0.63    inference(ennf_transformation,[],[f12])).
% 2.16/0.63  fof(f12,axiom,(
% 2.16/0.63    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 2.16/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 2.16/0.63  fof(f1701,plain,(
% 2.16/0.63    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 2.16/0.63    inference(subsumption_resolution,[],[f1697,f365])).
% 2.16/0.63  fof(f365,plain,(
% 2.16/0.63    r1_tarski(k3_subset_1(sK0,sK2),sK0)),
% 2.16/0.63    inference(superposition,[],[f79,f360])).
% 2.16/0.63  fof(f1697,plain,(
% 2.16/0.63    ~r1_tarski(k3_subset_1(sK0,sK2),sK0) | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 2.16/0.63    inference(resolution,[],[f1671,f402])).
% 2.16/0.63  fof(f1671,plain,(
% 2.16/0.63    ( ! [X11] : (~r1_xboole_0(X11,sK1) | ~r1_tarski(X11,sK0) | r1_tarski(X11,k3_subset_1(sK0,sK1))) )),
% 2.16/0.63    inference(superposition,[],[f533,f1454])).
% 2.16/0.63  fof(f1454,plain,(
% 2.16/0.63    sK0 = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1)))),
% 2.16/0.63    inference(backward_demodulation,[],[f809,f1453])).
% 2.16/0.63  fof(f1453,plain,(
% 2.16/0.63    sK0 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))),
% 2.16/0.63    inference(backward_demodulation,[],[f392,f1452])).
% 2.16/0.63  fof(f1452,plain,(
% 2.16/0.63    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 2.16/0.63    inference(forward_demodulation,[],[f1442,f292])).
% 2.16/0.63  fof(f1442,plain,(
% 2.16/0.63    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)),
% 2.16/0.63    inference(superposition,[],[f288,f254])).
% 2.16/0.63  fof(f254,plain,(
% 2.16/0.63    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 2.16/0.63    inference(resolution,[],[f250,f48])).
% 2.16/0.63  fof(f250,plain,(
% 2.16/0.63    v1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),
% 2.16/0.63    inference(forward_demodulation,[],[f245,f51])).
% 2.16/0.63  fof(f245,plain,(
% 2.16/0.63    v1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),
% 2.16/0.63    inference(resolution,[],[f159,f78])).
% 2.16/0.63  fof(f159,plain,(
% 2.16/0.63    ( ! [X2] : (~r1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X2)),sK0) | v1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X2)))) )),
% 2.16/0.63    inference(resolution,[],[f151,f62])).
% 2.16/0.63  fof(f151,plain,(
% 2.16/0.63    ( ! [X0] : (r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK0)) )),
% 2.16/0.63    inference(resolution,[],[f149,f79])).
% 2.16/0.63  fof(f149,plain,(
% 2.16/0.63    ( ! [X8] : (~r1_tarski(X8,sK1) | r1_tarski(X8,sK0)) )),
% 2.16/0.63    inference(resolution,[],[f73,f133])).
% 2.16/0.63  fof(f392,plain,(
% 2.16/0.63    k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 2.16/0.63    inference(forward_demodulation,[],[f386,f80])).
% 2.16/0.63  fof(f386,plain,(
% 2.16/0.63    k3_tarski(k1_enumset1(sK1,sK1,sK0)) = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))),
% 2.16/0.63    inference(superposition,[],[f81,f361])).
% 2.16/0.63  fof(f809,plain,(
% 2.16/0.63    k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1)))),
% 2.16/0.63    inference(forward_demodulation,[],[f808,f392])).
% 2.16/0.63  fof(f808,plain,(
% 2.16/0.63    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1)))),
% 2.16/0.63    inference(forward_demodulation,[],[f802,f80])).
% 2.16/0.63  fof(f802,plain,(
% 2.16/0.63    k3_tarski(k1_enumset1(sK1,sK1,sK0)) = k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1)))),
% 2.16/0.63    inference(superposition,[],[f82,f361])).
% 2.16/0.63  fof(f533,plain,(
% 2.16/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0))) | ~r1_xboole_0(X2,X1) | r1_tarski(X2,X0)) )),
% 2.16/0.63    inference(superposition,[],[f88,f80])).
% 2.16/0.63  % SZS output end Proof for theBenchmark
% 2.16/0.63  % (11243)------------------------------
% 2.16/0.63  % (11243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.63  % (11243)Termination reason: Refutation
% 2.16/0.63  
% 2.16/0.63  % (11243)Memory used [KB]: 7164
% 2.16/0.63  % (11243)Time elapsed: 0.219 s
% 2.16/0.63  % (11243)------------------------------
% 2.16/0.63  % (11243)------------------------------
% 2.16/0.63  % (11236)Success in time 0.276 s
%------------------------------------------------------------------------------
