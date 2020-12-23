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
% DateTime   : Thu Dec  3 12:44:24 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 464 expanded)
%              Number of leaves         :   20 ( 125 expanded)
%              Depth                    :   21
%              Number of atoms          :  222 (1054 expanded)
%              Number of equality atoms :   63 ( 221 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1630,plain,(
    $false ),
    inference(global_subsumption,[],[f1617,f1629])).

fof(f1629,plain,(
    ~ r1_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f1628,f1136])).

fof(f1136,plain,(
    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1073,f44])).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1073,plain,(
    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f204,f273])).

fof(f273,plain,(
    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK0)) ),
    inference(forward_demodulation,[],[f252,f139])).

fof(f139,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f136,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f136,plain,(
    r1_tarski(sK1,sK0) ),
    inference(forward_demodulation,[],[f133,f42])).

fof(f42,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f133,plain,(
    r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f105,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(f105,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f41,f40,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,k3_subset_1(X0,X2))
             => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f41,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f252,plain,(
    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK0,k2_xboole_0(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f136,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f74,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f53,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f204,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f64,f44])).

fof(f1628,plain,(
    ~ r1_xboole_0(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1627,f204])).

fof(f1627,plain,(
    ~ r1_xboole_0(sK2,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0))) ),
    inference(forward_demodulation,[],[f1625,f1324])).

fof(f1324,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f136,f153,f344])).

fof(f344,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = X1
      | ~ r1_tarski(X1,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f341])).

fof(f341,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X1)
      | k2_xboole_0(X1,X0) = X1
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X1)
      | k2_xboole_0(X1,X0) = X1 ) ),
    inference(resolution,[],[f69,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,sK3(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,sK3(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f153,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f56,f79])).

fof(f79,plain,(
    ! [X1] : r3_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    <=> r3_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) )
    <=> r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      | r1_tarski(X1,X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f1625,plain,(
    ~ r1_xboole_0(sK2,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f346,f1532,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(forward_demodulation,[],[f77,f64])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))
      | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f72,f46])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(f1532,plain,(
    ~ r1_tarski(sK2,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f39,f1531])).

fof(f1531,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f1530,f44])).

fof(f1530,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f1522,f1188])).

fof(f1188,plain,(
    ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f1182,f64])).

fof(f1182,plain,(
    ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),X0)) ),
    inference(superposition,[],[f64,f1136])).

fof(f1522,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0))) ),
    inference(backward_demodulation,[],[f367,f1324])).

fof(f367,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f40,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(backward_demodulation,[],[f75,f64])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f55,f73])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f39,plain,(
    ~ r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f346,plain,(
    ! [X0] : r1_tarski(sK2,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f43,f183])).

fof(f183,plain,(
    ! [X8] : k2_xboole_0(sK0,X8) = k2_xboole_0(sK2,k2_xboole_0(sK0,X8)) ),
    inference(superposition,[],[f63,f125])).

fof(f125,plain,(
    sK0 = k2_xboole_0(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f116,f54])).

fof(f116,plain,(
    r1_tarski(sK2,sK0) ),
    inference(forward_demodulation,[],[f113,f42])).

fof(f113,plain,(
    r1_tarski(sK2,k3_tarski(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f104,f51])).

fof(f104,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f41,f37,f50])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1617,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f1589,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1589,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f1293,f1418,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f1418,plain,(
    r1_tarski(sK1,k5_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f38,f1417])).

fof(f1417,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f1416,f44])).

fof(f1416,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f1408,f1198])).

fof(f1198,plain,(
    ! [X0] : k5_xboole_0(sK2,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK2,X0))) ),
    inference(forward_demodulation,[],[f1192,f64])).

fof(f1192,plain,(
    ! [X0] : k5_xboole_0(sK2,X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK2),X0)) ),
    inference(superposition,[],[f64,f1145])).

fof(f1145,plain,(
    sK2 = k5_xboole_0(sK0,k5_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f1074,f44])).

fof(f1074,plain,(
    sK2 = k5_xboole_0(sK0,k5_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f204,f269])).

fof(f269,plain,(
    sK2 = k5_xboole_0(sK2,k5_xboole_0(sK0,sK0)) ),
    inference(forward_demodulation,[],[f256,f125])).

fof(f256,plain,(
    sK2 = k5_xboole_0(sK2,k5_xboole_0(sK0,k2_xboole_0(sK2,sK0))) ),
    inference(unit_resulting_resolution,[],[f116,f81])).

fof(f1408,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK2,sK0))) ),
    inference(backward_demodulation,[],[f366,f1326])).

fof(f1326,plain,(
    sK0 = k2_xboole_0(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f116,f153,f344])).

fof(f366,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK2,k2_xboole_0(sK0,sK2)))) ),
    inference(unit_resulting_resolution,[],[f37,f80])).

fof(f38,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f1293,plain,(
    r1_xboole_0(k5_xboole_0(sK0,sK2),sK2) ),
    inference(forward_demodulation,[],[f1272,f44])).

fof(f1272,plain,(
    r1_xboole_0(k5_xboole_0(sK2,sK0),sK2) ),
    inference(unit_resulting_resolution,[],[f116,f153,f297])).

fof(f297,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k5_xboole_0(X0,X1))
      | r1_xboole_0(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f85,f81])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(forward_demodulation,[],[f78,f64])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f71,f46])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:09:16 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.50  % (2589)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (2598)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (2598)Refutation not found, incomplete strategy% (2598)------------------------------
% 0.21/0.50  % (2598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (2598)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (2598)Memory used [KB]: 10618
% 0.21/0.50  % (2598)Time elapsed: 0.093 s
% 0.21/0.50  % (2598)------------------------------
% 0.21/0.50  % (2598)------------------------------
% 0.21/0.50  % (2610)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (2603)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.50  % (2597)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (2597)Refutation not found, incomplete strategy% (2597)------------------------------
% 0.21/0.50  % (2597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2593)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (2590)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (2597)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2597)Memory used [KB]: 10618
% 0.21/0.51  % (2597)Time elapsed: 0.096 s
% 0.21/0.51  % (2597)------------------------------
% 0.21/0.51  % (2597)------------------------------
% 0.21/0.51  % (2591)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (2587)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (2588)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (2602)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (2594)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (2592)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (2608)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (2605)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (2607)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (2609)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (2600)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (2604)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (2604)Refutation not found, incomplete strategy% (2604)------------------------------
% 0.21/0.54  % (2604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2604)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2604)Memory used [KB]: 10618
% 0.21/0.54  % (2604)Time elapsed: 0.132 s
% 0.21/0.54  % (2604)------------------------------
% 0.21/0.54  % (2604)------------------------------
% 0.21/0.54  % (2615)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (2612)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (2614)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (2613)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (2601)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (2611)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (2616)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (2606)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (2599)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.55  % (2595)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.56  % (2596)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.97/0.63  % (2669)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.97/0.64  % (2673)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.97/0.65  % (2683)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.18/0.71  % (2611)Refutation found. Thanks to Tanya!
% 2.18/0.71  % SZS status Theorem for theBenchmark
% 2.74/0.73  % SZS output start Proof for theBenchmark
% 2.74/0.73  fof(f1630,plain,(
% 2.74/0.73    $false),
% 2.74/0.73    inference(global_subsumption,[],[f1617,f1629])).
% 2.74/0.73  fof(f1629,plain,(
% 2.74/0.73    ~r1_xboole_0(sK2,sK1)),
% 2.74/0.73    inference(forward_demodulation,[],[f1628,f1136])).
% 2.74/0.73  fof(f1136,plain,(
% 2.74/0.73    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 2.74/0.73    inference(forward_demodulation,[],[f1073,f44])).
% 2.74/0.73  fof(f44,plain,(
% 2.74/0.73    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.74/0.73    inference(cnf_transformation,[],[f1])).
% 2.74/0.73  fof(f1,axiom,(
% 2.74/0.73    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.74/0.73  fof(f1073,plain,(
% 2.74/0.73    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,sK0))),
% 2.74/0.73    inference(superposition,[],[f204,f273])).
% 2.74/0.73  fof(f273,plain,(
% 2.74/0.73    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK0))),
% 2.74/0.73    inference(forward_demodulation,[],[f252,f139])).
% 2.74/0.73  fof(f139,plain,(
% 2.74/0.73    sK0 = k2_xboole_0(sK1,sK0)),
% 2.74/0.73    inference(unit_resulting_resolution,[],[f136,f54])).
% 2.74/0.73  fof(f54,plain,(
% 2.74/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.74/0.73    inference(cnf_transformation,[],[f29])).
% 2.74/0.73  fof(f29,plain,(
% 2.74/0.73    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.74/0.73    inference(ennf_transformation,[],[f7])).
% 2.74/0.73  fof(f7,axiom,(
% 2.74/0.73    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.74/0.73  fof(f136,plain,(
% 2.74/0.73    r1_tarski(sK1,sK0)),
% 2.74/0.73    inference(forward_demodulation,[],[f133,f42])).
% 2.74/0.73  fof(f42,plain,(
% 2.74/0.73    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 2.74/0.73    inference(cnf_transformation,[],[f17])).
% 2.74/0.73  fof(f17,axiom,(
% 2.74/0.73    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 2.74/0.73  fof(f133,plain,(
% 2.74/0.73    r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0)))),
% 2.74/0.73    inference(unit_resulting_resolution,[],[f105,f51])).
% 2.74/0.73  fof(f51,plain,(
% 2.74/0.73    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 2.74/0.73    inference(cnf_transformation,[],[f26])).
% 2.74/0.73  fof(f26,plain,(
% 2.74/0.73    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 2.74/0.73    inference(ennf_transformation,[],[f16])).
% 2.74/0.73  fof(f16,axiom,(
% 2.74/0.73    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).
% 2.74/0.73  fof(f105,plain,(
% 2.74/0.73    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.74/0.73    inference(unit_resulting_resolution,[],[f41,f40,f50])).
% 2.74/0.73  fof(f50,plain,(
% 2.74/0.73    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.74/0.73    inference(cnf_transformation,[],[f25])).
% 2.74/0.73  fof(f25,plain,(
% 2.74/0.73    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.74/0.73    inference(ennf_transformation,[],[f18])).
% 2.74/0.73  fof(f18,axiom,(
% 2.74/0.73    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.74/0.73  fof(f40,plain,(
% 2.74/0.73    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.74/0.73    inference(cnf_transformation,[],[f24])).
% 2.74/0.73  fof(f24,plain,(
% 2.74/0.73    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.74/0.73    inference(flattening,[],[f23])).
% 2.74/0.73  fof(f23,plain,(
% 2.74/0.73    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.74/0.73    inference(ennf_transformation,[],[f22])).
% 2.74/0.73  fof(f22,negated_conjecture,(
% 2.74/0.73    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 2.74/0.73    inference(negated_conjecture,[],[f21])).
% 2.74/0.73  fof(f21,conjecture,(
% 2.74/0.73    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 2.74/0.73  fof(f41,plain,(
% 2.74/0.73    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.74/0.73    inference(cnf_transformation,[],[f20])).
% 2.74/0.73  fof(f20,axiom,(
% 2.74/0.73    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.74/0.73  fof(f252,plain,(
% 2.74/0.73    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK0,k2_xboole_0(sK1,sK0)))),
% 2.74/0.73    inference(unit_resulting_resolution,[],[f136,f81])).
% 2.74/0.73  fof(f81,plain,(
% 2.74/0.73    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) = X0 | ~r1_tarski(X0,X1)) )),
% 2.74/0.73    inference(backward_demodulation,[],[f74,f64])).
% 2.74/0.73  fof(f64,plain,(
% 2.74/0.73    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.74/0.73    inference(cnf_transformation,[],[f14])).
% 2.74/0.73  fof(f14,axiom,(
% 2.74/0.73    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.74/0.73  fof(f74,plain,(
% 2.74/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = X0) )),
% 2.74/0.73    inference(definition_unfolding,[],[f53,f46])).
% 2.74/0.73  fof(f46,plain,(
% 2.74/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.74/0.73    inference(cnf_transformation,[],[f15])).
% 2.74/0.73  fof(f15,axiom,(
% 2.74/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.74/0.73  fof(f53,plain,(
% 2.74/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.74/0.73    inference(cnf_transformation,[],[f28])).
% 2.74/0.73  fof(f28,plain,(
% 2.74/0.73    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.74/0.73    inference(ennf_transformation,[],[f9])).
% 2.74/0.73  fof(f9,axiom,(
% 2.74/0.73    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.74/0.73  fof(f204,plain,(
% 2.74/0.73    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) )),
% 2.74/0.73    inference(superposition,[],[f64,f44])).
% 2.74/0.73  fof(f1628,plain,(
% 2.74/0.73    ~r1_xboole_0(sK2,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),
% 2.74/0.73    inference(forward_demodulation,[],[f1627,f204])).
% 2.74/0.73  fof(f1627,plain,(
% 2.74/0.73    ~r1_xboole_0(sK2,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)))),
% 2.74/0.73    inference(forward_demodulation,[],[f1625,f1324])).
% 2.74/0.73  fof(f1324,plain,(
% 2.74/0.73    sK0 = k2_xboole_0(sK0,sK1)),
% 2.74/0.73    inference(unit_resulting_resolution,[],[f136,f153,f344])).
% 2.74/0.73  fof(f344,plain,(
% 2.74/0.73    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = X1 | ~r1_tarski(X1,X1) | ~r1_tarski(X0,X1)) )),
% 2.74/0.73    inference(duplicate_literal_removal,[],[f341])).
% 2.74/0.73  fof(f341,plain,(
% 2.74/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X1) | k2_xboole_0(X1,X0) = X1 | ~r1_tarski(X0,X1) | ~r1_tarski(X1,X1) | k2_xboole_0(X1,X0) = X1) )),
% 2.74/0.73    inference(resolution,[],[f69,f67])).
% 2.74/0.73  fof(f67,plain,(
% 2.74/0.73    ( ! [X2,X0,X1] : (r1_tarski(X0,sK3(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1) | k2_xboole_0(X0,X2) = X1) )),
% 2.74/0.73    inference(cnf_transformation,[],[f36])).
% 2.74/0.73  fof(f36,plain,(
% 2.74/0.73    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.74/0.73    inference(flattening,[],[f35])).
% 2.74/0.73  fof(f35,plain,(
% 2.74/0.73    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.74/0.73    inference(ennf_transformation,[],[f8])).
% 2.74/0.73  fof(f8,axiom,(
% 2.74/0.73    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).
% 2.74/0.73  fof(f69,plain,(
% 2.74/0.73    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK3(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1) | k2_xboole_0(X0,X2) = X1) )),
% 2.74/0.73    inference(cnf_transformation,[],[f36])).
% 2.74/0.73  fof(f153,plain,(
% 2.74/0.73    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.74/0.73    inference(duplicate_literal_removal,[],[f144])).
% 2.74/0.73  fof(f144,plain,(
% 2.74/0.73    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 2.74/0.73    inference(resolution,[],[f56,f79])).
% 2.74/0.73  fof(f79,plain,(
% 2.74/0.73    ( ! [X1] : (r3_xboole_0(X1,X1)) )),
% 2.74/0.73    inference(equality_resolution,[],[f60])).
% 2.74/0.73  fof(f60,plain,(
% 2.74/0.73    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | X0 != X1) )),
% 2.74/0.73    inference(cnf_transformation,[],[f31])).
% 2.74/0.73  fof(f31,plain,(
% 2.74/0.73    ! [X0,X1] : ((r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1)) <=> r3_xboole_0(X0,X1))),
% 2.74/0.73    inference(ennf_transformation,[],[f5])).
% 2.74/0.73  fof(f5,axiom,(
% 2.74/0.73    ! [X0,X1] : (~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1)) <=> r3_xboole_0(X0,X1))),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_xboole_1)).
% 2.74/0.73  fof(f56,plain,(
% 2.74/0.73    ( ! [X0,X1] : (~r3_xboole_0(X0,X1) | r1_tarski(X1,X0) | r1_tarski(X0,X1)) )),
% 2.74/0.73    inference(cnf_transformation,[],[f3])).
% 2.74/0.73  fof(f3,axiom,(
% 2.74/0.73    ! [X0,X1] : (r3_xboole_0(X0,X1) <=> (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).
% 2.74/0.73  fof(f1625,plain,(
% 2.74/0.73    ~r1_xboole_0(sK2,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))))),
% 2.74/0.73    inference(unit_resulting_resolution,[],[f346,f1532,f84])).
% 2.74/0.73  fof(f84,plain,(
% 2.74/0.73    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 2.74/0.73    inference(forward_demodulation,[],[f77,f64])).
% 2.74/0.73  fof(f77,plain,(
% 2.74/0.73    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 2.74/0.73    inference(definition_unfolding,[],[f72,f46])).
% 2.74/0.73  fof(f72,plain,(
% 2.74/0.73    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 2.74/0.73    inference(cnf_transformation,[],[f6])).
% 2.74/0.73  fof(f6,axiom,(
% 2.74/0.73    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).
% 2.74/0.73  fof(f1532,plain,(
% 2.74/0.73    ~r1_tarski(sK2,k5_xboole_0(sK0,sK1))),
% 2.74/0.73    inference(backward_demodulation,[],[f39,f1531])).
% 2.74/0.73  fof(f1531,plain,(
% 2.74/0.73    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 2.74/0.73    inference(forward_demodulation,[],[f1530,f44])).
% 2.74/0.73  fof(f1530,plain,(
% 2.74/0.73    k3_subset_1(sK0,sK1) = k5_xboole_0(sK1,sK0)),
% 2.74/0.73    inference(forward_demodulation,[],[f1522,f1188])).
% 2.74/0.73  fof(f1188,plain,(
% 2.74/0.73    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,X0)))) )),
% 2.74/0.73    inference(forward_demodulation,[],[f1182,f64])).
% 2.74/0.73  fof(f1182,plain,(
% 2.74/0.73    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),X0))) )),
% 2.74/0.73    inference(superposition,[],[f64,f1136])).
% 2.74/0.73  fof(f1522,plain,(
% 2.74/0.73    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)))),
% 2.74/0.73    inference(backward_demodulation,[],[f367,f1324])).
% 2.74/0.73  fof(f367,plain,(
% 2.74/0.73    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))))),
% 2.74/0.73    inference(unit_resulting_resolution,[],[f40,f80])).
% 2.74/0.73  fof(f80,plain,(
% 2.74/0.73    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.74/0.73    inference(backward_demodulation,[],[f75,f64])).
% 2.74/0.73  fof(f75,plain,(
% 2.74/0.73    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 2.74/0.73    inference(definition_unfolding,[],[f55,f73])).
% 2.74/0.73  fof(f73,plain,(
% 2.74/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 2.74/0.73    inference(definition_unfolding,[],[f45,f46])).
% 2.74/0.73  fof(f45,plain,(
% 2.74/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.74/0.73    inference(cnf_transformation,[],[f4])).
% 2.74/0.73  fof(f4,axiom,(
% 2.74/0.73    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.74/0.73  fof(f55,plain,(
% 2.74/0.73    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.74/0.73    inference(cnf_transformation,[],[f30])).
% 2.74/0.73  fof(f30,plain,(
% 2.74/0.73    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.74/0.73    inference(ennf_transformation,[],[f19])).
% 2.74/0.73  fof(f19,axiom,(
% 2.74/0.73    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.74/0.73  fof(f39,plain,(
% 2.74/0.73    ~r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 2.74/0.73    inference(cnf_transformation,[],[f24])).
% 2.74/0.73  fof(f346,plain,(
% 2.74/0.73    ( ! [X0] : (r1_tarski(sK2,k2_xboole_0(sK0,X0))) )),
% 2.74/0.73    inference(superposition,[],[f43,f183])).
% 2.74/0.73  fof(f183,plain,(
% 2.74/0.73    ( ! [X8] : (k2_xboole_0(sK0,X8) = k2_xboole_0(sK2,k2_xboole_0(sK0,X8))) )),
% 2.74/0.73    inference(superposition,[],[f63,f125])).
% 2.74/0.73  fof(f125,plain,(
% 2.74/0.73    sK0 = k2_xboole_0(sK2,sK0)),
% 2.74/0.73    inference(unit_resulting_resolution,[],[f116,f54])).
% 2.74/0.73  fof(f116,plain,(
% 2.74/0.73    r1_tarski(sK2,sK0)),
% 2.74/0.73    inference(forward_demodulation,[],[f113,f42])).
% 2.74/0.73  fof(f113,plain,(
% 2.74/0.73    r1_tarski(sK2,k3_tarski(k1_zfmisc_1(sK0)))),
% 2.74/0.73    inference(unit_resulting_resolution,[],[f104,f51])).
% 2.74/0.73  fof(f104,plain,(
% 2.74/0.73    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 2.74/0.73    inference(unit_resulting_resolution,[],[f41,f37,f50])).
% 2.74/0.73  fof(f37,plain,(
% 2.74/0.73    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.74/0.73    inference(cnf_transformation,[],[f24])).
% 2.74/0.73  fof(f63,plain,(
% 2.74/0.73    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.74/0.73    inference(cnf_transformation,[],[f10])).
% 2.74/0.73  fof(f10,axiom,(
% 2.74/0.73    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.74/0.73  fof(f43,plain,(
% 2.74/0.73    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.74/0.73    inference(cnf_transformation,[],[f13])).
% 2.74/0.73  fof(f13,axiom,(
% 2.74/0.73    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.74/0.73  fof(f1617,plain,(
% 2.74/0.73    r1_xboole_0(sK2,sK1)),
% 2.74/0.73    inference(unit_resulting_resolution,[],[f1589,f52])).
% 2.74/0.73  fof(f52,plain,(
% 2.74/0.73    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.74/0.73    inference(cnf_transformation,[],[f27])).
% 2.74/0.73  fof(f27,plain,(
% 2.74/0.73    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.74/0.73    inference(ennf_transformation,[],[f2])).
% 2.74/0.73  fof(f2,axiom,(
% 2.74/0.73    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.74/0.73  fof(f1589,plain,(
% 2.74/0.73    r1_xboole_0(sK1,sK2)),
% 2.74/0.73    inference(unit_resulting_resolution,[],[f1293,f1418,f66])).
% 2.74/0.73  fof(f66,plain,(
% 2.74/0.73    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 2.74/0.73    inference(cnf_transformation,[],[f34])).
% 2.74/0.73  fof(f34,plain,(
% 2.74/0.73    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.74/0.73    inference(flattening,[],[f33])).
% 2.74/0.73  fof(f33,plain,(
% 2.74/0.73    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.74/0.73    inference(ennf_transformation,[],[f11])).
% 2.74/0.73  fof(f11,axiom,(
% 2.74/0.73    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.74/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 2.74/0.73  fof(f1418,plain,(
% 2.74/0.73    r1_tarski(sK1,k5_xboole_0(sK0,sK2))),
% 2.74/0.73    inference(backward_demodulation,[],[f38,f1417])).
% 2.74/0.73  fof(f1417,plain,(
% 2.74/0.73    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 2.74/0.73    inference(forward_demodulation,[],[f1416,f44])).
% 2.74/0.73  fof(f1416,plain,(
% 2.74/0.73    k3_subset_1(sK0,sK2) = k5_xboole_0(sK2,sK0)),
% 2.74/0.73    inference(forward_demodulation,[],[f1408,f1198])).
% 2.74/0.73  fof(f1198,plain,(
% 2.74/0.73    ( ! [X0] : (k5_xboole_0(sK2,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK2,X0)))) )),
% 2.74/0.73    inference(forward_demodulation,[],[f1192,f64])).
% 2.74/0.73  fof(f1192,plain,(
% 2.74/0.73    ( ! [X0] : (k5_xboole_0(sK2,X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK2),X0))) )),
% 2.74/0.73    inference(superposition,[],[f64,f1145])).
% 2.74/0.73  fof(f1145,plain,(
% 2.74/0.73    sK2 = k5_xboole_0(sK0,k5_xboole_0(sK0,sK2))),
% 2.74/0.73    inference(forward_demodulation,[],[f1074,f44])).
% 2.74/0.73  fof(f1074,plain,(
% 2.74/0.73    sK2 = k5_xboole_0(sK0,k5_xboole_0(sK2,sK0))),
% 2.74/0.73    inference(superposition,[],[f204,f269])).
% 2.74/0.73  fof(f269,plain,(
% 2.74/0.73    sK2 = k5_xboole_0(sK2,k5_xboole_0(sK0,sK0))),
% 2.74/0.73    inference(forward_demodulation,[],[f256,f125])).
% 2.74/0.73  fof(f256,plain,(
% 2.74/0.73    sK2 = k5_xboole_0(sK2,k5_xboole_0(sK0,k2_xboole_0(sK2,sK0)))),
% 2.74/0.73    inference(unit_resulting_resolution,[],[f116,f81])).
% 2.74/0.73  fof(f1408,plain,(
% 2.74/0.73    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK2,sK0)))),
% 2.74/0.73    inference(backward_demodulation,[],[f366,f1326])).
% 2.74/0.73  fof(f1326,plain,(
% 2.74/0.73    sK0 = k2_xboole_0(sK0,sK2)),
% 2.74/0.73    inference(unit_resulting_resolution,[],[f116,f153,f344])).
% 2.74/0.73  fof(f366,plain,(
% 2.74/0.73    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK2,k2_xboole_0(sK0,sK2))))),
% 2.74/0.73    inference(unit_resulting_resolution,[],[f37,f80])).
% 2.74/0.73  fof(f38,plain,(
% 2.74/0.73    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 2.74/0.73    inference(cnf_transformation,[],[f24])).
% 2.74/0.73  fof(f1293,plain,(
% 2.74/0.73    r1_xboole_0(k5_xboole_0(sK0,sK2),sK2)),
% 2.74/0.73    inference(forward_demodulation,[],[f1272,f44])).
% 2.74/0.73  fof(f1272,plain,(
% 2.74/0.73    r1_xboole_0(k5_xboole_0(sK2,sK0),sK2)),
% 2.74/0.73    inference(unit_resulting_resolution,[],[f116,f153,f297])).
% 2.74/0.73  fof(f297,plain,(
% 2.74/0.73    ( ! [X2,X0,X1] : (~r1_tarski(X2,k5_xboole_0(X0,X1)) | r1_xboole_0(X2,X0) | ~r1_tarski(X0,X1)) )),
% 2.74/0.73    inference(superposition,[],[f85,f81])).
% 2.74/0.73  fof(f85,plain,(
% 2.74/0.73    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 2.74/0.73    inference(forward_demodulation,[],[f78,f64])).
% 2.74/0.73  fof(f78,plain,(
% 2.74/0.73    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 2.74/0.73    inference(definition_unfolding,[],[f71,f46])).
% 2.74/0.73  fof(f71,plain,(
% 2.74/0.73    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 2.74/0.73    inference(cnf_transformation,[],[f6])).
% 2.74/0.73  % SZS output end Proof for theBenchmark
% 2.74/0.73  % (2611)------------------------------
% 2.74/0.73  % (2611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.74/0.73  % (2611)Termination reason: Refutation
% 2.74/0.73  
% 2.74/0.73  % (2611)Memory used [KB]: 8571
% 2.74/0.73  % (2611)Time elapsed: 0.305 s
% 2.74/0.73  % (2611)------------------------------
% 2.74/0.73  % (2611)------------------------------
% 2.74/0.73  % (2586)Success in time 0.354 s
%------------------------------------------------------------------------------
