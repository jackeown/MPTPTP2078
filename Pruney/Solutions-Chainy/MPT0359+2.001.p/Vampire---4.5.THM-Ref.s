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
% DateTime   : Thu Dec  3 12:44:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 (1217 expanded)
%              Number of leaves         :   20 ( 384 expanded)
%              Depth                    :   20
%              Number of atoms          :  143 (1603 expanded)
%              Number of equality atoms :   89 (1024 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f657,plain,(
    $false ),
    inference(subsumption_resolution,[],[f656,f111])).

fof(f111,plain,(
    sK0 != sK1 ),
    inference(subsumption_resolution,[],[f109,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f109,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | sK0 != sK1 ),
    inference(backward_demodulation,[],[f94,f108])).

fof(f108,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f87,f107])).

fof(f107,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f104,f61])).

fof(f61,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f34,f57])).

fof(f57,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f37,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f104,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f87,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k3_subset_1(X1,X1) ),
    inference(resolution,[],[f48,f71])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f62,f61])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f36,f57])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f94,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k4_xboole_0(sK0,sK0),sK0) ),
    inference(backward_demodulation,[],[f70,f87])).

fof(f70,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | sK0 != sK1 ),
    inference(inner_rewriting,[],[f69])).

fof(f69,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f59,f61])).

fof(f59,plain,
    ( sK1 != k3_subset_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f30,f57])).

fof(f30,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f656,plain,(
    sK0 = sK1 ),
    inference(forward_demodulation,[],[f655,f414])).

fof(f414,plain,(
    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f410,f384])).

fof(f384,plain,(
    sK1 = k4_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f367,f370])).

fof(f370,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f363,f92])).

fof(f92,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f86,f61])).

fof(f86,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f48,f35])).

fof(f363,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f151,f353])).

fof(f353,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f349,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f349,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f348,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f348,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | r1_tarski(X3,X4) ) ),
    inference(subsumption_resolution,[],[f347,f32])).

fof(f347,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k1_xboole_0,k3_subset_1(X4,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | r1_tarski(X3,X4) ) ),
    inference(forward_demodulation,[],[f344,f107])).

fof(f344,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | ~ r1_tarski(k3_subset_1(X4,X4),k3_subset_1(X4,X3))
      | r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f50,f71])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f151,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f58,f64])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f40,f46,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f367,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f359,f92])).

fof(f359,plain,(
    k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f64,f353])).

fof(f410,plain,(
    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,k4_xboole_0(sK0,k5_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f65,f370])).

fof(f65,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f41,f56,f46])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f655,plain,(
    sK1 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f650,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f38,f55,f55])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f650,plain,(
    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0)) ),
    inference(backward_demodulation,[],[f381,f648])).

fof(f648,plain,(
    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f630,f370])).

fof(f630,plain,(
    sK0 = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f277,f414])).

fof(f277,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(superposition,[],[f66,f63])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f381,plain,(
    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) ),
    inference(backward_demodulation,[],[f269,f370])).

fof(f269,plain,(
    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f255,f177])).

fof(f177,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f58,f163])).

fof(f163,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f162,f92])).

fof(f162,plain,(
    k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f143,f111])).

fof(f143,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | sK0 = sK1 ),
    inference(superposition,[],[f64,f90])).

fof(f90,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f73,f85])).

fof(f85,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f48,f31])).

fof(f73,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f52,f68])).

fof(f68,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f60,f61])).

fof(f60,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f29,f57])).

fof(f29,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f255,plain,(
    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f65,f180])).

fof(f180,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f163,f177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 21:26:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (4981)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.47  % (4981)Refutation not found, incomplete strategy% (4981)------------------------------
% 0.21/0.47  % (4981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (4981)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (4981)Memory used [KB]: 10874
% 0.21/0.47  % (4981)Time elapsed: 0.059 s
% 0.21/0.47  % (4981)------------------------------
% 0.21/0.47  % (4981)------------------------------
% 0.21/0.50  % (4996)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (5003)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.21/0.50  % (4980)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (4983)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (4983)Refutation not found, incomplete strategy% (4983)------------------------------
% 0.21/0.51  % (4983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4983)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4983)Memory used [KB]: 10618
% 0.21/0.51  % (4983)Time elapsed: 0.099 s
% 0.21/0.51  % (4983)------------------------------
% 0.21/0.51  % (4983)------------------------------
% 0.21/0.52  % (4988)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (4988)Refutation not found, incomplete strategy% (4988)------------------------------
% 0.21/0.52  % (4988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4988)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4988)Memory used [KB]: 6268
% 0.21/0.52  % (4988)Time elapsed: 0.110 s
% 0.21/0.52  % (4988)------------------------------
% 0.21/0.52  % (4988)------------------------------
% 0.21/0.52  % (4991)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (4999)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (4997)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (5000)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (4977)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (5003)Refutation not found, incomplete strategy% (5003)------------------------------
% 0.21/0.52  % (5003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4979)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (5003)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4993)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (5003)Memory used [KB]: 6652
% 0.21/0.52  % (5003)Time elapsed: 0.024 s
% 0.21/0.52  % (5003)------------------------------
% 0.21/0.52  % (5003)------------------------------
% 0.21/0.53  % (4999)Refutation not found, incomplete strategy% (4999)------------------------------
% 0.21/0.53  % (4999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4999)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4999)Memory used [KB]: 10874
% 0.21/0.53  % (4999)Time elapsed: 0.119 s
% 0.21/0.53  % (4999)------------------------------
% 0.21/0.53  % (4999)------------------------------
% 0.21/0.53  % (4998)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (4974)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (4984)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (4989)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (4982)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (4985)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (4982)Refutation not found, incomplete strategy% (4982)------------------------------
% 0.21/0.53  % (4982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4982)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4982)Memory used [KB]: 10746
% 0.21/0.53  % (4982)Time elapsed: 0.119 s
% 0.21/0.53  % (4982)------------------------------
% 0.21/0.53  % (4982)------------------------------
% 0.21/0.53  % (4992)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (4973)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (5001)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (4990)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (4990)Refutation not found, incomplete strategy% (4990)------------------------------
% 0.21/0.54  % (4990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4990)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4990)Memory used [KB]: 10618
% 0.21/0.54  % (4990)Time elapsed: 0.136 s
% 0.21/0.54  % (4990)------------------------------
% 0.21/0.54  % (4990)------------------------------
% 0.21/0.54  % (4995)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (4995)Refutation not found, incomplete strategy% (4995)------------------------------
% 0.21/0.54  % (4995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4995)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4995)Memory used [KB]: 10746
% 0.21/0.54  % (4995)Time elapsed: 0.132 s
% 0.21/0.54  % (4995)------------------------------
% 0.21/0.54  % (4995)------------------------------
% 0.21/0.54  % (4975)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (4987)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (4977)Refutation not found, incomplete strategy% (4977)------------------------------
% 0.21/0.54  % (4977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4977)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4977)Memory used [KB]: 6396
% 0.21/0.54  % (4977)Time elapsed: 0.133 s
% 0.21/0.54  % (4977)------------------------------
% 0.21/0.54  % (4977)------------------------------
% 0.21/0.55  % (4975)Refutation not found, incomplete strategy% (4975)------------------------------
% 0.21/0.55  % (4975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4975)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4975)Memory used [KB]: 10874
% 0.21/0.55  % (4975)Time elapsed: 0.128 s
% 0.21/0.55  % (4975)------------------------------
% 0.21/0.55  % (4975)------------------------------
% 0.21/0.55  % (4978)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (4986)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (4994)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (4976)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (5002)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (4979)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f657,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f656,f111])).
% 0.21/0.57  fof(f111,plain,(
% 0.21/0.57    sK0 != sK1),
% 0.21/0.57    inference(subsumption_resolution,[],[f109,f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.57  fof(f109,plain,(
% 0.21/0.57    ~r1_tarski(k1_xboole_0,sK0) | sK0 != sK1),
% 0.21/0.57    inference(backward_demodulation,[],[f94,f108])).
% 0.21/0.57  fof(f108,plain,(
% 0.21/0.57    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 0.21/0.57    inference(backward_demodulation,[],[f87,f107])).
% 0.21/0.57  fof(f107,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f104,f61])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.57    inference(definition_unfolding,[],[f34,f57])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f37,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,axiom,(
% 0.21/0.57    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 0.21/0.57    inference(resolution,[],[f49,f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,axiom,(
% 0.21/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.57  fof(f87,plain,(
% 0.21/0.57    ( ! [X1] : (k4_xboole_0(X1,X1) = k3_subset_1(X1,X1)) )),
% 0.21/0.57    inference(resolution,[],[f48,f71])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f62,f61])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f36,f57])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,axiom,(
% 0.21/0.57    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.57  fof(f94,plain,(
% 0.21/0.57    sK0 != sK1 | ~r1_tarski(k4_xboole_0(sK0,sK0),sK0)),
% 0.21/0.57    inference(backward_demodulation,[],[f70,f87])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | sK0 != sK1),
% 0.21/0.57    inference(inner_rewriting,[],[f69])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.57    inference(backward_demodulation,[],[f59,f61])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    sK1 != k3_subset_1(sK0,k1_xboole_0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.57    inference(definition_unfolding,[],[f30,f57])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.21/0.57    inference(negated_conjecture,[],[f22])).
% 0.21/0.57  fof(f22,conjecture,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 0.21/0.57  fof(f656,plain,(
% 0.21/0.57    sK0 = sK1),
% 0.21/0.57    inference(forward_demodulation,[],[f655,f414])).
% 0.21/0.57  fof(f414,plain,(
% 0.21/0.57    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.21/0.57    inference(forward_demodulation,[],[f410,f384])).
% 0.21/0.57  fof(f384,plain,(
% 0.21/0.57    sK1 = k4_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 0.21/0.57    inference(backward_demodulation,[],[f367,f370])).
% 0.21/0.57  fof(f370,plain,(
% 0.21/0.57    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 0.21/0.57    inference(forward_demodulation,[],[f363,f92])).
% 0.21/0.57  fof(f92,plain,(
% 0.21/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.57    inference(forward_demodulation,[],[f86,f61])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(resolution,[],[f48,f35])).
% 0.21/0.57  fof(f363,plain,(
% 0.21/0.57    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,k1_xboole_0))),
% 0.21/0.57    inference(superposition,[],[f151,f353])).
% 0.21/0.57  fof(f353,plain,(
% 0.21/0.57    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.21/0.57    inference(resolution,[],[f349,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.57  fof(f349,plain,(
% 0.21/0.57    r1_tarski(sK1,sK0)),
% 0.21/0.57    inference(resolution,[],[f348,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f348,plain,(
% 0.21/0.57    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X4)) | r1_tarski(X3,X4)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f347,f32])).
% 0.21/0.57  fof(f347,plain,(
% 0.21/0.57    ( ! [X4,X3] : (~r1_tarski(k1_xboole_0,k3_subset_1(X4,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(X4)) | r1_tarski(X3,X4)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f344,f107])).
% 0.21/0.57  fof(f344,plain,(
% 0.21/0.57    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X4)) | ~r1_tarski(k3_subset_1(X4,X4),k3_subset_1(X4,X3)) | r1_tarski(X3,X4)) )),
% 0.21/0.57    inference(resolution,[],[f50,f71])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f20])).
% 0.21/0.58  fof(f20,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 0.21/0.58  fof(f151,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.21/0.58    inference(superposition,[],[f58,f64])).
% 0.21/0.58  fof(f64,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f40,f46,f46])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f45,f46])).
% 0.21/0.58  fof(f45,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.58  fof(f367,plain,(
% 0.21/0.58    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.58    inference(forward_demodulation,[],[f359,f92])).
% 0.21/0.58  fof(f359,plain,(
% 0.21/0.58    k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.58    inference(superposition,[],[f64,f353])).
% 0.21/0.58  fof(f410,plain,(
% 0.21/0.58    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,k4_xboole_0(sK0,k5_xboole_0(sK0,sK1))))),
% 0.21/0.58    inference(superposition,[],[f65,f370])).
% 0.21/0.58  fof(f65,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f41,f56,f46])).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f42,f55])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f43,f54])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.58  fof(f655,plain,(
% 0.21/0.58    sK1 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.21/0.58    inference(forward_demodulation,[],[f650,f63])).
% 0.21/0.58  fof(f63,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f38,f55,f55])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.58  fof(f650,plain,(
% 0.21/0.58    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0))),
% 0.21/0.58    inference(backward_demodulation,[],[f381,f648])).
% 0.21/0.58  fof(f648,plain,(
% 0.21/0.58    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 0.21/0.58    inference(forward_demodulation,[],[f630,f370])).
% 0.21/0.58  fof(f630,plain,(
% 0.21/0.58    sK0 = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 0.21/0.58    inference(superposition,[],[f277,f414])).
% 0.21/0.58  fof(f277,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_enumset1(X1,X1,X1,X0))) )),
% 0.21/0.58    inference(superposition,[],[f66,f63])).
% 0.21/0.58  fof(f66,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f44,f56])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.58  fof(f381,plain,(
% 0.21/0.58    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))))),
% 0.21/0.58    inference(backward_demodulation,[],[f269,f370])).
% 0.21/0.58  fof(f269,plain,(
% 0.21/0.58    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))))),
% 0.21/0.58    inference(forward_demodulation,[],[f255,f177])).
% 0.21/0.58  fof(f177,plain,(
% 0.21/0.58    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 0.21/0.58    inference(superposition,[],[f58,f163])).
% 0.21/0.58  fof(f163,plain,(
% 0.21/0.58    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 0.21/0.58    inference(forward_demodulation,[],[f162,f92])).
% 0.21/0.58  fof(f162,plain,(
% 0.21/0.58    k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 0.21/0.58    inference(subsumption_resolution,[],[f143,f111])).
% 0.21/0.58  fof(f143,plain,(
% 0.21/0.58    k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | sK0 = sK1),
% 0.21/0.58    inference(superposition,[],[f64,f90])).
% 0.21/0.58  fof(f90,plain,(
% 0.21/0.58    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) | sK0 = sK1),
% 0.21/0.58    inference(backward_demodulation,[],[f73,f85])).
% 0.21/0.58  fof(f85,plain,(
% 0.21/0.58    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.21/0.58    inference(resolution,[],[f48,f31])).
% 0.21/0.58  fof(f73,plain,(
% 0.21/0.58    k1_xboole_0 = k4_xboole_0(k3_subset_1(sK0,sK1),sK1) | sK0 = sK1),
% 0.21/0.58    inference(resolution,[],[f52,f68])).
% 0.21/0.58  fof(f68,plain,(
% 0.21/0.58    r1_tarski(k3_subset_1(sK0,sK1),sK1) | sK0 = sK1),
% 0.21/0.58    inference(backward_demodulation,[],[f60,f61])).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    sK1 = k3_subset_1(sK0,k1_xboole_0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.58    inference(definition_unfolding,[],[f29,f57])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f24])).
% 0.21/0.58  fof(f255,plain,(
% 0.21/0.58    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))))),
% 0.21/0.58    inference(superposition,[],[f65,f180])).
% 0.21/0.58  fof(f180,plain,(
% 0.21/0.58    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 0.21/0.58    inference(backward_demodulation,[],[f163,f177])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (4979)------------------------------
% 0.21/0.58  % (4979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (4979)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (4979)Memory used [KB]: 6524
% 0.21/0.58  % (4979)Time elapsed: 0.152 s
% 0.21/0.58  % (4979)------------------------------
% 0.21/0.58  % (4979)------------------------------
% 0.21/0.58  % (4972)Success in time 0.206 s
%------------------------------------------------------------------------------
