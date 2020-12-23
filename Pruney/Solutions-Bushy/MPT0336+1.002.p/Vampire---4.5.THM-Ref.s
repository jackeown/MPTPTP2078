%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0336+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 149 expanded)
%              Number of leaves         :   10 (  38 expanded)
%              Depth                    :   16
%              Number of atoms          :   79 ( 291 expanded)
%              Number of equality atoms :   36 (  91 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f608,plain,(
    $false ),
    inference(subsumption_resolution,[],[f607,f223])).

fof(f223,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f212,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f212,plain,(
    k1_xboole_0 != k3_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f52,f156])).

fof(f156,plain,(
    ! [X14] : k3_xboole_0(sK1,X14) = k3_xboole_0(sK1,k2_xboole_0(X14,sK2)) ),
    inference(forward_demodulation,[],[f134,f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f134,plain,(
    ! [X14] : k3_xboole_0(sK1,k2_xboole_0(X14,sK2)) = k2_xboole_0(k3_xboole_0(sK1,X14),k1_xboole_0) ),
    inference(superposition,[],[f34,f70])).

fof(f70,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f55,f27])).

fof(f55,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f31,f22])).

fof(f22,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f52,plain,(
    k1_xboole_0 != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f30,f35])).

fof(f35,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f29,f23])).

fof(f23,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f607,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f606,f378])).

fof(f378,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f374,f70])).

fof(f374,plain,(
    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k1_tarski(sK3)) ),
    inference(superposition,[],[f156,f370])).

fof(f370,plain,(
    sK2 = k2_xboole_0(k1_tarski(sK3),sK2) ),
    inference(resolution,[],[f46,f21])).

fof(f21,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(resolution,[],[f28,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f606,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK1,k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f596,f468])).

fof(f468,plain,(
    ! [X2,X1] : k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f58,f27])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f33,f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f596,plain,(
    k3_xboole_0(sK1,k1_tarski(sK3)) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f390,f45])).

fof(f45,plain,(
    k1_tarski(sK3) = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(resolution,[],[f28,f20])).

fof(f20,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f390,plain,(
    ! [X0] : k3_xboole_0(sK1,X0) = k3_xboole_0(sK1,k2_xboole_0(X0,k1_tarski(sK3))) ),
    inference(forward_demodulation,[],[f385,f24])).

fof(f385,plain,(
    ! [X0] : k2_xboole_0(k3_xboole_0(sK1,X0),k1_xboole_0) = k3_xboole_0(sK1,k2_xboole_0(X0,k1_tarski(sK3))) ),
    inference(superposition,[],[f34,f378])).

%------------------------------------------------------------------------------
