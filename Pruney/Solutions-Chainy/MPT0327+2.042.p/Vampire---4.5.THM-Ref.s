%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:54 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   80 (1870 expanded)
%              Number of leaves         :   14 ( 568 expanded)
%              Depth                    :   26
%              Number of atoms          :   92 (2507 expanded)
%              Number of equality atoms :   74 (1504 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f228])).

fof(f228,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f222,f36])).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f222,plain,(
    sK1 != k5_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f162,f219])).

fof(f219,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f218,f76])).

fof(f76,plain,(
    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f71,f65])).

fof(f65,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f60,f61])).

fof(f61,plain,(
    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f56,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f56,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f22,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f22,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f60,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f56,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f33,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f71,plain,(
    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)) ),
    inference(superposition,[],[f46,f61])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f218,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f217,f65])).

fof(f217,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f210,f150])).

fof(f150,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f145,f46])).

fof(f145,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f143,f85])).

fof(f85,plain,(
    ! [X0] : k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f35,f76])).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f143,plain,(
    ! [X0] : k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f85,f139])).

fof(f139,plain,(
    ! [X0] : k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,X0)) ),
    inference(backward_demodulation,[],[f130,f138])).

fof(f138,plain,(
    ! [X0] : k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) ),
    inference(superposition,[],[f35,f134])).

fof(f134,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f129,f36])).

fof(f129,plain,(
    k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(superposition,[],[f85,f76])).

fof(f130,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f85,f85])).

fof(f210,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f85,f193])).

fof(f193,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k4_xboole_0(k1_xboole_0,X4)) ),
    inference(superposition,[],[f46,f169])).

fof(f169,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f156,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f34,f28,f28])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f156,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f150,f46])).

fof(f162,plain,(
    sK1 != k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f121,f156])).

fof(f121,plain,(
    sK1 != k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(forward_demodulation,[],[f120,f36])).

fof(f120,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(forward_demodulation,[],[f119,f76])).

fof(f119,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(backward_demodulation,[],[f81,f118])).

fof(f118,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0) ),
    inference(superposition,[],[f35,f115])).

fof(f115,plain,(
    k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f46,f72])).

fof(f72,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f68,f65])).

fof(f68,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(superposition,[],[f52,f61])).

fof(f81,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(backward_demodulation,[],[f75,f77])).

fof(f77,plain,(
    k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f52,f65])).

fof(f75,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f55,f74])).

fof(f74,plain,(
    ! [X0] : k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK1,X0))) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0) ),
    inference(forward_demodulation,[],[f70,f65])).

fof(f70,plain,(
    ! [X0] : k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0),X0) ),
    inference(superposition,[],[f48,f61])).

fof(f48,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f25,f28,f28])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f55,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) ),
    inference(forward_demodulation,[],[f47,f52])).

fof(f47,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f23,f43,f45,f45])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f28])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f23,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:01:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (29831)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.50  % (29824)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (29831)Refutation not found, incomplete strategy% (29831)------------------------------
% 0.22/0.51  % (29831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (29825)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (29831)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (29831)Memory used [KB]: 10746
% 0.22/0.51  % (29831)Time elapsed: 0.095 s
% 0.22/0.51  % (29831)------------------------------
% 0.22/0.51  % (29831)------------------------------
% 0.22/0.51  % (29836)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.51  % (29839)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (29827)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (29839)Refutation not found, incomplete strategy% (29839)------------------------------
% 0.22/0.52  % (29839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (29839)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (29839)Memory used [KB]: 1663
% 0.22/0.52  % (29839)Time elapsed: 0.110 s
% 0.22/0.52  % (29839)------------------------------
% 0.22/0.52  % (29839)------------------------------
% 0.22/0.52  % (29843)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (29835)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (29826)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (29832)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (29842)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (29850)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (29822)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (29820)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.30/0.53  % (29850)Refutation not found, incomplete strategy% (29850)------------------------------
% 1.30/0.53  % (29850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (29850)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (29850)Memory used [KB]: 1663
% 1.30/0.53  % (29850)Time elapsed: 0.135 s
% 1.30/0.53  % (29850)------------------------------
% 1.30/0.53  % (29850)------------------------------
% 1.30/0.53  % (29844)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.30/0.54  % (29834)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.30/0.54  % (29840)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.30/0.54  % (29849)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.30/0.54  % (29849)Refutation not found, incomplete strategy% (29849)------------------------------
% 1.30/0.54  % (29849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (29849)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (29849)Memory used [KB]: 10746
% 1.30/0.54  % (29849)Time elapsed: 0.139 s
% 1.30/0.54  % (29849)------------------------------
% 1.30/0.54  % (29849)------------------------------
% 1.30/0.54  % (29846)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.30/0.55  % (29838)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.30/0.55  % (29848)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.30/0.55  % (29829)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.30/0.55  % (29848)Refutation not found, incomplete strategy% (29848)------------------------------
% 1.30/0.55  % (29848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (29848)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (29848)Memory used [KB]: 6140
% 1.30/0.55  % (29848)Time elapsed: 0.137 s
% 1.30/0.55  % (29848)------------------------------
% 1.30/0.55  % (29848)------------------------------
% 1.50/0.55  % (29841)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.50/0.55  % (29828)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.50/0.56  % (29833)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.50/0.56  % (29823)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.50/0.57  % (29846)Refutation found. Thanks to Tanya!
% 1.50/0.57  % SZS status Theorem for theBenchmark
% 1.50/0.57  % SZS output start Proof for theBenchmark
% 1.50/0.57  fof(f229,plain,(
% 1.50/0.57    $false),
% 1.50/0.57    inference(trivial_inequality_removal,[],[f228])).
% 1.50/0.57  fof(f228,plain,(
% 1.50/0.57    sK1 != sK1),
% 1.50/0.57    inference(superposition,[],[f222,f36])).
% 1.50/0.57  fof(f36,plain,(
% 1.50/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.50/0.57    inference(cnf_transformation,[],[f9])).
% 1.50/0.57  fof(f9,axiom,(
% 1.50/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.50/0.57  fof(f222,plain,(
% 1.50/0.57    sK1 != k5_xboole_0(sK1,k1_xboole_0)),
% 1.50/0.57    inference(backward_demodulation,[],[f162,f219])).
% 1.50/0.57  fof(f219,plain,(
% 1.50/0.57    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.50/0.57    inference(forward_demodulation,[],[f218,f76])).
% 1.50/0.57  fof(f76,plain,(
% 1.50/0.57    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.50/0.57    inference(forward_demodulation,[],[f71,f65])).
% 1.50/0.57  fof(f65,plain,(
% 1.50/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.50/0.57    inference(forward_demodulation,[],[f60,f61])).
% 1.50/0.57  fof(f61,plain,(
% 1.50/0.57    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f56,f26])).
% 1.50/0.57  fof(f26,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.50/0.57    inference(cnf_transformation,[],[f3])).
% 1.50/0.57  fof(f3,axiom,(
% 1.50/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.50/0.57  fof(f56,plain,(
% 1.50/0.57    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f22,f50])).
% 1.50/0.57  fof(f50,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f30,f45])).
% 1.50/0.57  fof(f45,plain,(
% 1.50/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f32,f44])).
% 1.50/0.57  fof(f44,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f41,f42])).
% 1.50/0.57  fof(f42,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f14])).
% 1.50/0.57  fof(f14,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.50/0.57  fof(f41,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f13])).
% 1.50/0.57  fof(f13,axiom,(
% 1.50/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.50/0.57  fof(f32,plain,(
% 1.50/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f12])).
% 1.50/0.57  fof(f12,axiom,(
% 1.50/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.50/0.57  fof(f30,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f16])).
% 1.50/0.57  fof(f16,axiom,(
% 1.50/0.57    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.50/0.57  fof(f22,plain,(
% 1.50/0.57    r2_hidden(sK0,sK1)),
% 1.50/0.57    inference(cnf_transformation,[],[f20])).
% 1.50/0.57  fof(f20,plain,(
% 1.50/0.57    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 1.50/0.57    inference(ennf_transformation,[],[f19])).
% 1.50/0.57  fof(f19,negated_conjecture,(
% 1.50/0.57    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.50/0.57    inference(negated_conjecture,[],[f18])).
% 1.50/0.57  fof(f18,conjecture,(
% 1.50/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 1.50/0.57  fof(f60,plain,(
% 1.50/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f56,f51])).
% 1.50/0.57  fof(f51,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.50/0.57    inference(definition_unfolding,[],[f33,f28])).
% 1.50/0.57  fof(f28,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f7])).
% 1.50/0.57  fof(f7,axiom,(
% 1.50/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.50/0.57  fof(f33,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.50/0.57    inference(cnf_transformation,[],[f21])).
% 1.50/0.57  fof(f21,plain,(
% 1.50/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.50/0.57    inference(ennf_transformation,[],[f5])).
% 1.50/0.57  fof(f5,axiom,(
% 1.50/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.50/0.57  fof(f71,plain,(
% 1.50/0.57    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0))),
% 1.50/0.57    inference(superposition,[],[f46,f61])).
% 1.50/0.57  fof(f46,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.50/0.57    inference(definition_unfolding,[],[f29,f28])).
% 1.50/0.57  fof(f29,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f4])).
% 1.50/0.57  fof(f4,axiom,(
% 1.50/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.50/0.57  fof(f218,plain,(
% 1.50/0.57    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.50/0.57    inference(forward_demodulation,[],[f217,f65])).
% 1.50/0.57  fof(f217,plain,(
% 1.50/0.57    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.50/0.57    inference(forward_demodulation,[],[f210,f150])).
% 1.50/0.57  fof(f150,plain,(
% 1.50/0.57    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )),
% 1.50/0.57    inference(superposition,[],[f145,f46])).
% 1.50/0.57  fof(f145,plain,(
% 1.50/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 1.50/0.57    inference(forward_demodulation,[],[f143,f85])).
% 1.50/0.57  fof(f85,plain,(
% 1.50/0.57    ( ! [X0] : (k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.50/0.57    inference(superposition,[],[f35,f76])).
% 1.50/0.57  fof(f35,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f10])).
% 1.50/0.57  fof(f10,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.50/0.57  fof(f143,plain,(
% 1.50/0.57    ( ! [X0] : (k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 1.50/0.57    inference(superposition,[],[f85,f139])).
% 1.50/0.57  fof(f139,plain,(
% 1.50/0.57    ( ! [X0] : (k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,X0))) )),
% 1.50/0.57    inference(backward_demodulation,[],[f130,f138])).
% 1.50/0.57  fof(f138,plain,(
% 1.50/0.57    ( ! [X0] : (k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0))) )),
% 1.50/0.57    inference(superposition,[],[f35,f134])).
% 1.50/0.57  fof(f134,plain,(
% 1.50/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.50/0.57    inference(forward_demodulation,[],[f129,f36])).
% 1.50/0.57  fof(f129,plain,(
% 1.50/0.57    k5_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.50/0.57    inference(superposition,[],[f85,f76])).
% 1.50/0.57  fof(f130,plain,(
% 1.50/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,X0))) )),
% 1.50/0.57    inference(superposition,[],[f85,f85])).
% 1.50/0.57  fof(f210,plain,(
% 1.50/0.57    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.50/0.57    inference(superposition,[],[f85,f193])).
% 1.50/0.57  fof(f193,plain,(
% 1.50/0.57    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k4_xboole_0(k1_xboole_0,X4))) )),
% 1.50/0.57    inference(superposition,[],[f46,f169])).
% 1.50/0.57  fof(f169,plain,(
% 1.50/0.57    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 1.50/0.57    inference(superposition,[],[f156,f52])).
% 1.50/0.57  fof(f52,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.50/0.57    inference(definition_unfolding,[],[f34,f28,f28])).
% 1.50/0.57  fof(f34,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f1])).
% 1.50/0.57  fof(f1,axiom,(
% 1.50/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.50/0.57  fof(f156,plain,(
% 1.50/0.57    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )),
% 1.50/0.57    inference(superposition,[],[f150,f46])).
% 1.50/0.57  fof(f162,plain,(
% 1.50/0.57    sK1 != k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.50/0.57    inference(backward_demodulation,[],[f121,f156])).
% 1.50/0.57  fof(f121,plain,(
% 1.50/0.57    sK1 != k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 1.50/0.57    inference(forward_demodulation,[],[f120,f36])).
% 1.50/0.57  fof(f120,plain,(
% 1.50/0.57    sK1 != k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 1.50/0.57    inference(forward_demodulation,[],[f119,f76])).
% 1.50/0.57  fof(f119,plain,(
% 1.50/0.57    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 1.50/0.57    inference(backward_demodulation,[],[f81,f118])).
% 1.50/0.57  fof(f118,plain,(
% 1.50/0.57    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)) )),
% 1.50/0.57    inference(superposition,[],[f35,f115])).
% 1.50/0.57  fof(f115,plain,(
% 1.50/0.57    k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.50/0.57    inference(superposition,[],[f46,f72])).
% 1.50/0.57  fof(f72,plain,(
% 1.50/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.50/0.57    inference(forward_demodulation,[],[f68,f65])).
% 1.50/0.57  fof(f68,plain,(
% 1.50/0.57    k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.50/0.57    inference(superposition,[],[f52,f61])).
% 1.50/0.57  fof(f81,plain,(
% 1.50/0.57    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 1.50/0.57    inference(backward_demodulation,[],[f75,f77])).
% 1.50/0.57  fof(f77,plain,(
% 1.50/0.57    k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.50/0.57    inference(superposition,[],[f52,f65])).
% 1.50/0.57  fof(f75,plain,(
% 1.50/0.57    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.50/0.57    inference(backward_demodulation,[],[f55,f74])).
% 1.50/0.57  fof(f74,plain,(
% 1.50/0.57    ( ! [X0] : (k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK1,X0))) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)) )),
% 1.50/0.57    inference(forward_demodulation,[],[f70,f65])).
% 1.50/0.57  fof(f70,plain,(
% 1.50/0.57    ( ! [X0] : (k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0),X0)) )),
% 1.50/0.57    inference(superposition,[],[f48,f61])).
% 1.50/0.57  fof(f48,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f25,f28,f28])).
% 1.50/0.57  fof(f25,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f8])).
% 1.50/0.57  fof(f8,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.50/0.57  fof(f55,plain,(
% 1.50/0.57    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))),
% 1.50/0.57    inference(forward_demodulation,[],[f47,f52])).
% 1.50/0.57  fof(f47,plain,(
% 1.50/0.57    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))))),
% 1.50/0.57    inference(definition_unfolding,[],[f23,f43,f45,f45])).
% 1.50/0.57  fof(f43,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.50/0.57    inference(definition_unfolding,[],[f24,f28])).
% 1.50/0.57  fof(f24,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f11])).
% 1.50/0.57  fof(f11,axiom,(
% 1.50/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.50/0.57  fof(f23,plain,(
% 1.50/0.57    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.50/0.57    inference(cnf_transformation,[],[f20])).
% 1.50/0.57  % SZS output end Proof for theBenchmark
% 1.50/0.57  % (29846)------------------------------
% 1.50/0.57  % (29846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (29846)Termination reason: Refutation
% 1.50/0.57  
% 1.50/0.57  % (29846)Memory used [KB]: 6396
% 1.50/0.57  % (29846)Time elapsed: 0.143 s
% 1.50/0.57  % (29846)------------------------------
% 1.50/0.57  % (29846)------------------------------
% 1.50/0.57  % (29817)Success in time 0.204 s
%------------------------------------------------------------------------------
