%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:58 EST 2020

% Result     : Theorem 6.59s
% Output     : Refutation 6.59s
% Verified   : 
% Statistics : Number of formulae       :  105 (1180 expanded)
%              Number of leaves         :   25 ( 404 expanded)
%              Depth                    :   21
%              Number of atoms          :  120 (1208 expanded)
%              Number of equality atoms :   78 (1136 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3426,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3423,f33])).

fof(f33,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f3423,plain,(
    r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f3422,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f51,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f3422,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f3421,f119])).

fof(f119,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f106,f93])).

fof(f93,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f92,f78])).

fof(f78,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f68])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f92,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(forward_demodulation,[],[f77,f91])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f90,f76])).

fof(f76,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f36,f69])).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f75,f35])).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f34,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f69])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f77,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f38,f70])).

fof(f38,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f106,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f50,f91])).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f3421,plain,(
    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(forward_demodulation,[],[f3415,f113])).

fof(f113,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f50,f42])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f3415,plain,(
    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(superposition,[],[f94,f3242])).

fof(f3242,plain,(
    sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(forward_demodulation,[],[f3241,f3234])).

fof(f3234,plain,(
    ! [X41,X42,X40] : k6_enumset1(X40,X40,X40,X40,X40,X40,X41,X42) = k6_enumset1(X40,X40,X40,X40,X40,X41,X42,X40) ),
    inference(subsumption_resolution,[],[f3229,f2298])).

fof(f2298,plain,(
    ! [X30,X28,X26,X29,X27,X25] : r1_tarski(k6_enumset1(X25,X25,X25,X25,X26,X27,X28,X29),k6_enumset1(X25,X25,X25,X26,X27,X28,X29,X30)) ),
    inference(superposition,[],[f314,f309])).

fof(f309,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X5,X5,X6) ),
    inference(superposition,[],[f85,f73])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f60,f69,f65,f67])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f59,f58,f69,f65,f68])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(f314,plain,(
    ! [X21,X19,X17,X22,X20,X18,X16] : r1_tarski(k6_enumset1(X16,X16,X16,X16,X17,X18,X19,X20),k6_enumset1(X16,X16,X17,X18,X19,X20,X21,X22)) ),
    inference(superposition,[],[f79,f85])).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f40,f69])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f3229,plain,(
    ! [X41,X42,X40] :
      ( ~ r1_tarski(k6_enumset1(X40,X40,X40,X40,X40,X40,X41,X42),k6_enumset1(X40,X40,X40,X40,X40,X41,X42,X40))
      | k6_enumset1(X40,X40,X40,X40,X40,X40,X41,X42) = k6_enumset1(X40,X40,X40,X40,X40,X41,X42,X40) ) ),
    inference(superposition,[],[f155,f506])).

fof(f506,plain,(
    ! [X33,X34,X32] : k6_enumset1(X32,X32,X32,X32,X32,X32,X33,X34) = k3_tarski(k6_enumset1(k6_enumset1(X32,X32,X32,X32,X32,X33,X34,X32),k6_enumset1(X32,X32,X32,X32,X32,X33,X34,X32),k6_enumset1(X32,X32,X32,X32,X32,X33,X34,X32),k6_enumset1(X32,X32,X32,X32,X32,X33,X34,X32),k6_enumset1(X32,X32,X32,X32,X32,X33,X34,X32),k6_enumset1(X32,X32,X32,X32,X32,X33,X34,X32),k6_enumset1(X32,X32,X32,X32,X32,X33,X34,X32),k6_enumset1(X33,X33,X33,X33,X33,X33,X33,X34))) ),
    inference(superposition,[],[f86,f78])).

fof(f86,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))) ),
    inference(definition_unfolding,[],[f62,f71,f69,f58,f68])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f61,f69,f64,f67])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ) ),
    inference(resolution,[],[f79,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3241,plain,(
    sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f3240,f79])).

fof(f3240,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(forward_demodulation,[],[f2909,f3234])).

fof(f2909,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)))
    | sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(resolution,[],[f2901,f48])).

fof(f2901,plain,(
    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(forward_demodulation,[],[f2898,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f54,f66,f66])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(f2898,plain,(
    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,sK2)),sK2) ),
    inference(backward_demodulation,[],[f316,f2872])).

fof(f2872,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X6) = k6_enumset1(X0,X1,X2,X3,X4,X6,X5,X5) ),
    inference(superposition,[],[f295,f73])).

fof(f295,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X3,X4,X5,X6,X7,X0,X1,X2) = k3_tarski(k6_enumset1(k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X2,X2,X2,X2,X2,X1,X0,X0))) ),
    inference(superposition,[],[f73,f84])).

fof(f316,plain,(
    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(backward_demodulation,[],[f95,f309])).

fof(f95,plain,(
    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(backward_demodulation,[],[f74,f84])).

fof(f74,plain,(
    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f32,f69,f68])).

fof(f32,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f94,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(backward_demodulation,[],[f80,f50])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f41,f70])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.35  % CPULimit   : 60
% 0.19/0.35  % WCLimit    : 600
% 0.19/0.35  % DateTime   : Tue Dec  1 15:03:07 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.22/0.50  % (22360)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.51  % (22337)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (22360)Refutation not found, incomplete strategy% (22360)------------------------------
% 0.22/0.51  % (22360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22360)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22360)Memory used [KB]: 10874
% 0.22/0.52  % (22360)Time elapsed: 0.102 s
% 0.22/0.52  % (22360)------------------------------
% 0.22/0.52  % (22360)------------------------------
% 0.22/0.53  % (22347)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (22348)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.53  % (22340)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (22361)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (22341)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (22339)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (22333)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (22333)Refutation not found, incomplete strategy% (22333)------------------------------
% 0.22/0.54  % (22333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22336)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (22361)Refutation not found, incomplete strategy% (22361)------------------------------
% 0.22/0.54  % (22361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22361)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (22361)Memory used [KB]: 1663
% 0.22/0.54  % (22361)Time elapsed: 0.126 s
% 0.22/0.54  % (22361)------------------------------
% 0.22/0.54  % (22361)------------------------------
% 0.22/0.54  % (22346)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (22357)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (22355)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (22357)Refutation not found, incomplete strategy% (22357)------------------------------
% 0.22/0.54  % (22357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22357)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (22357)Memory used [KB]: 6268
% 0.22/0.54  % (22357)Time elapsed: 0.122 s
% 0.22/0.54  % (22357)------------------------------
% 0.22/0.54  % (22357)------------------------------
% 0.22/0.54  % (22338)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (22352)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (22334)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (22335)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (22356)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (22359)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (22348)Refutation not found, incomplete strategy% (22348)------------------------------
% 0.22/0.55  % (22348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22332)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (22343)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (22345)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (22333)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (22333)Memory used [KB]: 1663
% 0.22/0.55  % (22333)Time elapsed: 0.124 s
% 0.22/0.55  % (22333)------------------------------
% 0.22/0.55  % (22333)------------------------------
% 0.22/0.55  % (22354)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (22349)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (22350)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (22346)Refutation not found, incomplete strategy% (22346)------------------------------
% 0.22/0.55  % (22346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22358)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (22342)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (22351)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (22349)Refutation not found, incomplete strategy% (22349)------------------------------
% 0.22/0.55  % (22349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22349)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (22349)Memory used [KB]: 1918
% 0.22/0.55  % (22349)Time elapsed: 0.135 s
% 0.22/0.55  % (22349)------------------------------
% 0.22/0.55  % (22349)------------------------------
% 0.22/0.55  % (22353)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.56  % (22343)Refutation not found, incomplete strategy% (22343)------------------------------
% 0.22/0.56  % (22343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22343)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (22343)Memory used [KB]: 6396
% 0.22/0.56  % (22343)Time elapsed: 0.113 s
% 0.22/0.56  % (22343)------------------------------
% 0.22/0.56  % (22343)------------------------------
% 0.22/0.56  % (22342)Refutation not found, incomplete strategy% (22342)------------------------------
% 0.22/0.56  % (22342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22342)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (22342)Memory used [KB]: 10874
% 0.22/0.56  % (22342)Time elapsed: 0.149 s
% 0.22/0.56  % (22342)------------------------------
% 0.22/0.56  % (22342)------------------------------
% 0.22/0.56  % (22348)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (22348)Memory used [KB]: 10618
% 0.22/0.56  % (22348)Time elapsed: 0.136 s
% 0.22/0.56  % (22348)------------------------------
% 0.22/0.56  % (22348)------------------------------
% 1.47/0.56  % (22358)Refutation not found, incomplete strategy% (22358)------------------------------
% 1.47/0.56  % (22358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (22358)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (22358)Memory used [KB]: 6268
% 1.47/0.56  % (22358)Time elapsed: 0.149 s
% 1.47/0.56  % (22358)------------------------------
% 1.47/0.56  % (22358)------------------------------
% 1.47/0.56  % (22359)Refutation not found, incomplete strategy% (22359)------------------------------
% 1.47/0.56  % (22359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (22359)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (22359)Memory used [KB]: 6268
% 1.47/0.56  % (22359)Time elapsed: 0.113 s
% 1.47/0.56  % (22359)------------------------------
% 1.47/0.56  % (22359)------------------------------
% 1.47/0.56  % (22350)Refutation not found, incomplete strategy% (22350)------------------------------
% 1.47/0.56  % (22350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (22350)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (22350)Memory used [KB]: 1791
% 1.47/0.56  % (22350)Time elapsed: 0.146 s
% 1.47/0.56  % (22350)------------------------------
% 1.47/0.56  % (22350)------------------------------
% 1.47/0.56  % (22344)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.47/0.56  % (22344)Refutation not found, incomplete strategy% (22344)------------------------------
% 1.47/0.56  % (22344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (22344)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (22344)Memory used [KB]: 10618
% 1.47/0.56  % (22344)Time elapsed: 0.153 s
% 1.47/0.56  % (22344)------------------------------
% 1.47/0.56  % (22344)------------------------------
% 1.47/0.56  % (22346)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (22346)Memory used [KB]: 1663
% 1.47/0.56  % (22346)Time elapsed: 0.139 s
% 1.47/0.56  % (22346)------------------------------
% 1.47/0.56  % (22346)------------------------------
% 1.47/0.56  % (22356)Refutation not found, incomplete strategy% (22356)------------------------------
% 1.47/0.56  % (22356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (22356)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (22356)Memory used [KB]: 10746
% 1.47/0.56  % (22356)Time elapsed: 0.150 s
% 1.47/0.56  % (22356)------------------------------
% 1.47/0.56  % (22356)------------------------------
% 1.90/0.63  % (22375)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.00/0.65  % (22385)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.00/0.67  % (22391)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.00/0.67  % (22405)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.00/0.67  % (22334)Refutation not found, incomplete strategy% (22334)------------------------------
% 2.00/0.67  % (22334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.67  % (22340)Refutation not found, incomplete strategy% (22340)------------------------------
% 2.00/0.67  % (22340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.67  % (22340)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.67  
% 2.00/0.67  % (22340)Memory used [KB]: 6268
% 2.00/0.67  % (22340)Time elapsed: 0.242 s
% 2.00/0.67  % (22340)------------------------------
% 2.00/0.67  % (22340)------------------------------
% 2.00/0.68  % (22398)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.00/0.68  % (22334)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.68  
% 2.00/0.68  % (22334)Memory used [KB]: 6396
% 2.00/0.68  % (22334)Time elapsed: 0.254 s
% 2.00/0.68  % (22334)------------------------------
% 2.00/0.68  % (22334)------------------------------
% 2.00/0.68  % (22401)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.00/0.68  % (22398)Refutation not found, incomplete strategy% (22398)------------------------------
% 2.00/0.68  % (22398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.68  % (22398)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.68  
% 2.00/0.68  % (22398)Memory used [KB]: 10746
% 2.00/0.68  % (22398)Time elapsed: 0.106 s
% 2.00/0.68  % (22398)------------------------------
% 2.00/0.68  % (22398)------------------------------
% 2.00/0.68  % (22332)Refutation not found, incomplete strategy% (22332)------------------------------
% 2.00/0.68  % (22332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.68  % (22399)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.00/0.68  % (22393)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.00/0.68  % (22391)Refutation not found, incomplete strategy% (22391)------------------------------
% 2.00/0.68  % (22391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.68  % (22391)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.68  
% 2.00/0.68  % (22391)Memory used [KB]: 6268
% 2.00/0.68  % (22391)Time elapsed: 0.109 s
% 2.00/0.68  % (22391)------------------------------
% 2.00/0.68  % (22391)------------------------------
% 2.00/0.68  % (22394)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.00/0.69  % (22410)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.00/0.69  % (22402)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.00/0.69  % (22335)Refutation not found, incomplete strategy% (22335)------------------------------
% 2.00/0.69  % (22335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.69  % (22335)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.69  
% 2.00/0.69  % (22335)Memory used [KB]: 6140
% 2.00/0.69  % (22335)Time elapsed: 0.249 s
% 2.00/0.69  % (22335)------------------------------
% 2.00/0.69  % (22335)------------------------------
% 2.00/0.69  % (22347)Refutation not found, incomplete strategy% (22347)------------------------------
% 2.00/0.69  % (22347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.69  % (22393)Refutation not found, incomplete strategy% (22393)------------------------------
% 2.00/0.69  % (22393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.69  % (22347)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.69  
% 2.00/0.69  % (22347)Memory used [KB]: 6140
% 2.00/0.69  % (22347)Time elapsed: 0.258 s
% 2.00/0.69  % (22347)------------------------------
% 2.00/0.69  % (22347)------------------------------
% 2.00/0.69  % (22332)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.69  
% 2.00/0.69  % (22332)Memory used [KB]: 1791
% 2.00/0.69  % (22332)Time elapsed: 0.270 s
% 2.00/0.69  % (22332)------------------------------
% 2.00/0.69  % (22332)------------------------------
% 2.00/0.69  % (22393)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.69  
% 2.00/0.69  % (22393)Memory used [KB]: 10618
% 2.00/0.69  % (22393)Time elapsed: 0.117 s
% 2.00/0.69  % (22393)------------------------------
% 2.00/0.69  % (22393)------------------------------
% 2.00/0.69  % (22396)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.00/0.70  % (22410)Refutation not found, incomplete strategy% (22410)------------------------------
% 2.00/0.70  % (22410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.70  % (22410)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.70  
% 2.00/0.70  % (22410)Memory used [KB]: 10746
% 2.00/0.70  % (22410)Time elapsed: 0.096 s
% 2.00/0.70  % (22410)------------------------------
% 2.00/0.70  % (22410)------------------------------
% 2.00/0.70  % (22396)Refutation not found, incomplete strategy% (22396)------------------------------
% 2.00/0.70  % (22396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.70  % (22396)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.70  
% 2.00/0.70  % (22396)Memory used [KB]: 1791
% 2.00/0.70  % (22396)Time elapsed: 0.125 s
% 2.00/0.70  % (22396)------------------------------
% 2.00/0.70  % (22396)------------------------------
% 2.00/0.70  % (22409)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.00/0.71  % (22407)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.00/0.71  % (22394)Refutation not found, incomplete strategy% (22394)------------------------------
% 2.00/0.71  % (22394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.71  % (22394)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.71  
% 2.00/0.71  % (22394)Memory used [KB]: 10874
% 2.00/0.71  % (22394)Time elapsed: 0.136 s
% 2.00/0.71  % (22394)------------------------------
% 2.00/0.71  % (22394)------------------------------
% 2.00/0.71  % (22402)Refutation not found, incomplete strategy% (22402)------------------------------
% 2.00/0.71  % (22402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.71  % (22402)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.71  
% 2.00/0.71  % (22402)Memory used [KB]: 10746
% 2.00/0.71  % (22402)Time elapsed: 0.132 s
% 2.00/0.71  % (22402)------------------------------
% 2.00/0.71  % (22402)------------------------------
% 2.59/0.72  % (22407)Refutation not found, incomplete strategy% (22407)------------------------------
% 2.59/0.72  % (22407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.59/0.72  % (22407)Termination reason: Refutation not found, incomplete strategy
% 2.59/0.72  
% 2.59/0.72  % (22407)Memory used [KB]: 10746
% 2.59/0.72  % (22407)Time elapsed: 0.138 s
% 2.59/0.72  % (22407)------------------------------
% 2.59/0.72  % (22407)------------------------------
% 2.82/0.77  % (22467)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.82/0.78  % (22476)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 2.82/0.78  % (22482)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 2.82/0.78  % (22480)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 2.82/0.79  % (22483)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 2.82/0.79  % (22471)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 2.82/0.79  % (22466)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 2.82/0.80  % (22482)Refutation not found, incomplete strategy% (22482)------------------------------
% 2.82/0.80  % (22482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.82/0.80  % (22482)Termination reason: Refutation not found, incomplete strategy
% 2.82/0.80  
% 2.82/0.80  % (22482)Memory used [KB]: 1663
% 2.82/0.80  % (22482)Time elapsed: 0.068 s
% 2.82/0.80  % (22482)------------------------------
% 2.82/0.80  % (22482)------------------------------
% 2.82/0.81  % (22401)Refutation not found, incomplete strategy% (22401)------------------------------
% 2.82/0.81  % (22401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.82/0.81  % (22401)Termination reason: Refutation not found, incomplete strategy
% 2.82/0.81  
% 2.82/0.81  % (22401)Memory used [KB]: 6268
% 2.82/0.81  % (22401)Time elapsed: 0.217 s
% 2.82/0.81  % (22401)------------------------------
% 2.82/0.81  % (22401)------------------------------
% 3.26/0.85  % (22467)Refutation not found, incomplete strategy% (22467)------------------------------
% 3.26/0.85  % (22467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.86  % (22467)Termination reason: Refutation not found, incomplete strategy
% 3.26/0.86  
% 3.26/0.86  % (22467)Memory used [KB]: 6140
% 3.26/0.86  % (22467)Time elapsed: 0.136 s
% 3.26/0.86  % (22467)------------------------------
% 3.26/0.86  % (22467)------------------------------
% 3.48/0.90  % (22466)Refutation not found, incomplete strategy% (22466)------------------------------
% 3.48/0.90  % (22466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.48/0.90  % (22466)Termination reason: Refutation not found, incomplete strategy
% 3.48/0.90  
% 3.48/0.90  % (22466)Memory used [KB]: 6268
% 3.48/0.90  % (22466)Time elapsed: 0.164 s
% 3.48/0.90  % (22466)------------------------------
% 3.48/0.90  % (22466)------------------------------
% 3.78/0.94  % (22338)Time limit reached!
% 3.78/0.94  % (22338)------------------------------
% 3.78/0.94  % (22338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.78/0.94  % (22338)Termination reason: Time limit
% 3.78/0.94  
% 3.78/0.94  % (22338)Memory used [KB]: 15735
% 3.78/0.94  % (22338)Time elapsed: 0.522 s
% 3.78/0.94  % (22338)------------------------------
% 3.78/0.94  % (22338)------------------------------
% 4.19/1.03  % (22409)Refutation not found, incomplete strategy% (22409)------------------------------
% 4.19/1.03  % (22409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.19/1.03  % (22409)Termination reason: Refutation not found, incomplete strategy
% 4.19/1.03  
% 4.19/1.03  % (22409)Memory used [KB]: 3837
% 4.19/1.03  % (22409)Time elapsed: 0.431 s
% 4.19/1.03  % (22409)------------------------------
% 4.19/1.03  % (22409)------------------------------
% 4.19/1.06  % (22339)Time limit reached!
% 4.19/1.06  % (22339)------------------------------
% 4.19/1.06  % (22339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.19/1.07  % (22339)Termination reason: Time limit
% 4.19/1.07  % (22339)Termination phase: Saturation
% 4.19/1.07  
% 4.19/1.07  % (22339)Memory used [KB]: 10490
% 4.19/1.07  % (22339)Time elapsed: 0.600 s
% 4.19/1.07  % (22339)------------------------------
% 4.19/1.07  % (22339)------------------------------
% 5.60/1.13  % (22476)Time limit reached!
% 5.60/1.13  % (22476)------------------------------
% 5.60/1.13  % (22476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.60/1.13  % (22476)Termination reason: Time limit
% 5.60/1.13  
% 5.60/1.13  % (22476)Memory used [KB]: 12281
% 5.60/1.13  % (22476)Time elapsed: 0.410 s
% 5.60/1.13  % (22476)------------------------------
% 5.60/1.13  % (22476)------------------------------
% 5.60/1.14  % (22483)Time limit reached!
% 5.60/1.14  % (22483)------------------------------
% 5.60/1.14  % (22483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.60/1.14  % (22483)Termination reason: Time limit
% 5.60/1.14  
% 5.60/1.14  % (22483)Memory used [KB]: 11129
% 5.60/1.14  % (22483)Time elapsed: 0.414 s
% 5.60/1.14  % (22483)------------------------------
% 5.60/1.14  % (22483)------------------------------
% 6.59/1.20  % (22405)Refutation found. Thanks to Tanya!
% 6.59/1.20  % SZS status Theorem for theBenchmark
% 6.59/1.20  % SZS output start Proof for theBenchmark
% 6.59/1.20  fof(f3426,plain,(
% 6.59/1.20    $false),
% 6.59/1.20    inference(subsumption_resolution,[],[f3423,f33])).
% 6.59/1.20  fof(f33,plain,(
% 6.59/1.20    ~r2_hidden(sK0,sK2)),
% 6.59/1.20    inference(cnf_transformation,[],[f31])).
% 6.59/1.20  fof(f31,plain,(
% 6.59/1.20    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 6.59/1.20    inference(ennf_transformation,[],[f28])).
% 6.59/1.20  fof(f28,negated_conjecture,(
% 6.59/1.20    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 6.59/1.20    inference(negated_conjecture,[],[f27])).
% 6.59/1.20  fof(f27,conjecture,(
% 6.59/1.20    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 6.59/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 6.59/1.20  fof(f3423,plain,(
% 6.59/1.20    r2_hidden(sK0,sK2)),
% 6.59/1.20    inference(resolution,[],[f3422,f83])).
% 6.59/1.20  fof(f83,plain,(
% 6.59/1.20    ( ! [X2,X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 6.59/1.20    inference(definition_unfolding,[],[f51,f68])).
% 6.59/1.20  fof(f68,plain,(
% 6.59/1.20    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 6.59/1.20    inference(definition_unfolding,[],[f44,f67])).
% 6.59/1.20  fof(f67,plain,(
% 6.59/1.20    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 6.59/1.20    inference(definition_unfolding,[],[f49,f66])).
% 6.59/1.20  fof(f66,plain,(
% 6.59/1.20    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 6.59/1.20    inference(definition_unfolding,[],[f55,f65])).
% 6.59/1.20  fof(f65,plain,(
% 6.59/1.20    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 6.59/1.20    inference(definition_unfolding,[],[f56,f64])).
% 6.59/1.20  fof(f64,plain,(
% 6.59/1.20    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 6.59/1.20    inference(definition_unfolding,[],[f57,f58])).
% 6.59/1.20  fof(f58,plain,(
% 6.59/1.20    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 6.59/1.20    inference(cnf_transformation,[],[f24])).
% 6.59/1.20  fof(f24,axiom,(
% 6.59/1.20    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 6.59/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 6.59/1.20  fof(f57,plain,(
% 6.59/1.20    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 6.59/1.20    inference(cnf_transformation,[],[f23])).
% 6.59/1.20  fof(f23,axiom,(
% 6.59/1.20    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 6.59/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 6.59/1.20  fof(f56,plain,(
% 6.59/1.20    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 6.59/1.20    inference(cnf_transformation,[],[f22])).
% 6.59/1.20  fof(f22,axiom,(
% 6.59/1.20    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 6.59/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 6.59/1.20  fof(f55,plain,(
% 6.59/1.20    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.59/1.20    inference(cnf_transformation,[],[f21])).
% 6.59/1.20  fof(f21,axiom,(
% 6.59/1.20    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.59/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 6.59/1.20  fof(f49,plain,(
% 6.59/1.20    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 6.59/1.20    inference(cnf_transformation,[],[f20])).
% 6.59/1.21  fof(f20,axiom,(
% 6.59/1.21    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 6.59/1.21  fof(f44,plain,(
% 6.59/1.21    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 6.59/1.21    inference(cnf_transformation,[],[f19])).
% 6.59/1.21  fof(f19,axiom,(
% 6.59/1.21    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 6.59/1.21  fof(f51,plain,(
% 6.59/1.21    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 6.59/1.21    inference(cnf_transformation,[],[f26])).
% 6.59/1.21  fof(f26,axiom,(
% 6.59/1.21    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 6.59/1.21  fof(f3422,plain,(
% 6.59/1.21    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 6.59/1.21    inference(forward_demodulation,[],[f3421,f119])).
% 6.59/1.21  fof(f119,plain,(
% 6.59/1.21    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 6.59/1.21    inference(forward_demodulation,[],[f106,f93])).
% 6.59/1.21  fof(f93,plain,(
% 6.59/1.21    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 6.59/1.21    inference(backward_demodulation,[],[f92,f78])).
% 6.59/1.21  fof(f78,plain,(
% 6.59/1.21    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 6.59/1.21    inference(definition_unfolding,[],[f39,f69])).
% 6.59/1.21  fof(f69,plain,(
% 6.59/1.21    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 6.59/1.21    inference(definition_unfolding,[],[f43,f68])).
% 6.59/1.21  fof(f43,plain,(
% 6.59/1.21    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 6.59/1.21    inference(cnf_transformation,[],[f25])).
% 6.59/1.21  fof(f25,axiom,(
% 6.59/1.21    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 6.59/1.21  fof(f39,plain,(
% 6.59/1.21    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 6.59/1.21    inference(cnf_transformation,[],[f30])).
% 6.59/1.21  fof(f30,plain,(
% 6.59/1.21    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 6.59/1.21    inference(rectify,[],[f2])).
% 6.59/1.21  fof(f2,axiom,(
% 6.59/1.21    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 6.59/1.21  fof(f92,plain,(
% 6.59/1.21    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 6.59/1.21    inference(forward_demodulation,[],[f77,f91])).
% 6.59/1.21  fof(f91,plain,(
% 6.59/1.21    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 6.59/1.21    inference(backward_demodulation,[],[f90,f76])).
% 6.59/1.21  fof(f76,plain,(
% 6.59/1.21    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 6.59/1.21    inference(definition_unfolding,[],[f36,f69])).
% 6.59/1.21  fof(f36,plain,(
% 6.59/1.21    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.59/1.21    inference(cnf_transformation,[],[f6])).
% 6.59/1.21  fof(f6,axiom,(
% 6.59/1.21    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 6.59/1.21  fof(f90,plain,(
% 6.59/1.21    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)))) )),
% 6.59/1.21    inference(backward_demodulation,[],[f75,f35])).
% 6.59/1.21  fof(f35,plain,(
% 6.59/1.21    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.59/1.21    inference(cnf_transformation,[],[f8])).
% 6.59/1.21  fof(f8,axiom,(
% 6.59/1.21    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 6.59/1.21  fof(f75,plain,(
% 6.59/1.21    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)))) )),
% 6.59/1.21    inference(definition_unfolding,[],[f34,f70])).
% 6.59/1.21  fof(f70,plain,(
% 6.59/1.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 6.59/1.21    inference(definition_unfolding,[],[f45,f69])).
% 6.59/1.21  fof(f45,plain,(
% 6.59/1.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 6.59/1.21    inference(cnf_transformation,[],[f11])).
% 6.59/1.21  fof(f11,axiom,(
% 6.59/1.21    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 6.59/1.21  fof(f34,plain,(
% 6.59/1.21    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 6.59/1.21    inference(cnf_transformation,[],[f7])).
% 6.59/1.21  fof(f7,axiom,(
% 6.59/1.21    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 6.59/1.21  fof(f77,plain,(
% 6.59/1.21    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 6.59/1.21    inference(definition_unfolding,[],[f38,f70])).
% 6.59/1.21  fof(f38,plain,(
% 6.59/1.21    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 6.59/1.21    inference(cnf_transformation,[],[f29])).
% 6.59/1.21  fof(f29,plain,(
% 6.59/1.21    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 6.59/1.21    inference(rectify,[],[f3])).
% 6.59/1.21  fof(f3,axiom,(
% 6.59/1.21    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 6.59/1.21  fof(f106,plain,(
% 6.59/1.21    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 6.59/1.21    inference(superposition,[],[f50,f91])).
% 6.59/1.21  fof(f50,plain,(
% 6.59/1.21    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 6.59/1.21    inference(cnf_transformation,[],[f10])).
% 6.59/1.21  fof(f10,axiom,(
% 6.59/1.21    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 6.59/1.21  fof(f3421,plain,(
% 6.59/1.21    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)),
% 6.59/1.21    inference(forward_demodulation,[],[f3415,f113])).
% 6.59/1.21  fof(f113,plain,(
% 6.59/1.21    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 6.59/1.21    inference(superposition,[],[f50,f42])).
% 6.59/1.21  fof(f42,plain,(
% 6.59/1.21    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 6.59/1.21    inference(cnf_transformation,[],[f1])).
% 6.59/1.21  fof(f1,axiom,(
% 6.59/1.21    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 6.59/1.21  fof(f3415,plain,(
% 6.59/1.21    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 6.59/1.21    inference(superposition,[],[f94,f3242])).
% 6.59/1.21  fof(f3242,plain,(
% 6.59/1.21    sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 6.59/1.21    inference(forward_demodulation,[],[f3241,f3234])).
% 6.59/1.21  fof(f3234,plain,(
% 6.59/1.21    ( ! [X41,X42,X40] : (k6_enumset1(X40,X40,X40,X40,X40,X40,X41,X42) = k6_enumset1(X40,X40,X40,X40,X40,X41,X42,X40)) )),
% 6.59/1.21    inference(subsumption_resolution,[],[f3229,f2298])).
% 6.59/1.21  fof(f2298,plain,(
% 6.59/1.21    ( ! [X30,X28,X26,X29,X27,X25] : (r1_tarski(k6_enumset1(X25,X25,X25,X25,X26,X27,X28,X29),k6_enumset1(X25,X25,X25,X26,X27,X28,X29,X30))) )),
% 6.59/1.21    inference(superposition,[],[f314,f309])).
% 6.59/1.21  fof(f309,plain,(
% 6.59/1.21    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X5,X5,X6)) )),
% 6.59/1.21    inference(superposition,[],[f85,f73])).
% 6.59/1.21  fof(f73,plain,(
% 6.59/1.21    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7)))) )),
% 6.59/1.21    inference(definition_unfolding,[],[f60,f69,f65,f67])).
% 6.59/1.21  fof(f60,plain,(
% 6.59/1.21    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 6.59/1.21    inference(cnf_transformation,[],[f17])).
% 6.59/1.21  fof(f17,axiom,(
% 6.59/1.21    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).
% 6.59/1.21  fof(f85,plain,(
% 6.59/1.21    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)))) )),
% 6.59/1.21    inference(definition_unfolding,[],[f59,f58,f69,f65,f68])).
% 6.59/1.21  fof(f59,plain,(
% 6.59/1.21    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 6.59/1.21    inference(cnf_transformation,[],[f16])).
% 6.59/1.21  fof(f16,axiom,(
% 6.59/1.21    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).
% 6.59/1.21  fof(f314,plain,(
% 6.59/1.21    ( ! [X21,X19,X17,X22,X20,X18,X16] : (r1_tarski(k6_enumset1(X16,X16,X16,X16,X17,X18,X19,X20),k6_enumset1(X16,X16,X17,X18,X19,X20,X21,X22))) )),
% 6.59/1.21    inference(superposition,[],[f79,f85])).
% 6.59/1.21  fof(f79,plain,(
% 6.59/1.21    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 6.59/1.21    inference(definition_unfolding,[],[f40,f69])).
% 6.59/1.21  fof(f40,plain,(
% 6.59/1.21    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 6.59/1.21    inference(cnf_transformation,[],[f9])).
% 6.59/1.21  fof(f9,axiom,(
% 6.59/1.21    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 6.59/1.21  fof(f3229,plain,(
% 6.59/1.21    ( ! [X41,X42,X40] : (~r1_tarski(k6_enumset1(X40,X40,X40,X40,X40,X40,X41,X42),k6_enumset1(X40,X40,X40,X40,X40,X41,X42,X40)) | k6_enumset1(X40,X40,X40,X40,X40,X40,X41,X42) = k6_enumset1(X40,X40,X40,X40,X40,X41,X42,X40)) )),
% 6.59/1.21    inference(superposition,[],[f155,f506])).
% 6.59/1.21  fof(f506,plain,(
% 6.59/1.21    ( ! [X33,X34,X32] : (k6_enumset1(X32,X32,X32,X32,X32,X32,X33,X34) = k3_tarski(k6_enumset1(k6_enumset1(X32,X32,X32,X32,X32,X33,X34,X32),k6_enumset1(X32,X32,X32,X32,X32,X33,X34,X32),k6_enumset1(X32,X32,X32,X32,X32,X33,X34,X32),k6_enumset1(X32,X32,X32,X32,X32,X33,X34,X32),k6_enumset1(X32,X32,X32,X32,X32,X33,X34,X32),k6_enumset1(X32,X32,X32,X32,X32,X33,X34,X32),k6_enumset1(X32,X32,X32,X32,X32,X33,X34,X32),k6_enumset1(X33,X33,X33,X33,X33,X33,X33,X34)))) )),
% 6.59/1.21    inference(superposition,[],[f86,f78])).
% 6.59/1.21  fof(f86,plain,(
% 6.59/1.21    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8)))) )),
% 6.59/1.21    inference(definition_unfolding,[],[f62,f71,f69,f58,f68])).
% 6.59/1.21  fof(f71,plain,(
% 6.59/1.21    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8)))) )),
% 6.59/1.21    inference(definition_unfolding,[],[f61,f69,f64,f67])).
% 6.59/1.21  fof(f61,plain,(
% 6.59/1.21    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))) )),
% 6.59/1.21    inference(cnf_transformation,[],[f13])).
% 6.59/1.21  fof(f13,axiom,(
% 6.59/1.21    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).
% 6.59/1.21  fof(f62,plain,(
% 6.59/1.21    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) )),
% 6.59/1.21    inference(cnf_transformation,[],[f14])).
% 6.59/1.21  fof(f14,axiom,(
% 6.59/1.21    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).
% 6.59/1.21  fof(f155,plain,(
% 6.59/1.21    ( ! [X0,X1] : (~r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0) )),
% 6.59/1.21    inference(resolution,[],[f79,f48])).
% 6.59/1.21  fof(f48,plain,(
% 6.59/1.21    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 6.59/1.21    inference(cnf_transformation,[],[f4])).
% 6.59/1.21  fof(f4,axiom,(
% 6.59/1.21    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.59/1.21  fof(f3241,plain,(
% 6.59/1.21    sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 6.59/1.21    inference(subsumption_resolution,[],[f3240,f79])).
% 6.59/1.21  fof(f3240,plain,(
% 6.59/1.21    ~r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 6.59/1.21    inference(forward_demodulation,[],[f2909,f3234])).
% 6.59/1.21  fof(f2909,plain,(
% 6.59/1.21    ~r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))) | sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 6.59/1.21    inference(resolution,[],[f2901,f48])).
% 6.59/1.21  fof(f2901,plain,(
% 6.59/1.21    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 6.59/1.21    inference(forward_demodulation,[],[f2898,f84])).
% 6.59/1.21  fof(f84,plain,(
% 6.59/1.21    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0)) )),
% 6.59/1.21    inference(definition_unfolding,[],[f54,f66,f66])).
% 6.59/1.21  fof(f54,plain,(
% 6.59/1.21    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 6.59/1.21    inference(cnf_transformation,[],[f12])).
% 6.59/1.21  fof(f12,axiom,(
% 6.59/1.21    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 6.59/1.21  fof(f2898,plain,(
% 6.59/1.21    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,sK2)),sK2)),
% 6.59/1.21    inference(backward_demodulation,[],[f316,f2872])).
% 6.59/1.21  fof(f2872,plain,(
% 6.59/1.21    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X6) = k6_enumset1(X0,X1,X2,X3,X4,X6,X5,X5)) )),
% 6.59/1.21    inference(superposition,[],[f295,f73])).
% 6.59/1.21  fof(f295,plain,(
% 6.59/1.21    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X3,X4,X5,X6,X7,X0,X1,X2) = k3_tarski(k6_enumset1(k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7),k6_enumset1(X2,X2,X2,X2,X2,X1,X0,X0)))) )),
% 6.59/1.21    inference(superposition,[],[f73,f84])).
% 6.59/1.21  fof(f316,plain,(
% 6.59/1.21    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)),
% 6.59/1.21    inference(backward_demodulation,[],[f95,f309])).
% 6.59/1.21  fof(f95,plain,(
% 6.59/1.21    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)),
% 6.59/1.21    inference(backward_demodulation,[],[f74,f84])).
% 6.59/1.21  fof(f74,plain,(
% 6.59/1.21    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 6.59/1.21    inference(definition_unfolding,[],[f32,f69,f68])).
% 6.59/1.21  fof(f32,plain,(
% 6.59/1.21    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 6.59/1.21    inference(cnf_transformation,[],[f31])).
% 6.59/1.21  fof(f94,plain,(
% 6.59/1.21    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 6.59/1.21    inference(backward_demodulation,[],[f80,f50])).
% 6.59/1.21  fof(f80,plain,(
% 6.59/1.21    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 6.59/1.21    inference(definition_unfolding,[],[f41,f70])).
% 6.59/1.21  fof(f41,plain,(
% 6.59/1.21    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 6.59/1.21    inference(cnf_transformation,[],[f5])).
% 6.59/1.21  fof(f5,axiom,(
% 6.59/1.21    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 6.59/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 6.59/1.21  % SZS output end Proof for theBenchmark
% 6.59/1.21  % (22405)------------------------------
% 6.59/1.21  % (22405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.59/1.21  % (22405)Termination reason: Refutation
% 6.59/1.21  
% 6.59/1.21  % (22405)Memory used [KB]: 16502
% 6.59/1.21  % (22405)Time elapsed: 0.628 s
% 6.59/1.21  % (22405)------------------------------
% 6.59/1.21  % (22405)------------------------------
% 6.59/1.21  % (22331)Success in time 0.848 s
%------------------------------------------------------------------------------
