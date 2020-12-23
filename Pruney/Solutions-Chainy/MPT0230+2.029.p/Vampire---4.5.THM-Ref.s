%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 228 expanded)
%              Number of leaves         :   20 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  132 ( 295 expanded)
%              Number of equality atoms :   91 ( 233 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f760,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f90,f164,f665])).

fof(f665,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_tarski(sK1,sK2))
      | ~ sP6(X1,sK0,sK2,sK1) ) ),
    inference(superposition,[],[f217,f644])).

fof(f644,plain,(
    k2_tarski(sK1,sK2) = k4_enumset1(sK1,sK1,sK1,sK2,sK1,sK0) ),
    inference(forward_demodulation,[],[f616,f52])).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f616,plain,(
    k5_xboole_0(k2_tarski(sK1,sK2),k1_xboole_0) = k4_enumset1(sK1,sK1,sK1,sK2,sK1,sK0) ),
    inference(superposition,[],[f210,f411])).

fof(f411,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) ),
    inference(backward_demodulation,[],[f323,f404])).

fof(f404,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f282,f403])).

fof(f403,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f402,f52])).

fof(f402,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f386,f266])).

fof(f266,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f96,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f96,plain,(
    ! [X1] : r1_tarski(k4_xboole_0(X1,X1),X1) ),
    inference(superposition,[],[f73,f75])).

fof(f75,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f51,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f51,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f34,f48])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f386,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f128,f291])).

fof(f291,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f286,f52])).

fof(f286,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f69,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f73,f35])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f49,f48])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f128,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f69,f74])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f50,f48,f48])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f282,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f93,f74])).

fof(f323,plain,(
    k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) ),
    inference(forward_demodulation,[],[f318,f127])).

fof(f127,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f69,f75])).

fof(f318,plain,(
    k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) = k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) ),
    inference(superposition,[],[f69,f119])).

fof(f119,plain,(
    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f71,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f30,f46])).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f210,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X1,X0,X2) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1))) ),
    inference(superposition,[],[f83,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X0),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f45,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))) ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))),k4_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))))) ),
    inference(definition_unfolding,[],[f65,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))),k4_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))))) ),
    inference(definition_unfolding,[],[f47,f53,f67,f46])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f53])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f217,plain,(
    ! [X4,X2,X5,X3] :
      ( r2_hidden(X5,k4_enumset1(X3,X3,X3,X2,X3,X4))
      | ~ sP6(X5,X4,X2,X3) ) ),
    inference(backward_demodulation,[],[f180,f215])).

fof(f215,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) = k4_enumset1(X1,X1,X0,X2,X0,X3) ),
    inference(backward_demodulation,[],[f76,f214])).

fof(f214,plain,(
    ! [X17,X15,X18,X16] : k4_enumset1(X15,X15,X16,X17,X16,X18) = k5_xboole_0(k5_xboole_0(k2_tarski(X16,X16),k4_xboole_0(k2_tarski(X15,X17),k2_tarski(X16,X16))),k4_xboole_0(k2_tarski(X18,X18),k5_xboole_0(k2_tarski(X16,X16),k4_xboole_0(k2_tarski(X15,X17),k2_tarski(X16,X16))))) ),
    inference(superposition,[],[f83,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f55,f66,f67])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ),
    inference(definition_unfolding,[],[f54,f67,f68])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f180,plain,(
    ! [X4,X2,X5,X3] :
      ( r2_hidden(X5,k5_xboole_0(k2_tarski(X3,X3),k4_xboole_0(k2_tarski(X2,X4),k2_tarski(X3,X3))))
      | ~ sP6(X5,X4,X2,X3) ) ),
    inference(superposition,[],[f89,f77])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))))
      | ~ sP6(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP6(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))) != X3 ) ),
    inference(definition_unfolding,[],[f60,f66])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP6(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f164,plain,(
    ~ r2_hidden(sK0,k2_tarski(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f106,f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f106,plain,(
    ~ sP4(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f31,f32,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | X1 = X3
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f31,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,(
    ! [X4,X0,X1] : sP6(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP6(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:59 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.20/0.50  % (5614)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.50  % (5630)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.51  % (5617)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (5638)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (5624)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (5633)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (5622)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (5622)Refutation not found, incomplete strategy% (5622)------------------------------
% 0.20/0.52  % (5622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5625)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (5622)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5622)Memory used [KB]: 10618
% 0.20/0.52  % (5622)Time elapsed: 0.129 s
% 0.20/0.52  % (5622)------------------------------
% 0.20/0.52  % (5622)------------------------------
% 0.20/0.52  % (5613)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (5616)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (5624)Refutation not found, incomplete strategy% (5624)------------------------------
% 0.20/0.52  % (5624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5624)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5624)Memory used [KB]: 1791
% 0.20/0.52  % (5624)Time elapsed: 0.063 s
% 0.20/0.52  % (5624)------------------------------
% 0.20/0.52  % (5624)------------------------------
% 0.20/0.53  % (5612)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (5615)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (5636)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (5611)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (5611)Refutation not found, incomplete strategy% (5611)------------------------------
% 0.20/0.53  % (5611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5611)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (5611)Memory used [KB]: 1663
% 0.20/0.53  % (5611)Time elapsed: 0.125 s
% 0.20/0.53  % (5610)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (5611)------------------------------
% 0.20/0.53  % (5611)------------------------------
% 0.20/0.54  % (5620)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (5635)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (5639)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (5628)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (5628)Refutation not found, incomplete strategy% (5628)------------------------------
% 0.20/0.54  % (5628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5628)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5628)Memory used [KB]: 1791
% 0.20/0.54  % (5628)Time elapsed: 0.139 s
% 0.20/0.54  % (5628)------------------------------
% 0.20/0.54  % (5628)------------------------------
% 0.20/0.54  % (5621)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (5634)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (5619)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (5626)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (5631)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (5626)Refutation not found, incomplete strategy% (5626)------------------------------
% 0.20/0.55  % (5626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (5626)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (5626)Memory used [KB]: 10618
% 0.20/0.55  % (5626)Time elapsed: 0.138 s
% 0.20/0.55  % (5626)------------------------------
% 0.20/0.55  % (5626)------------------------------
% 0.20/0.55  % (5618)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (5623)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (5637)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (5630)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % (5627)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.56  % (5632)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.56  % (5640)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.56  % (5640)Refutation not found, incomplete strategy% (5640)------------------------------
% 0.20/0.56  % (5640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (5640)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (5640)Memory used [KB]: 1663
% 0.20/0.56  % (5640)Time elapsed: 0.003 s
% 0.20/0.56  % (5640)------------------------------
% 0.20/0.56  % (5640)------------------------------
% 0.20/0.56  % (5637)Refutation not found, incomplete strategy% (5637)------------------------------
% 0.20/0.56  % (5637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (5637)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (5637)Memory used [KB]: 6268
% 0.20/0.56  % (5637)Time elapsed: 0.159 s
% 0.20/0.56  % (5637)------------------------------
% 0.20/0.56  % (5637)------------------------------
% 1.58/0.57  % SZS output start Proof for theBenchmark
% 1.58/0.57  fof(f760,plain,(
% 1.58/0.57    $false),
% 1.58/0.57    inference(unit_resulting_resolution,[],[f90,f164,f665])).
% 1.58/0.57  fof(f665,plain,(
% 1.58/0.57    ( ! [X1] : (r2_hidden(X1,k2_tarski(sK1,sK2)) | ~sP6(X1,sK0,sK2,sK1)) )),
% 1.58/0.57    inference(superposition,[],[f217,f644])).
% 1.58/0.57  fof(f644,plain,(
% 1.58/0.57    k2_tarski(sK1,sK2) = k4_enumset1(sK1,sK1,sK1,sK2,sK1,sK0)),
% 1.58/0.57    inference(forward_demodulation,[],[f616,f52])).
% 1.58/0.57  fof(f52,plain,(
% 1.58/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.58/0.57    inference(cnf_transformation,[],[f8])).
% 1.58/0.57  fof(f8,axiom,(
% 1.58/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.58/0.57  fof(f616,plain,(
% 1.58/0.57    k5_xboole_0(k2_tarski(sK1,sK2),k1_xboole_0) = k4_enumset1(sK1,sK1,sK1,sK2,sK1,sK0)),
% 1.58/0.57    inference(superposition,[],[f210,f411])).
% 1.58/0.57  fof(f411,plain,(
% 1.58/0.57    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))),
% 1.58/0.57    inference(backward_demodulation,[],[f323,f404])).
% 1.58/0.57  fof(f404,plain,(
% 1.58/0.57    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.58/0.57    inference(backward_demodulation,[],[f282,f403])).
% 1.58/0.57  fof(f403,plain,(
% 1.58/0.57    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = X4) )),
% 1.58/0.57    inference(forward_demodulation,[],[f402,f52])).
% 1.58/0.57  fof(f402,plain,(
% 1.58/0.57    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0)) )),
% 1.58/0.57    inference(forward_demodulation,[],[f386,f266])).
% 1.58/0.57  fof(f266,plain,(
% 1.58/0.57    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.58/0.57    inference(unit_resulting_resolution,[],[f96,f35])).
% 1.58/0.57  fof(f35,plain,(
% 1.58/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.58/0.57    inference(cnf_transformation,[],[f28])).
% 1.58/0.57  fof(f28,plain,(
% 1.58/0.57    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.58/0.57    inference(ennf_transformation,[],[f6])).
% 1.58/0.57  fof(f6,axiom,(
% 1.58/0.57    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.58/0.57  fof(f96,plain,(
% 1.58/0.57    ( ! [X1] : (r1_tarski(k4_xboole_0(X1,X1),X1)) )),
% 1.58/0.57    inference(superposition,[],[f73,f75])).
% 1.58/0.57  fof(f75,plain,(
% 1.58/0.57    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.58/0.57    inference(definition_unfolding,[],[f51,f48])).
% 1.58/0.57  fof(f48,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f7])).
% 1.58/0.57  fof(f7,axiom,(
% 1.58/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.58/0.57  fof(f51,plain,(
% 1.58/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.58/0.57    inference(cnf_transformation,[],[f25])).
% 1.58/0.57  fof(f25,plain,(
% 1.58/0.57    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.58/0.57    inference(rectify,[],[f2])).
% 1.58/0.57  fof(f2,axiom,(
% 1.58/0.57    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.58/0.57  fof(f73,plain,(
% 1.58/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.58/0.57    inference(definition_unfolding,[],[f34,f48])).
% 1.58/0.57  fof(f34,plain,(
% 1.58/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f4])).
% 1.58/0.57  fof(f4,axiom,(
% 1.58/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.58/0.57  fof(f386,plain,(
% 1.58/0.57    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k4_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 1.58/0.57    inference(superposition,[],[f128,f291])).
% 1.58/0.57  fof(f291,plain,(
% 1.58/0.57    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 1.58/0.57    inference(forward_demodulation,[],[f286,f52])).
% 1.58/0.57  fof(f286,plain,(
% 1.58/0.57    ( ! [X2] : (k4_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.58/0.57    inference(superposition,[],[f69,f93])).
% 1.58/0.57  fof(f93,plain,(
% 1.58/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.58/0.57    inference(unit_resulting_resolution,[],[f73,f35])).
% 1.58/0.57  fof(f69,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.58/0.57    inference(definition_unfolding,[],[f49,f48])).
% 1.58/0.57  fof(f49,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f3])).
% 1.58/0.57  fof(f3,axiom,(
% 1.58/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.58/0.57  fof(f128,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.58/0.57    inference(superposition,[],[f69,f74])).
% 1.58/0.57  fof(f74,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.58/0.57    inference(definition_unfolding,[],[f50,f48,f48])).
% 1.58/0.57  fof(f50,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f1])).
% 1.58/0.57  fof(f1,axiom,(
% 1.58/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.58/0.57  fof(f282,plain,(
% 1.58/0.57    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 1.58/0.57    inference(superposition,[],[f93,f74])).
% 1.58/0.57  fof(f323,plain,(
% 1.58/0.57    k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))),
% 1.58/0.57    inference(forward_demodulation,[],[f318,f127])).
% 1.58/0.57  fof(f127,plain,(
% 1.58/0.57    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.58/0.57    inference(superposition,[],[f69,f75])).
% 1.58/0.57  fof(f318,plain,(
% 1.58/0.57    k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) = k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))),
% 1.58/0.57    inference(superposition,[],[f69,f119])).
% 1.58/0.57  fof(f119,plain,(
% 1.58/0.57    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))),
% 1.58/0.57    inference(unit_resulting_resolution,[],[f71,f72])).
% 1.58/0.57  fof(f72,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.58/0.57    inference(definition_unfolding,[],[f33,f48])).
% 1.58/0.57  fof(f33,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.58/0.57    inference(cnf_transformation,[],[f27])).
% 1.58/0.57  fof(f27,plain,(
% 1.58/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.58/0.57    inference(ennf_transformation,[],[f5])).
% 1.58/0.57  fof(f5,axiom,(
% 1.58/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.58/0.57  fof(f71,plain,(
% 1.58/0.57    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))),
% 1.58/0.57    inference(definition_unfolding,[],[f30,f46])).
% 1.58/0.57  fof(f46,plain,(
% 1.58/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f15])).
% 1.58/0.57  fof(f15,axiom,(
% 1.58/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.58/0.57  fof(f30,plain,(
% 1.58/0.57    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.58/0.57    inference(cnf_transformation,[],[f26])).
% 1.58/0.57  fof(f26,plain,(
% 1.58/0.57    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.58/0.57    inference(ennf_transformation,[],[f24])).
% 1.58/0.57  fof(f24,negated_conjecture,(
% 1.58/0.57    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.58/0.57    inference(negated_conjecture,[],[f23])).
% 1.58/0.57  fof(f23,conjecture,(
% 1.58/0.57    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.58/0.57  fof(f210,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X1,X0,X2) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))) )),
% 1.58/0.57    inference(superposition,[],[f83,f70])).
% 1.58/0.57  fof(f70,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X0),k2_tarski(X0,X0)))) )),
% 1.58/0.57    inference(definition_unfolding,[],[f45,f66])).
% 1.58/0.57  fof(f66,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0)))) )),
% 1.58/0.57    inference(definition_unfolding,[],[f44,f53])).
% 1.58/0.57  fof(f53,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f9])).
% 1.58/0.57  fof(f9,axiom,(
% 1.58/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.58/0.57  fof(f44,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f13])).
% 1.58/0.57  fof(f13,axiom,(
% 1.58/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 1.58/0.57  fof(f45,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f16])).
% 1.58/0.57  fof(f16,axiom,(
% 1.58/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.58/0.57  fof(f83,plain,(
% 1.58/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))),k4_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))))) )),
% 1.58/0.57    inference(definition_unfolding,[],[f65,f68])).
% 1.58/0.57  fof(f68,plain,(
% 1.58/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))),k4_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))))) )),
% 1.58/0.57    inference(definition_unfolding,[],[f47,f53,f67,f46])).
% 1.58/0.57  fof(f67,plain,(
% 1.58/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) )),
% 1.58/0.57    inference(definition_unfolding,[],[f36,f53])).
% 1.58/0.57  fof(f36,plain,(
% 1.58/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f12])).
% 1.58/0.57  fof(f12,axiom,(
% 1.58/0.57    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 1.58/0.57  fof(f47,plain,(
% 1.58/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f14])).
% 1.58/0.57  fof(f14,axiom,(
% 1.58/0.57    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 1.58/0.57  fof(f65,plain,(
% 1.58/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f19])).
% 1.58/0.57  fof(f19,axiom,(
% 1.58/0.57    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.58/0.57  fof(f217,plain,(
% 1.58/0.57    ( ! [X4,X2,X5,X3] : (r2_hidden(X5,k4_enumset1(X3,X3,X3,X2,X3,X4)) | ~sP6(X5,X4,X2,X3)) )),
% 1.58/0.57    inference(backward_demodulation,[],[f180,f215])).
% 1.58/0.57  fof(f215,plain,(
% 1.58/0.57    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) = k4_enumset1(X1,X1,X0,X2,X0,X3)) )),
% 1.58/0.57    inference(backward_demodulation,[],[f76,f214])).
% 1.58/0.57  fof(f214,plain,(
% 1.58/0.57    ( ! [X17,X15,X18,X16] : (k4_enumset1(X15,X15,X16,X17,X16,X18) = k5_xboole_0(k5_xboole_0(k2_tarski(X16,X16),k4_xboole_0(k2_tarski(X15,X17),k2_tarski(X16,X16))),k4_xboole_0(k2_tarski(X18,X18),k5_xboole_0(k2_tarski(X16,X16),k4_xboole_0(k2_tarski(X15,X17),k2_tarski(X16,X16)))))) )),
% 1.58/0.57    inference(superposition,[],[f83,f77])).
% 1.58/0.57  fof(f77,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) )),
% 1.58/0.57    inference(definition_unfolding,[],[f55,f66,f67])).
% 1.58/0.57  fof(f55,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f17])).
% 1.58/0.57  fof(f17,axiom,(
% 1.58/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.58/0.57  fof(f76,plain,(
% 1.58/0.57    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))))) )),
% 1.58/0.57    inference(definition_unfolding,[],[f54,f67,f68])).
% 1.58/0.57  fof(f54,plain,(
% 1.58/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f18])).
% 1.58/0.57  fof(f18,axiom,(
% 1.58/0.57    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.58/0.57  fof(f180,plain,(
% 1.58/0.57    ( ! [X4,X2,X5,X3] : (r2_hidden(X5,k5_xboole_0(k2_tarski(X3,X3),k4_xboole_0(k2_tarski(X2,X4),k2_tarski(X3,X3)))) | ~sP6(X5,X4,X2,X3)) )),
% 1.58/0.57    inference(superposition,[],[f89,f77])).
% 1.58/0.57  fof(f89,plain,(
% 1.58/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0)))) | ~sP6(X4,X2,X1,X0)) )),
% 1.58/0.57    inference(equality_resolution,[],[f81])).
% 1.58/0.57  fof(f81,plain,(
% 1.58/0.57    ( ! [X4,X2,X0,X3,X1] : (~sP6(X4,X2,X1,X0) | r2_hidden(X4,X3) | k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))) != X3) )),
% 1.58/0.57    inference(definition_unfolding,[],[f60,f66])).
% 1.58/0.57  fof(f60,plain,(
% 1.58/0.57    ( ! [X4,X2,X0,X3,X1] : (~sP6(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.58/0.57    inference(cnf_transformation,[],[f29])).
% 1.58/0.57  fof(f29,plain,(
% 1.58/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.58/0.57    inference(ennf_transformation,[],[f10])).
% 1.58/0.57  fof(f10,axiom,(
% 1.58/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.58/0.57  fof(f164,plain,(
% 1.58/0.57    ~r2_hidden(sK0,k2_tarski(sK1,sK2))),
% 1.58/0.57    inference(unit_resulting_resolution,[],[f106,f84])).
% 1.58/0.57  fof(f84,plain,(
% 1.58/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_tarski(X0,X1)) | sP4(X3,X1,X0)) )),
% 1.58/0.57    inference(equality_resolution,[],[f41])).
% 1.58/0.57  fof(f41,plain,(
% 1.58/0.57    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.58/0.57    inference(cnf_transformation,[],[f11])).
% 1.58/0.57  fof(f11,axiom,(
% 1.58/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.58/0.57  fof(f106,plain,(
% 1.58/0.57    ~sP4(sK0,sK2,sK1)),
% 1.58/0.57    inference(unit_resulting_resolution,[],[f31,f32,f39])).
% 1.58/0.57  fof(f39,plain,(
% 1.58/0.57    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | X1 = X3 | X0 = X3) )),
% 1.58/0.57    inference(cnf_transformation,[],[f11])).
% 1.58/0.57  fof(f32,plain,(
% 1.58/0.57    sK0 != sK2),
% 1.58/0.57    inference(cnf_transformation,[],[f26])).
% 1.58/0.57  fof(f31,plain,(
% 1.58/0.57    sK0 != sK1),
% 1.58/0.57    inference(cnf_transformation,[],[f26])).
% 1.58/0.57  fof(f90,plain,(
% 1.58/0.57    ( ! [X4,X0,X1] : (sP6(X4,X4,X1,X0)) )),
% 1.58/0.57    inference(equality_resolution,[],[f58])).
% 1.58/0.57  fof(f58,plain,(
% 1.58/0.57    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP6(X4,X2,X1,X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f29])).
% 1.58/0.57  % SZS output end Proof for theBenchmark
% 1.58/0.57  % (5630)------------------------------
% 1.58/0.57  % (5630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (5630)Termination reason: Refutation
% 1.58/0.57  
% 1.58/0.57  % (5630)Memory used [KB]: 2174
% 1.58/0.57  % (5630)Time elapsed: 0.162 s
% 1.58/0.57  % (5630)------------------------------
% 1.58/0.57  % (5630)------------------------------
% 1.58/0.58  % (5601)Success in time 0.211 s
%------------------------------------------------------------------------------
