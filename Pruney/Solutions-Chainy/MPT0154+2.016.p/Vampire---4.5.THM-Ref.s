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
% DateTime   : Thu Dec  3 12:33:33 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   93 (1981 expanded)
%              Number of leaves         :   15 ( 623 expanded)
%              Depth                    :   21
%              Number of atoms          :  130 (2745 expanded)
%              Number of equality atoms :   75 (1665 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1088,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1087])).

fof(f1087,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(backward_demodulation,[],[f997,f1076])).

fof(f1076,plain,(
    ! [X6,X8,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(X8,k5_xboole_0(X6,k5_xboole_0(X7,X8))) ),
    inference(superposition,[],[f998,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f998,plain,(
    ! [X4,X3] : k5_xboole_0(X4,k5_xboole_0(X3,X4)) = X3 ),
    inference(forward_demodulation,[],[f990,f972])).

fof(f972,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f949,f580])).

fof(f580,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k5_xboole_0(k3_xboole_0(X7,X7),X8)) = X8 ),
    inference(forward_demodulation,[],[f575,f407])).

fof(f407,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f406,f55])).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f406,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(resolution,[],[f405,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ) ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f405,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f402,f338])).

fof(f338,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(k1_xboole_0,X1),X0)
      | r1_tarski(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f98,f55])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X0)))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f70,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f31])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f402,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_xboole_0,X0),X1)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f368,f34])).

fof(f368,plain,(
    ! [X5,X3] :
      ( ~ r2_hidden(X5,k1_xboole_0)
      | r2_hidden(X5,X3) ) ),
    inference(superposition,[],[f71,f58])).

fof(f58,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f28,f31,f50])).

fof(f28,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f47,f31])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f575,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k5_xboole_0(k3_xboole_0(X7,X7),X8)) = k5_xboole_0(k1_xboole_0,X8) ),
    inference(superposition,[],[f37,f359])).

fof(f359,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f58,f56])).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f25,f50])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f949,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X0)) ),
    inference(backward_demodulation,[],[f638,f930])).

fof(f930,plain,(
    ! [X0] : k3_xboole_0(X0,k3_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f320,f616])).

fof(f616,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = X1 ),
    inference(superposition,[],[f580,f608])).

fof(f608,plain,(
    ! [X2] : k3_xboole_0(k3_xboole_0(X2,X2),k3_xboole_0(X2,X2)) = X2 ),
    inference(forward_demodulation,[],[f595,f381])).

fof(f381,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f57,f359])).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f27,f50])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f595,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = k3_xboole_0(k3_xboole_0(X2,X2),k3_xboole_0(X2,X2)) ),
    inference(superposition,[],[f580,f359])).

fof(f320,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))) = X1 ),
    inference(resolution,[],[f319,f59])).

fof(f319,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f82,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(k3_xboole_0(X0,X1),X2),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f67,f34])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f638,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,k3_xboole_0(X0,X0)))) ),
    inference(forward_demodulation,[],[f633,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f633,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(k3_xboole_0(X0,X0),X0))) ),
    inference(resolution,[],[f626,f59])).

fof(f626,plain,(
    ! [X20] : r1_tarski(X20,k3_xboole_0(X20,X20)) ),
    inference(superposition,[],[f319,f608])).

fof(f990,plain,(
    ! [X4,X3] : k5_xboole_0(X4,k3_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X3,X4))) = X3 ),
    inference(backward_demodulation,[],[f911,f972])).

fof(f911,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X3) = k5_xboole_0(X4,k3_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X3,X4))) ),
    inference(forward_demodulation,[],[f888,f381])).

fof(f888,plain,(
    ! [X4,X3] : k5_xboole_0(k3_xboole_0(X3,X3),k1_xboole_0) = k5_xboole_0(X4,k3_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f616,f568])).

fof(f568,plain,(
    ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2)))) ),
    inference(superposition,[],[f359,f37])).

fof(f997,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0))))) ),
    inference(backward_demodulation,[],[f865,f972])).

fof(f865,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))))) ),
    inference(backward_demodulation,[],[f75,f863])).

fof(f863,plain,(
    ! [X8,X7] : k3_xboole_0(X7,X7) = k3_xboole_0(X7,k5_xboole_0(X7,k5_xboole_0(X8,k3_xboole_0(X7,X8)))) ),
    inference(forward_demodulation,[],[f839,f381])).

fof(f839,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k5_xboole_0(X7,k5_xboole_0(X8,k3_xboole_0(X7,X8)))) = k5_xboole_0(k3_xboole_0(X7,X7),k1_xboole_0) ),
    inference(superposition,[],[f616,f349])).

fof(f349,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) ),
    inference(superposition,[],[f58,f29])).

fof(f75,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))))))) ),
    inference(forward_demodulation,[],[f74,f37])).

fof(f74,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))))))) ),
    inference(backward_demodulation,[],[f73,f37])).

fof(f73,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))))) ),
    inference(forward_demodulation,[],[f72,f29])).

fof(f72,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k1_tarski(sK0)))) ),
    inference(backward_demodulation,[],[f54,f29])).

fof(f54,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f23,f51,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f36,f50,f51])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f30,f50])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f23,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:53:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (22165)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.49  % (22158)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.51  % (22165)Refutation not found, incomplete strategy% (22165)------------------------------
% 0.22/0.51  % (22165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22165)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22165)Memory used [KB]: 6268
% 0.22/0.51  % (22165)Time elapsed: 0.082 s
% 0.22/0.51  % (22165)------------------------------
% 0.22/0.51  % (22165)------------------------------
% 0.22/0.51  % (22142)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (22144)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.24/0.53  % (22159)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.24/0.53  % (22151)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.24/0.53  % (22151)Refutation not found, incomplete strategy% (22151)------------------------------
% 1.24/0.53  % (22151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (22151)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (22151)Memory used [KB]: 10618
% 1.24/0.53  % (22151)Time elapsed: 0.123 s
% 1.24/0.53  % (22151)------------------------------
% 1.24/0.53  % (22151)------------------------------
% 1.24/0.53  % (22161)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.24/0.53  % (22143)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.24/0.54  % (22143)Refutation not found, incomplete strategy% (22143)------------------------------
% 1.24/0.54  % (22143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (22143)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (22143)Memory used [KB]: 6140
% 1.24/0.54  % (22143)Time elapsed: 0.127 s
% 1.24/0.54  % (22143)------------------------------
% 1.24/0.54  % (22143)------------------------------
% 1.24/0.54  % (22153)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.24/0.54  % (22150)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.24/0.54  % (22152)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.54  % (22164)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.24/0.54  % (22139)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.24/0.54  % (22154)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.24/0.54  % (22167)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.24/0.54  % (22141)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.54  % (22137)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.24/0.54  % (22137)Refutation not found, incomplete strategy% (22137)------------------------------
% 1.24/0.54  % (22137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (22137)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (22137)Memory used [KB]: 1663
% 1.24/0.54  % (22137)Time elapsed: 0.123 s
% 1.24/0.54  % (22137)------------------------------
% 1.24/0.54  % (22137)------------------------------
% 1.24/0.54  % (22141)Refutation not found, incomplete strategy% (22141)------------------------------
% 1.24/0.54  % (22141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (22141)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (22141)Memory used [KB]: 10746
% 1.24/0.54  % (22141)Time elapsed: 0.127 s
% 1.24/0.54  % (22141)------------------------------
% 1.24/0.54  % (22141)------------------------------
% 1.24/0.54  % (22157)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.24/0.54  % (22146)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.24/0.54  % (22166)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.24/0.55  % (22163)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.24/0.55  % (22149)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.24/0.55  % (22168)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.24/0.55  % (22163)Refutation not found, incomplete strategy% (22163)------------------------------
% 1.24/0.55  % (22163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.55  % (22163)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.55  
% 1.24/0.55  % (22163)Memory used [KB]: 1663
% 1.24/0.55  % (22163)Time elapsed: 0.136 s
% 1.24/0.55  % (22163)------------------------------
% 1.24/0.55  % (22163)------------------------------
% 1.24/0.55  % (22157)Refutation not found, incomplete strategy% (22157)------------------------------
% 1.24/0.55  % (22157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.55  % (22149)Refutation not found, incomplete strategy% (22149)------------------------------
% 1.24/0.55  % (22149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.55  % (22149)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.55  
% 1.24/0.55  % (22149)Memory used [KB]: 10618
% 1.24/0.55  % (22149)Time elapsed: 0.140 s
% 1.24/0.55  % (22149)------------------------------
% 1.24/0.55  % (22149)------------------------------
% 1.24/0.55  % (22169)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.24/0.55  % (22157)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.55  
% 1.24/0.55  % (22157)Memory used [KB]: 10618
% 1.24/0.55  % (22157)Time elapsed: 0.141 s
% 1.24/0.55  % (22157)------------------------------
% 1.24/0.55  % (22157)------------------------------
% 1.24/0.55  % (22155)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.24/0.55  % (22155)Refutation not found, incomplete strategy% (22155)------------------------------
% 1.24/0.55  % (22155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.55  % (22155)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.55  
% 1.24/0.55  % (22155)Memory used [KB]: 6140
% 1.24/0.55  % (22155)Time elapsed: 0.002 s
% 1.24/0.55  % (22155)------------------------------
% 1.24/0.55  % (22155)------------------------------
% 1.24/0.55  % (22148)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.53/0.55  % (22160)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.53/0.55  % (22160)Refutation not found, incomplete strategy% (22160)------------------------------
% 1.53/0.55  % (22160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.55  % (22160)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.55  
% 1.53/0.55  % (22160)Memory used [KB]: 10746
% 1.53/0.55  % (22160)Time elapsed: 0.149 s
% 1.53/0.55  % (22160)------------------------------
% 1.53/0.55  % (22160)------------------------------
% 1.53/0.56  % (22148)Refutation not found, incomplete strategy% (22148)------------------------------
% 1.53/0.56  % (22148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (22148)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (22148)Memory used [KB]: 10618
% 1.53/0.56  % (22148)Time elapsed: 0.150 s
% 1.53/0.56  % (22148)------------------------------
% 1.53/0.56  % (22148)------------------------------
% 1.53/0.56  % (22161)Refutation not found, incomplete strategy% (22161)------------------------------
% 1.53/0.56  % (22161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (22161)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (22161)Memory used [KB]: 1663
% 1.53/0.56  % (22161)Time elapsed: 0.118 s
% 1.53/0.56  % (22161)------------------------------
% 1.53/0.56  % (22161)------------------------------
% 1.53/0.56  % (22150)Refutation not found, incomplete strategy% (22150)------------------------------
% 1.53/0.56  % (22150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (22150)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (22150)Memory used [KB]: 10618
% 1.53/0.56  % (22150)Time elapsed: 0.152 s
% 1.53/0.56  % (22150)------------------------------
% 1.53/0.56  % (22150)------------------------------
% 1.53/0.56  % (22162)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.53/0.56  % (22162)Refutation not found, incomplete strategy% (22162)------------------------------
% 1.53/0.56  % (22162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (22162)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (22162)Memory used [KB]: 10746
% 1.53/0.56  % (22162)Time elapsed: 0.149 s
% 1.53/0.56  % (22162)------------------------------
% 1.53/0.56  % (22162)------------------------------
% 1.53/0.57  % (22147)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.53/0.57  % (22156)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.57  % (22166)Refutation not found, incomplete strategy% (22166)------------------------------
% 1.53/0.57  % (22166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (22166)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (22166)Memory used [KB]: 10874
% 1.53/0.57  % (22166)Time elapsed: 0.148 s
% 1.53/0.57  % (22166)------------------------------
% 1.53/0.57  % (22166)------------------------------
% 1.53/0.59  % (22180)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.53/0.60  % (22180)Refutation not found, incomplete strategy% (22180)------------------------------
% 1.53/0.60  % (22180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.60  % (22180)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.60  
% 1.53/0.60  % (22180)Memory used [KB]: 6140
% 1.53/0.60  % (22180)Time elapsed: 0.046 s
% 1.53/0.60  % (22180)------------------------------
% 1.53/0.60  % (22180)------------------------------
% 1.53/0.62  % (22146)Refutation found. Thanks to Tanya!
% 1.53/0.62  % SZS status Theorem for theBenchmark
% 1.53/0.62  % SZS output start Proof for theBenchmark
% 1.53/0.62  fof(f1088,plain,(
% 1.53/0.62    $false),
% 1.53/0.62    inference(trivial_inequality_removal,[],[f1087])).
% 1.53/0.62  fof(f1087,plain,(
% 1.53/0.62    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))),
% 1.53/0.62    inference(backward_demodulation,[],[f997,f1076])).
% 1.53/0.62  fof(f1076,plain,(
% 1.53/0.62    ( ! [X6,X8,X7] : (k5_xboole_0(X6,X7) = k5_xboole_0(X8,k5_xboole_0(X6,k5_xboole_0(X7,X8)))) )),
% 1.53/0.62    inference(superposition,[],[f998,f37])).
% 1.53/0.62  fof(f37,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.53/0.62    inference(cnf_transformation,[],[f11])).
% 1.53/0.62  fof(f11,axiom,(
% 1.53/0.62    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.53/0.62  fof(f998,plain,(
% 1.53/0.62    ( ! [X4,X3] : (k5_xboole_0(X4,k5_xboole_0(X3,X4)) = X3) )),
% 1.53/0.62    inference(forward_demodulation,[],[f990,f972])).
% 1.53/0.62  fof(f972,plain,(
% 1.53/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.53/0.62    inference(forward_demodulation,[],[f949,f580])).
% 1.53/0.62  fof(f580,plain,(
% 1.53/0.62    ( ! [X8,X7] : (k5_xboole_0(X7,k5_xboole_0(k3_xboole_0(X7,X7),X8)) = X8) )),
% 1.53/0.62    inference(forward_demodulation,[],[f575,f407])).
% 1.53/0.62  fof(f407,plain,(
% 1.53/0.62    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.53/0.62    inference(forward_demodulation,[],[f406,f55])).
% 1.53/0.62  fof(f55,plain,(
% 1.53/0.62    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.53/0.62    inference(definition_unfolding,[],[f24,f31])).
% 1.53/0.62  fof(f31,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.53/0.62    inference(cnf_transformation,[],[f6])).
% 1.53/0.62  fof(f6,axiom,(
% 1.53/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.53/0.62  fof(f24,plain,(
% 1.53/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.53/0.62    inference(cnf_transformation,[],[f9])).
% 1.53/0.62  fof(f9,axiom,(
% 1.53/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.53/0.62  fof(f406,plain,(
% 1.53/0.62    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0) )),
% 1.53/0.62    inference(resolution,[],[f405,f59])).
% 1.53/0.62  fof(f59,plain,(
% 1.53/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1) )),
% 1.53/0.62    inference(definition_unfolding,[],[f33,f50])).
% 1.53/0.62  fof(f50,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.53/0.62    inference(definition_unfolding,[],[f32,f31])).
% 1.53/0.62  fof(f32,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.53/0.62    inference(cnf_transformation,[],[f12])).
% 1.53/0.62  fof(f12,axiom,(
% 1.53/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.53/0.62  fof(f33,plain,(
% 1.53/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.53/0.62    inference(cnf_transformation,[],[f21])).
% 1.53/0.62  fof(f21,plain,(
% 1.53/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.53/0.62    inference(ennf_transformation,[],[f7])).
% 1.53/0.62  fof(f7,axiom,(
% 1.53/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.53/0.62  fof(f405,plain,(
% 1.53/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.53/0.62    inference(subsumption_resolution,[],[f402,f338])).
% 1.53/0.62  fof(f338,plain,(
% 1.53/0.62    ( ! [X0,X1] : (~r2_hidden(sK2(k1_xboole_0,X1),X0) | r1_tarski(k1_xboole_0,X1)) )),
% 1.53/0.62    inference(superposition,[],[f98,f55])).
% 1.53/0.62  fof(f98,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X0))) | r1_tarski(X0,X1)) )),
% 1.53/0.62    inference(resolution,[],[f70,f34])).
% 1.53/0.62  fof(f34,plain,(
% 1.53/0.62    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f22])).
% 1.53/0.62  fof(f22,plain,(
% 1.53/0.62    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.53/0.62    inference(ennf_transformation,[],[f19])).
% 1.53/0.62  fof(f19,plain,(
% 1.53/0.62    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.53/0.62    inference(unused_predicate_definition_removal,[],[f2])).
% 1.53/0.62  fof(f2,axiom,(
% 1.53/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.53/0.62  fof(f70,plain,(
% 1.53/0.62    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.53/0.62    inference(equality_resolution,[],[f61])).
% 1.53/0.62  fof(f61,plain,(
% 1.53/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.53/0.62    inference(definition_unfolding,[],[f48,f31])).
% 1.53/0.62  fof(f48,plain,(
% 1.53/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.53/0.62    inference(cnf_transformation,[],[f4])).
% 1.53/0.62  fof(f4,axiom,(
% 1.53/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.53/0.62  fof(f402,plain,(
% 1.53/0.62    ( ! [X0,X1] : (r2_hidden(sK2(k1_xboole_0,X0),X1) | r1_tarski(k1_xboole_0,X0)) )),
% 1.53/0.62    inference(resolution,[],[f368,f34])).
% 1.53/0.62  fof(f368,plain,(
% 1.53/0.62    ( ! [X5,X3] : (~r2_hidden(X5,k1_xboole_0) | r2_hidden(X5,X3)) )),
% 1.53/0.62    inference(superposition,[],[f71,f58])).
% 1.53/0.62  fof(f58,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 1.53/0.62    inference(definition_unfolding,[],[f28,f31,f50])).
% 1.53/0.62  fof(f28,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.53/0.62    inference(cnf_transformation,[],[f10])).
% 1.53/0.62  fof(f10,axiom,(
% 1.53/0.62    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.53/0.62  fof(f71,plain,(
% 1.53/0.62    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 1.53/0.62    inference(equality_resolution,[],[f62])).
% 1.53/0.62  fof(f62,plain,(
% 1.53/0.62    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.53/0.62    inference(definition_unfolding,[],[f47,f31])).
% 1.53/0.62  fof(f47,plain,(
% 1.53/0.62    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.53/0.62    inference(cnf_transformation,[],[f4])).
% 1.53/0.62  fof(f575,plain,(
% 1.53/0.62    ( ! [X8,X7] : (k5_xboole_0(X7,k5_xboole_0(k3_xboole_0(X7,X7),X8)) = k5_xboole_0(k1_xboole_0,X8)) )),
% 1.53/0.62    inference(superposition,[],[f37,f359])).
% 1.53/0.62  fof(f359,plain,(
% 1.53/0.62    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.53/0.62    inference(superposition,[],[f58,f56])).
% 1.53/0.62  fof(f56,plain,(
% 1.53/0.62    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 1.53/0.62    inference(definition_unfolding,[],[f25,f50])).
% 1.53/0.62  fof(f25,plain,(
% 1.53/0.62    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.53/0.62    inference(cnf_transformation,[],[f8])).
% 1.53/0.62  fof(f8,axiom,(
% 1.53/0.62    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.53/0.62  fof(f949,plain,(
% 1.53/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X0))) )),
% 1.53/0.62    inference(backward_demodulation,[],[f638,f930])).
% 1.53/0.62  fof(f930,plain,(
% 1.53/0.62    ( ! [X0] : (k3_xboole_0(X0,k3_xboole_0(X0,X0)) = X0) )),
% 1.53/0.62    inference(superposition,[],[f320,f616])).
% 1.53/0.62  fof(f616,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = X1) )),
% 1.53/0.62    inference(superposition,[],[f580,f608])).
% 1.53/0.62  fof(f608,plain,(
% 1.53/0.62    ( ! [X2] : (k3_xboole_0(k3_xboole_0(X2,X2),k3_xboole_0(X2,X2)) = X2) )),
% 1.53/0.62    inference(forward_demodulation,[],[f595,f381])).
% 1.53/0.62  fof(f381,plain,(
% 1.53/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.53/0.62    inference(backward_demodulation,[],[f57,f359])).
% 1.53/0.62  fof(f57,plain,(
% 1.53/0.62    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 1.53/0.62    inference(definition_unfolding,[],[f27,f50])).
% 1.53/0.62  fof(f27,plain,(
% 1.53/0.62    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.53/0.62    inference(cnf_transformation,[],[f18])).
% 1.53/0.62  fof(f18,plain,(
% 1.53/0.62    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.53/0.62    inference(rectify,[],[f5])).
% 1.53/0.62  fof(f5,axiom,(
% 1.53/0.62    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.53/0.62  fof(f595,plain,(
% 1.53/0.62    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = k3_xboole_0(k3_xboole_0(X2,X2),k3_xboole_0(X2,X2))) )),
% 1.53/0.62    inference(superposition,[],[f580,f359])).
% 1.53/0.62  fof(f320,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))) = X1) )),
% 1.53/0.62    inference(resolution,[],[f319,f59])).
% 1.53/0.62  fof(f319,plain,(
% 1.53/0.62    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 1.53/0.62    inference(duplicate_literal_removal,[],[f310])).
% 1.53/0.62  fof(f310,plain,(
% 1.53/0.62    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1) | r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 1.53/0.62    inference(resolution,[],[f82,f35])).
% 1.53/0.62  fof(f35,plain,(
% 1.53/0.62    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f22])).
% 1.53/0.62  fof(f82,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK2(k3_xboole_0(X0,X1),X2),X1) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 1.53/0.62    inference(resolution,[],[f67,f34])).
% 1.53/0.62  fof(f67,plain,(
% 1.53/0.62    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | r2_hidden(X3,X1)) )),
% 1.53/0.62    inference(equality_resolution,[],[f42])).
% 1.53/0.62  fof(f42,plain,(
% 1.53/0.62    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.53/0.62    inference(cnf_transformation,[],[f3])).
% 1.53/0.62  fof(f3,axiom,(
% 1.53/0.62    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.53/0.62  fof(f638,plain,(
% 1.53/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,k3_xboole_0(X0,X0))))) )),
% 1.53/0.62    inference(forward_demodulation,[],[f633,f29])).
% 1.53/0.62  fof(f29,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f1])).
% 1.53/0.62  fof(f1,axiom,(
% 1.53/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.53/0.62  fof(f633,plain,(
% 1.53/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(k3_xboole_0(X0,X0),X0)))) )),
% 1.53/0.62    inference(resolution,[],[f626,f59])).
% 1.53/0.62  fof(f626,plain,(
% 1.53/0.62    ( ! [X20] : (r1_tarski(X20,k3_xboole_0(X20,X20))) )),
% 1.53/0.62    inference(superposition,[],[f319,f608])).
% 1.53/0.62  fof(f990,plain,(
% 1.53/0.62    ( ! [X4,X3] : (k5_xboole_0(X4,k3_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X3,X4))) = X3) )),
% 1.53/0.62    inference(backward_demodulation,[],[f911,f972])).
% 1.53/0.62  fof(f911,plain,(
% 1.53/0.62    ( ! [X4,X3] : (k3_xboole_0(X3,X3) = k5_xboole_0(X4,k3_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X3,X4)))) )),
% 1.53/0.62    inference(forward_demodulation,[],[f888,f381])).
% 1.53/0.62  fof(f888,plain,(
% 1.53/0.62    ( ! [X4,X3] : (k5_xboole_0(k3_xboole_0(X3,X3),k1_xboole_0) = k5_xboole_0(X4,k3_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X3,X4)))) )),
% 1.53/0.62    inference(superposition,[],[f616,f568])).
% 1.53/0.62  fof(f568,plain,(
% 1.53/0.62    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2))))) )),
% 1.53/0.62    inference(superposition,[],[f359,f37])).
% 1.53/0.62  fof(f997,plain,(
% 1.53/0.62    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0)))))),
% 1.53/0.62    inference(backward_demodulation,[],[f865,f972])).
% 1.53/0.62  fof(f865,plain,(
% 1.53/0.62    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK0))))))),
% 1.53/0.62    inference(backward_demodulation,[],[f75,f863])).
% 1.53/0.62  fof(f863,plain,(
% 1.53/0.62    ( ! [X8,X7] : (k3_xboole_0(X7,X7) = k3_xboole_0(X7,k5_xboole_0(X7,k5_xboole_0(X8,k3_xboole_0(X7,X8))))) )),
% 1.53/0.62    inference(forward_demodulation,[],[f839,f381])).
% 1.53/0.62  fof(f839,plain,(
% 1.53/0.62    ( ! [X8,X7] : (k3_xboole_0(X7,k5_xboole_0(X7,k5_xboole_0(X8,k3_xboole_0(X7,X8)))) = k5_xboole_0(k3_xboole_0(X7,X7),k1_xboole_0)) )),
% 1.53/0.62    inference(superposition,[],[f616,f349])).
% 1.53/0.62  fof(f349,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))))) )),
% 1.53/0.62    inference(superposition,[],[f58,f29])).
% 1.53/0.62  fof(f75,plain,(
% 1.53/0.62    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))))))))),
% 1.53/0.62    inference(forward_demodulation,[],[f74,f37])).
% 1.53/0.62  fof(f74,plain,(
% 1.53/0.62    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))))))),
% 1.53/0.62    inference(backward_demodulation,[],[f73,f37])).
% 1.53/0.62  fof(f73,plain,(
% 1.53/0.62    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))))))),
% 1.53/0.62    inference(forward_demodulation,[],[f72,f29])).
% 1.53/0.62  fof(f72,plain,(
% 1.53/0.62    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k1_tarski(sK0))))),
% 1.53/0.62    inference(backward_demodulation,[],[f54,f29])).
% 1.53/0.62  fof(f54,plain,(
% 1.53/0.62    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0))))),
% 1.53/0.62    inference(definition_unfolding,[],[f23,f51,f52])).
% 1.53/0.62  fof(f52,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0))))) )),
% 1.53/0.62    inference(definition_unfolding,[],[f36,f50,f51])).
% 1.53/0.62  fof(f36,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.53/0.62    inference(cnf_transformation,[],[f14])).
% 1.53/0.62  fof(f14,axiom,(
% 1.53/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 1.53/0.62  fof(f51,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0))))) )),
% 1.53/0.62    inference(definition_unfolding,[],[f30,f50])).
% 1.53/0.62  fof(f30,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.53/0.62    inference(cnf_transformation,[],[f13])).
% 1.53/0.62  fof(f13,axiom,(
% 1.53/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 1.53/0.62  fof(f23,plain,(
% 1.53/0.62    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 1.53/0.62    inference(cnf_transformation,[],[f20])).
% 1.53/0.62  fof(f20,plain,(
% 1.53/0.62    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 1.53/0.62    inference(ennf_transformation,[],[f17])).
% 1.53/0.62  fof(f17,negated_conjecture,(
% 1.53/0.62    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.53/0.62    inference(negated_conjecture,[],[f16])).
% 1.53/0.62  fof(f16,conjecture,(
% 1.53/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.53/0.62  % SZS output end Proof for theBenchmark
% 1.53/0.62  % (22146)------------------------------
% 1.53/0.62  % (22146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.62  % (22146)Termination reason: Refutation
% 1.53/0.62  
% 1.53/0.62  % (22146)Memory used [KB]: 6908
% 1.53/0.62  % (22146)Time elapsed: 0.185 s
% 1.53/0.62  % (22146)------------------------------
% 1.53/0.62  % (22146)------------------------------
% 1.53/0.62  % (22134)Success in time 0.249 s
%------------------------------------------------------------------------------
