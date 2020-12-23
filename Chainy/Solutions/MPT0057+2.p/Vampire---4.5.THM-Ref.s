%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0057+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:06 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   34 (  67 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   35 (  68 expanded)
%              Number of equality atoms :   34 (  67 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1120,plain,(
    $false ),
    inference(subsumption_resolution,[],[f919,f1119])).

fof(f1119,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X4)))) ),
    inference(backward_demodulation,[],[f410,f1118])).

fof(f1118,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))))) ),
    inference(forward_demodulation,[],[f1117,f171])).

fof(f171,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f134,f142,f142])).

fof(f142,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f134,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f1117,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))))) ),
    inference(forward_demodulation,[],[f1116,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1116,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)))) ),
    inference(forward_demodulation,[],[f1061,f155])).

fof(f1061,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),X2))) ),
    inference(superposition,[],[f171,f158])).

fof(f158,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f410,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4)))))) ),
    inference(forward_demodulation,[],[f409,f155])).

fof(f409,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(k4_xboole_0(X2,X3),X4))))) ),
    inference(forward_demodulation,[],[f384,f155])).

fof(f384,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),X4)))) ),
    inference(superposition,[],[f179,f155])).

fof(f179,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f143,f142])).

fof(f143,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f919,plain,(
    k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) != k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) ),
    inference(superposition,[],[f191,f155])).

fof(f191,plain,(
    k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) != k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f161,f188])).

fof(f188,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f176,f155])).

fof(f176,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f139,f142,f142])).

fof(f139,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f161,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(definition_unfolding,[],[f124,f142,f142,f142])).

fof(f124,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f121])).

fof(f121,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f101,f120])).

fof(f120,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f91])).

fof(f91,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f90])).

fof(f90,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).
%------------------------------------------------------------------------------
