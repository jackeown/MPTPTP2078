%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:40 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  144 (1407 expanded)
%              Number of leaves         :   14 ( 464 expanded)
%              Depth                    :   37
%              Number of atoms          :  179 (1528 expanded)
%              Number of equality atoms :   95 (1253 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :   12 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1505,plain,(
    $false ),
    inference(resolution,[],[f1502,f181])).

fof(f181,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f105,f96])).

fof(f96,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X0,X1)),X1) ),
    inference(backward_demodulation,[],[f68,f94])).

fof(f94,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f85,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f85,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f60,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f34,f24])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(X0,X1))),X1) ),
    inference(backward_demodulation,[],[f50,f60])).

fof(f50,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),X1) ),
    inference(backward_demodulation,[],[f39,f34])).

fof(f39,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f26,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f105,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k5_xboole_0(sK2,k2_xboole_0(sK1,sK2)),X0)
      | r1_xboole_0(sK0,X0) ) ),
    inference(backward_demodulation,[],[f72,f94])).

fof(f72,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2))),X0)
      | r1_xboole_0(sK0,X0) ) ),
    inference(backward_demodulation,[],[f58,f60])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2)))),X0)
      | r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f45,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f45,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2))))) ),
    inference(backward_demodulation,[],[f38,f34])).

fof(f38,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)))) ),
    inference(definition_unfolding,[],[f22,f37])).

fof(f22,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f1502,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f1418,f23])).

fof(f23,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f1418,plain,(
    r1_tarski(sK0,sK1) ),
    inference(forward_demodulation,[],[f1417,f25])).

fof(f1417,plain,(
    r1_tarski(k5_xboole_0(sK0,k1_xboole_0),sK1) ),
    inference(forward_demodulation,[],[f1409,f24])).

fof(f1409,plain,(
    r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),sK1) ),
    inference(superposition,[],[f102,f1038])).

fof(f1038,plain,(
    sK1 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f813,f995])).

fof(f995,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(backward_demodulation,[],[f159,f975])).

fof(f975,plain,(
    ! [X3] : k2_xboole_0(k1_xboole_0,k2_xboole_0(X3,k1_xboole_0)) = X3 ),
    inference(backward_demodulation,[],[f151,f974])).

fof(f974,plain,(
    ! [X2] : k2_xboole_0(k1_xboole_0,X2) = X2 ),
    inference(resolution,[],[f966,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f966,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f504,f962])).

fof(f962,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X1))) = X0 ),
    inference(forward_demodulation,[],[f961,f101])).

fof(f101,plain,(
    ! [X4,X3] : k2_xboole_0(k5_xboole_0(X3,k2_xboole_0(X4,X3)),X4) = X4 ),
    inference(backward_demodulation,[],[f83,f94])).

fof(f83,plain,(
    ! [X4,X3] : k2_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k2_xboole_0(X4,X3))),X4) = X4 ),
    inference(resolution,[],[f69,f31])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(X0,X1))),X0) ),
    inference(backward_demodulation,[],[f49,f60])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),X0) ),
    inference(backward_demodulation,[],[f40,f34])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f961,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X1))) = k2_xboole_0(k5_xboole_0(X1,k2_xboole_0(X0,X1)),X0) ),
    inference(backward_demodulation,[],[f282,f960])).

fof(f960,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = X2 ),
    inference(resolution,[],[f958,f31])).

fof(f958,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(forward_demodulation,[],[f889,f25])).

fof(f889,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[],[f156,f24])).

fof(f156,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X1))),X0) ),
    inference(forward_demodulation,[],[f152,f34])).

fof(f152,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),X0) ),
    inference(superposition,[],[f97,f98])).

fof(f98,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f70,f94])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k2_xboole_0(X1,X0)))) ),
    inference(backward_demodulation,[],[f48,f60])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k2_xboole_0(X1,X0))))) ),
    inference(backward_demodulation,[],[f41,f34])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f97,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X1,k2_xboole_0(X0,X1)),X0) ),
    inference(backward_demodulation,[],[f69,f94])).

fof(f282,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X1))) = k2_xboole_0(k5_xboole_0(X1,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f281,f95])).

fof(f95,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f60,f94])).

fof(f281,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X1))) = k2_xboole_0(k5_xboole_0(X1,k2_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X0,X0)))) ),
    inference(forward_demodulation,[],[f240,f95])).

fof(f240,plain,(
    ! [X0,X1] : k2_xboole_0(k5_xboole_0(X1,k2_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X0,X0)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X1))))) ),
    inference(superposition,[],[f107,f98])).

fof(f107,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k5_xboole_0(X1,k2_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X1,X2))))))) ),
    inference(forward_demodulation,[],[f99,f94])).

fof(f99,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k2_xboole_0(X1,X2)))))))) = k2_xboole_0(k5_xboole_0(X1,k2_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) ),
    inference(backward_demodulation,[],[f76,f94])).

fof(f76,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k2_xboole_0(X1,X2)))))))) ),
    inference(backward_demodulation,[],[f75,f61])).

fof(f61,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(X2,X3) ),
    inference(superposition,[],[f34,f25])).

fof(f75,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k2_xboole_0(X1,X2))))))))) ),
    inference(forward_demodulation,[],[f74,f60])).

fof(f74,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))))))))) ),
    inference(forward_demodulation,[],[f67,f60])).

fof(f67,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))))))))) = k2_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) ),
    inference(backward_demodulation,[],[f57,f60])).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))))))))) ),
    inference(forward_demodulation,[],[f56,f34])).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))))))))) ),
    inference(forward_demodulation,[],[f55,f34])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))))))))) ),
    inference(forward_demodulation,[],[f54,f34])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))))))) ),
    inference(forward_demodulation,[],[f53,f34])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))))))) ),
    inference(forward_demodulation,[],[f52,f34])).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))))) = k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) ),
    inference(forward_demodulation,[],[f51,f34])).

fof(f51,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))))) = k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) ),
    inference(forward_demodulation,[],[f44,f34])).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))))) = k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),k5_xboole_0(k5_xboole_0(X0,X2),k2_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f35,f37,f37,f37,f30])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f504,plain,(
    ! [X0,X1] : r1_tarski(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X1)))) ),
    inference(backward_demodulation,[],[f451,f476])).

fof(f476,plain,(
    ! [X14,X15,X16] : k5_xboole_0(X14,k5_xboole_0(X15,X16)) = k5_xboole_0(X16,k5_xboole_0(X14,X15)) ),
    inference(superposition,[],[f357,f34])).

fof(f357,plain,(
    ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(superposition,[],[f95,f341])).

fof(f341,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f327,f25])).

fof(f327,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f95,f63])).

fof(f63,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f34,f24])).

fof(f451,plain,(
    ! [X0,X1] : r1_tarski(k1_xboole_0,k5_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(X0,k2_xboole_0(X1,X0)))) ),
    inference(forward_demodulation,[],[f441,f357])).

fof(f441,plain,(
    ! [X0,X1] : r1_tarski(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(X1,X0)),k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f433,f98])).

fof(f433,plain,(
    ! [X6,X5] : r1_tarski(k1_xboole_0,k5_xboole_0(X5,k2_xboole_0(X6,X5))) ),
    inference(forward_demodulation,[],[f408,f24])).

fof(f408,plain,(
    ! [X6,X5] : r1_tarski(k5_xboole_0(X6,X6),k5_xboole_0(X5,k2_xboole_0(X6,X5))) ),
    inference(superposition,[],[f97,f101])).

fof(f151,plain,(
    ! [X3] : k2_xboole_0(k1_xboole_0,X3) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X3,k1_xboole_0)) ),
    inference(superposition,[],[f98,f94])).

fof(f159,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,k1_xboole_0)) ),
    inference(resolution,[],[f146,f31])).

fof(f146,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f142,f24])).

fof(f142,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,X0),k2_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f97,f128])).

fof(f128,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(X2,k1_xboole_0),X2) = X2 ),
    inference(resolution,[],[f126,f31])).

fof(f126,plain,(
    ! [X3] : r1_tarski(k2_xboole_0(X3,k1_xboole_0),X3) ),
    inference(superposition,[],[f97,f94])).

fof(f813,plain,(
    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k5_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f804,f24])).

fof(f804,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK1,k5_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0))) ),
    inference(superposition,[],[f98,f738])).

fof(f738,plain,(
    sK1 = k2_xboole_0(k5_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0)),sK1) ),
    inference(superposition,[],[f101,f701])).

fof(f701,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f98,f688])).

fof(f688,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f687,f162])).

fof(f162,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f160,f31])).

fof(f160,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f146,f128])).

fof(f687,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f686,f24])).

fof(f686,plain,(
    k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f671,f419])).

fof(f419,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k2_xboole_0(X3,X2)) = k2_xboole_0(k1_xboole_0,k5_xboole_0(X2,k2_xboole_0(X3,X2))) ),
    inference(forward_demodulation,[],[f399,f24])).

fof(f399,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k2_xboole_0(X3,X2)) = k2_xboole_0(k5_xboole_0(X3,X3),k5_xboole_0(X2,k2_xboole_0(X3,X2))) ),
    inference(superposition,[],[f101,f101])).

fof(f671,plain,(
    k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f98,f649])).

fof(f649,plain,(
    k1_xboole_0 = k2_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f648,f24])).

fof(f648,plain,(
    k1_xboole_0 = k2_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)),k5_xboole_0(sK2,sK2)) ),
    inference(forward_demodulation,[],[f647,f366])).

fof(f366,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5))) ),
    inference(forward_demodulation,[],[f358,f34])).

fof(f358,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5)) ),
    inference(superposition,[],[f34,f341])).

fof(f647,plain,(
    k1_xboole_0 = k2_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK0,sK2)))) ),
    inference(forward_demodulation,[],[f646,f365])).

fof(f365,plain,(
    k2_xboole_0(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f191,f357])).

fof(f191,plain,(
    k2_xboole_0(sK0,sK2) = k5_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f95,f185])).

fof(f185,plain,(
    sK0 = k5_xboole_0(sK2,k2_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f183,f25])).

fof(f183,plain,(
    k5_xboole_0(sK2,k2_xboole_0(sK0,sK2)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f95,f182])).

fof(f182,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK2,k2_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f181,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) ) ),
    inference(backward_demodulation,[],[f43,f34])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f646,plain,(
    k1_xboole_0 = k2_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK2,k2_xboole_0(sK0,sK2)))) ),
    inference(forward_demodulation,[],[f645,f24])).

fof(f645,plain,(
    k2_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK2,k2_xboole_0(sK0,sK2)))) = k5_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f644,f366])).

fof(f644,plain,(
    k2_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK2,k2_xboole_0(sK0,sK2)))) = k5_xboole_0(sK2,k5_xboole_0(k2_xboole_0(sK1,sK2),k5_xboole_0(sK2,k2_xboole_0(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f635,f95])).

fof(f635,plain,(
    k2_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK2,k2_xboole_0(sK0,sK2)))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(k2_xboole_0(sK1,sK2),k5_xboole_0(sK2,k2_xboole_0(sK1,sK2)))))) ),
    inference(superposition,[],[f107,f106])).

fof(f106,plain,(
    k5_xboole_0(sK2,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f71,f94])).

fof(f71,plain,(
    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2)))) ),
    inference(backward_demodulation,[],[f59,f60])).

fof(f59,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2)))) = k2_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2))))) ),
    inference(resolution,[],[f45,f31])).

fof(f102,plain,(
    ! [X2,X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X0,X1)))),X2) ),
    inference(backward_demodulation,[],[f84,f94])).

fof(f84,plain,(
    ! [X2,X0,X1] : r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X0,X1))))),X2) ),
    inference(superposition,[],[f69,f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:57:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (29563)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (29550)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (29554)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (29555)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (29558)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (29556)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (29564)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (29549)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (29562)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (29566)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (29561)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (29559)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (29557)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (29551)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (29552)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (29560)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (29565)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (29553)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 1.21/0.52  % (29550)Refutation found. Thanks to Tanya!
% 1.21/0.52  % SZS status Theorem for theBenchmark
% 1.21/0.53  % SZS output start Proof for theBenchmark
% 1.21/0.53  fof(f1505,plain,(
% 1.21/0.53    $false),
% 1.21/0.53    inference(resolution,[],[f1502,f181])).
% 1.21/0.53  fof(f181,plain,(
% 1.21/0.53    r1_xboole_0(sK0,sK2)),
% 1.21/0.53    inference(resolution,[],[f105,f96])).
% 1.21/0.53  fof(f96,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X0,X1)),X1)) )),
% 1.21/0.53    inference(backward_demodulation,[],[f68,f94])).
% 1.21/0.53  fof(f94,plain,(
% 1.21/0.53    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.21/0.53    inference(forward_demodulation,[],[f85,f25])).
% 1.21/0.53  fof(f25,plain,(
% 1.21/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.21/0.53    inference(cnf_transformation,[],[f7])).
% 1.21/0.53  fof(f7,axiom,(
% 1.21/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.21/0.53  fof(f85,plain,(
% 1.21/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.21/0.53    inference(superposition,[],[f60,f24])).
% 1.21/0.53  fof(f24,plain,(
% 1.21/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f11])).
% 1.21/0.53  fof(f11,axiom,(
% 1.21/0.53    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.21/0.53  fof(f60,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.21/0.53    inference(superposition,[],[f34,f24])).
% 1.21/0.53  fof(f34,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.21/0.53    inference(cnf_transformation,[],[f10])).
% 1.21/0.53  fof(f10,axiom,(
% 1.21/0.53    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.21/0.53  fof(f68,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(X0,X1))),X1)) )),
% 1.21/0.53    inference(backward_demodulation,[],[f50,f60])).
% 1.21/0.53  fof(f50,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),X1)) )),
% 1.21/0.53    inference(backward_demodulation,[],[f39,f34])).
% 1.21/0.53  fof(f39,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),X1)) )),
% 1.21/0.53    inference(definition_unfolding,[],[f26,f37])).
% 1.21/0.53  fof(f37,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 1.21/0.53    inference(definition_unfolding,[],[f29,f30])).
% 1.21/0.53  fof(f30,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.21/0.53    inference(cnf_transformation,[],[f12])).
% 1.21/0.53  fof(f12,axiom,(
% 1.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.21/0.53  fof(f29,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.21/0.53    inference(cnf_transformation,[],[f2])).
% 1.21/0.53  fof(f2,axiom,(
% 1.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.21/0.53  fof(f26,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f9])).
% 1.21/0.53  fof(f9,axiom,(
% 1.21/0.53    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.21/0.53  fof(f105,plain,(
% 1.21/0.53    ( ! [X0] : (~r1_xboole_0(k5_xboole_0(sK2,k2_xboole_0(sK1,sK2)),X0) | r1_xboole_0(sK0,X0)) )),
% 1.21/0.53    inference(backward_demodulation,[],[f72,f94])).
% 1.21/0.53  fof(f72,plain,(
% 1.21/0.53    ( ! [X0] : (~r1_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2))),X0) | r1_xboole_0(sK0,X0)) )),
% 1.21/0.53    inference(backward_demodulation,[],[f58,f60])).
% 1.21/0.53  fof(f58,plain,(
% 1.21/0.53    ( ! [X0] : (~r1_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2)))),X0) | r1_xboole_0(sK0,X0)) )),
% 1.21/0.53    inference(resolution,[],[f45,f36])).
% 1.21/0.53  fof(f36,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f18])).
% 1.21/0.53  fof(f18,plain,(
% 1.21/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.21/0.53    inference(flattening,[],[f17])).
% 1.21/0.53  fof(f17,plain,(
% 1.21/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.21/0.53    inference(ennf_transformation,[],[f8])).
% 1.21/0.53  fof(f8,axiom,(
% 1.21/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.21/0.53  fof(f45,plain,(
% 1.21/0.53    r1_tarski(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2)))))),
% 1.21/0.53    inference(backward_demodulation,[],[f38,f34])).
% 1.21/0.53  fof(f38,plain,(
% 1.21/0.53    r1_tarski(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))))),
% 1.21/0.53    inference(definition_unfolding,[],[f22,f37])).
% 1.21/0.53  fof(f22,plain,(
% 1.21/0.53    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.21/0.53    inference(cnf_transformation,[],[f20])).
% 1.21/0.53  fof(f20,plain,(
% 1.21/0.53    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f19])).
% 1.21/0.53  fof(f19,plain,(
% 1.21/0.53    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 1.21/0.53    introduced(choice_axiom,[])).
% 1.21/0.53  fof(f15,plain,(
% 1.21/0.53    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.21/0.53    inference(ennf_transformation,[],[f14])).
% 1.21/0.53  fof(f14,negated_conjecture,(
% 1.21/0.53    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.21/0.53    inference(negated_conjecture,[],[f13])).
% 1.21/0.53  fof(f13,conjecture,(
% 1.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.21/0.53  fof(f1502,plain,(
% 1.21/0.53    ~r1_xboole_0(sK0,sK2)),
% 1.21/0.53    inference(resolution,[],[f1418,f23])).
% 1.21/0.53  fof(f23,plain,(
% 1.21/0.53    ~r1_tarski(sK0,sK1) | ~r1_xboole_0(sK0,sK2)),
% 1.21/0.53    inference(cnf_transformation,[],[f20])).
% 1.21/0.53  fof(f1418,plain,(
% 1.21/0.53    r1_tarski(sK0,sK1)),
% 1.21/0.53    inference(forward_demodulation,[],[f1417,f25])).
% 1.21/0.53  fof(f1417,plain,(
% 1.21/0.53    r1_tarski(k5_xboole_0(sK0,k1_xboole_0),sK1)),
% 1.21/0.53    inference(forward_demodulation,[],[f1409,f24])).
% 1.21/0.53  fof(f1409,plain,(
% 1.21/0.53    r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),sK1)),
% 1.21/0.53    inference(superposition,[],[f102,f1038])).
% 1.21/0.53  fof(f1038,plain,(
% 1.21/0.53    sK1 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.21/0.53    inference(backward_demodulation,[],[f813,f995])).
% 1.21/0.53  fof(f995,plain,(
% 1.21/0.53    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.21/0.53    inference(backward_demodulation,[],[f159,f975])).
% 1.21/0.53  fof(f975,plain,(
% 1.21/0.53    ( ! [X3] : (k2_xboole_0(k1_xboole_0,k2_xboole_0(X3,k1_xboole_0)) = X3) )),
% 1.21/0.53    inference(backward_demodulation,[],[f151,f974])).
% 1.21/0.53  fof(f974,plain,(
% 1.21/0.53    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = X2) )),
% 1.21/0.53    inference(resolution,[],[f966,f31])).
% 1.21/0.53  fof(f31,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.21/0.53    inference(cnf_transformation,[],[f16])).
% 1.21/0.53  fof(f16,plain,(
% 1.21/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.21/0.53    inference(ennf_transformation,[],[f3])).
% 1.21/0.53  fof(f3,axiom,(
% 1.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.21/0.53  fof(f966,plain,(
% 1.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.21/0.53    inference(backward_demodulation,[],[f504,f962])).
% 1.21/0.53  fof(f962,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X1))) = X0) )),
% 1.21/0.53    inference(forward_demodulation,[],[f961,f101])).
% 1.21/0.53  fof(f101,plain,(
% 1.21/0.53    ( ! [X4,X3] : (k2_xboole_0(k5_xboole_0(X3,k2_xboole_0(X4,X3)),X4) = X4) )),
% 1.21/0.53    inference(backward_demodulation,[],[f83,f94])).
% 1.21/0.53  fof(f83,plain,(
% 1.21/0.53    ( ! [X4,X3] : (k2_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k2_xboole_0(X4,X3))),X4) = X4) )),
% 1.21/0.53    inference(resolution,[],[f69,f31])).
% 1.21/0.53  fof(f69,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(X0,X1))),X0)) )),
% 1.21/0.53    inference(backward_demodulation,[],[f49,f60])).
% 1.21/0.53  fof(f49,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),X0)) )),
% 1.21/0.53    inference(backward_demodulation,[],[f40,f34])).
% 1.21/0.53  fof(f40,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),X0)) )),
% 1.21/0.53    inference(definition_unfolding,[],[f27,f37])).
% 1.21/0.53  fof(f27,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f4])).
% 1.21/0.53  fof(f4,axiom,(
% 1.21/0.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.21/0.53  fof(f961,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X1))) = k2_xboole_0(k5_xboole_0(X1,k2_xboole_0(X0,X1)),X0)) )),
% 1.21/0.53    inference(backward_demodulation,[],[f282,f960])).
% 1.21/0.53  fof(f960,plain,(
% 1.21/0.53    ( ! [X2] : (k2_xboole_0(X2,X2) = X2) )),
% 1.21/0.53    inference(resolution,[],[f958,f31])).
% 1.21/0.53  fof(f958,plain,(
% 1.21/0.53    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.21/0.53    inference(forward_demodulation,[],[f889,f25])).
% 1.21/0.53  fof(f889,plain,(
% 1.21/0.53    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0)) )),
% 1.21/0.53    inference(superposition,[],[f156,f24])).
% 1.21/0.53  fof(f156,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X1))),X0)) )),
% 1.21/0.53    inference(forward_demodulation,[],[f152,f34])).
% 1.21/0.53  fof(f152,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(X1,X0)),k2_xboole_0(X0,X1)),X0)) )),
% 1.21/0.53    inference(superposition,[],[f97,f98])).
% 1.21/0.53  fof(f98,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X1,X0)))) )),
% 1.21/0.53    inference(backward_demodulation,[],[f70,f94])).
% 1.21/0.53  fof(f70,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k2_xboole_0(X1,X0))))) )),
% 1.21/0.53    inference(backward_demodulation,[],[f48,f60])).
% 1.21/0.53  fof(f48,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k2_xboole_0(X1,X0)))))) )),
% 1.21/0.53    inference(backward_demodulation,[],[f41,f34])).
% 1.21/0.53  fof(f41,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0))))) )),
% 1.21/0.53    inference(definition_unfolding,[],[f28,f37])).
% 1.21/0.53  fof(f28,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.21/0.53    inference(cnf_transformation,[],[f5])).
% 1.21/0.53  fof(f5,axiom,(
% 1.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.21/0.53  fof(f97,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X1,k2_xboole_0(X0,X1)),X0)) )),
% 1.21/0.53    inference(backward_demodulation,[],[f69,f94])).
% 1.21/0.53  fof(f282,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X1))) = k2_xboole_0(k5_xboole_0(X1,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X0))) )),
% 1.21/0.53    inference(forward_demodulation,[],[f281,f95])).
% 1.21/0.53  fof(f95,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.21/0.53    inference(backward_demodulation,[],[f60,f94])).
% 1.21/0.53  fof(f281,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X1))) = k2_xboole_0(k5_xboole_0(X1,k2_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X0,X0))))) )),
% 1.21/0.53    inference(forward_demodulation,[],[f240,f95])).
% 1.21/0.53  fof(f240,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k2_xboole_0(k5_xboole_0(X1,k2_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X0,X0)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X1)))))) )),
% 1.21/0.53    inference(superposition,[],[f107,f98])).
% 1.21/0.53  fof(f107,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k5_xboole_0(X1,k2_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X1,X2)))))))) )),
% 1.21/0.53    inference(forward_demodulation,[],[f99,f94])).
% 1.21/0.53  fof(f99,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k2_xboole_0(X1,X2)))))))) = k2_xboole_0(k5_xboole_0(X1,k2_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2))))) )),
% 1.21/0.53    inference(backward_demodulation,[],[f76,f94])).
% 1.21/0.53  fof(f76,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k2_xboole_0(X1,X2))))))))) )),
% 1.21/0.53    inference(backward_demodulation,[],[f75,f61])).
% 1.21/0.53  fof(f61,plain,(
% 1.21/0.53    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(X2,X3)) )),
% 1.21/0.53    inference(superposition,[],[f34,f25])).
% 1.21/0.53  fof(f75,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k2_xboole_0(X1,X2)))))))))) )),
% 1.21/0.53    inference(forward_demodulation,[],[f74,f60])).
% 1.21/0.53  fof(f74,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))))))))) )),
% 1.21/0.53    inference(forward_demodulation,[],[f67,f60])).
% 1.21/0.53  fof(f67,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))))))))) = k2_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2))))) )),
% 1.21/0.53    inference(backward_demodulation,[],[f57,f60])).
% 1.21/0.53  fof(f57,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))))))))))) )),
% 1.21/0.53    inference(forward_demodulation,[],[f56,f34])).
% 1.21/0.53  fof(f56,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))))))))))) )),
% 1.21/0.53    inference(forward_demodulation,[],[f55,f34])).
% 1.21/0.53  fof(f55,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))))))))) )),
% 1.21/0.53    inference(forward_demodulation,[],[f54,f34])).
% 1.21/0.53  fof(f54,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))))))))) )),
% 1.21/0.53    inference(forward_demodulation,[],[f53,f34])).
% 1.21/0.53  fof(f53,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))))))) )),
% 1.21/0.53    inference(forward_demodulation,[],[f52,f34])).
% 1.21/0.53  fof(f52,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))))) = k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2))))) )),
% 1.21/0.53    inference(forward_demodulation,[],[f51,f34])).
% 1.21/0.53  fof(f51,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))))) = k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X2,k2_xboole_0(X0,X2))))) )),
% 1.21/0.53    inference(forward_demodulation,[],[f44,f34])).
% 1.21/0.53  fof(f44,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))),k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))))) = k2_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),k5_xboole_0(k5_xboole_0(X0,X2),k2_xboole_0(X0,X2)))) )),
% 1.21/0.53    inference(definition_unfolding,[],[f35,f37,f37,f37,f30])).
% 1.21/0.53  fof(f35,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.21/0.53    inference(cnf_transformation,[],[f6])).
% 1.21/0.53  fof(f6,axiom,(
% 1.21/0.53    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.21/0.53  fof(f504,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X1))))) )),
% 1.21/0.53    inference(backward_demodulation,[],[f451,f476])).
% 1.21/0.53  fof(f476,plain,(
% 1.21/0.53    ( ! [X14,X15,X16] : (k5_xboole_0(X14,k5_xboole_0(X15,X16)) = k5_xboole_0(X16,k5_xboole_0(X14,X15))) )),
% 1.21/0.53    inference(superposition,[],[f357,f34])).
% 1.21/0.53  fof(f357,plain,(
% 1.21/0.53    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) )),
% 1.21/0.53    inference(superposition,[],[f95,f341])).
% 1.21/0.53  fof(f341,plain,(
% 1.21/0.53    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 1.21/0.53    inference(forward_demodulation,[],[f327,f25])).
% 1.21/0.53  fof(f327,plain,(
% 1.21/0.53    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 1.21/0.53    inference(superposition,[],[f95,f63])).
% 1.21/0.53  fof(f63,plain,(
% 1.21/0.53    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 1.21/0.53    inference(superposition,[],[f34,f24])).
% 1.21/0.53  fof(f451,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_xboole_0,k5_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(X0,k2_xboole_0(X1,X0))))) )),
% 1.21/0.53    inference(forward_demodulation,[],[f441,f357])).
% 1.21/0.53  fof(f441,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(X1,X0)),k2_xboole_0(X0,X1)))) )),
% 1.21/0.53    inference(superposition,[],[f433,f98])).
% 1.21/0.53  fof(f433,plain,(
% 1.21/0.53    ( ! [X6,X5] : (r1_tarski(k1_xboole_0,k5_xboole_0(X5,k2_xboole_0(X6,X5)))) )),
% 1.21/0.53    inference(forward_demodulation,[],[f408,f24])).
% 1.21/0.53  fof(f408,plain,(
% 1.21/0.53    ( ! [X6,X5] : (r1_tarski(k5_xboole_0(X6,X6),k5_xboole_0(X5,k2_xboole_0(X6,X5)))) )),
% 1.21/0.53    inference(superposition,[],[f97,f101])).
% 1.21/0.53  fof(f151,plain,(
% 1.21/0.53    ( ! [X3] : (k2_xboole_0(k1_xboole_0,X3) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X3,k1_xboole_0))) )),
% 1.21/0.53    inference(superposition,[],[f98,f94])).
% 1.21/0.53  fof(f159,plain,(
% 1.21/0.53    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,k1_xboole_0))) )),
% 1.21/0.53    inference(resolution,[],[f146,f31])).
% 1.21/0.53  fof(f146,plain,(
% 1.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0))) )),
% 1.21/0.53    inference(forward_demodulation,[],[f142,f24])).
% 1.21/0.53  fof(f142,plain,(
% 1.21/0.53    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,X0),k2_xboole_0(X0,k1_xboole_0))) )),
% 1.21/0.53    inference(superposition,[],[f97,f128])).
% 1.21/0.53  fof(f128,plain,(
% 1.21/0.53    ( ! [X2] : (k2_xboole_0(k2_xboole_0(X2,k1_xboole_0),X2) = X2) )),
% 1.21/0.53    inference(resolution,[],[f126,f31])).
% 1.21/0.53  fof(f126,plain,(
% 1.21/0.53    ( ! [X3] : (r1_tarski(k2_xboole_0(X3,k1_xboole_0),X3)) )),
% 1.21/0.53    inference(superposition,[],[f97,f94])).
% 1.21/0.53  fof(f813,plain,(
% 1.21/0.53    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k5_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0)))),
% 1.21/0.53    inference(forward_demodulation,[],[f804,f24])).
% 1.21/0.53  fof(f804,plain,(
% 1.21/0.53    k2_xboole_0(sK1,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK1,k5_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0)))),
% 1.21/0.53    inference(superposition,[],[f98,f738])).
% 1.21/0.53  fof(f738,plain,(
% 1.21/0.53    sK1 = k2_xboole_0(k5_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0)),sK1)),
% 1.21/0.53    inference(superposition,[],[f101,f701])).
% 1.21/0.53  fof(f701,plain,(
% 1.21/0.53    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)),
% 1.21/0.53    inference(superposition,[],[f98,f688])).
% 1.21/0.53  fof(f688,plain,(
% 1.21/0.53    k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 1.21/0.53    inference(forward_demodulation,[],[f687,f162])).
% 1.21/0.53  fof(f162,plain,(
% 1.21/0.53    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.21/0.53    inference(resolution,[],[f160,f31])).
% 1.21/0.53  fof(f160,plain,(
% 1.21/0.53    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.21/0.53    inference(superposition,[],[f146,f128])).
% 1.21/0.53  fof(f687,plain,(
% 1.21/0.53    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 1.21/0.53    inference(forward_demodulation,[],[f686,f24])).
% 1.21/0.53  fof(f686,plain,(
% 1.21/0.53    k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 1.21/0.53    inference(forward_demodulation,[],[f671,f419])).
% 1.21/0.53  fof(f419,plain,(
% 1.21/0.53    ( ! [X2,X3] : (k5_xboole_0(X2,k2_xboole_0(X3,X2)) = k2_xboole_0(k1_xboole_0,k5_xboole_0(X2,k2_xboole_0(X3,X2)))) )),
% 1.21/0.53    inference(forward_demodulation,[],[f399,f24])).
% 1.21/0.53  fof(f399,plain,(
% 1.21/0.53    ( ! [X2,X3] : (k5_xboole_0(X2,k2_xboole_0(X3,X2)) = k2_xboole_0(k5_xboole_0(X3,X3),k5_xboole_0(X2,k2_xboole_0(X3,X2)))) )),
% 1.21/0.53    inference(superposition,[],[f101,f101])).
% 1.21/0.53  fof(f671,plain,(
% 1.21/0.53    k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))),
% 1.21/0.53    inference(superposition,[],[f98,f649])).
% 1.21/0.53  fof(f649,plain,(
% 1.21/0.53    k1_xboole_0 = k2_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)),k1_xboole_0)),
% 1.21/0.53    inference(forward_demodulation,[],[f648,f24])).
% 1.21/0.53  fof(f648,plain,(
% 1.21/0.53    k1_xboole_0 = k2_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)),k5_xboole_0(sK2,sK2))),
% 1.21/0.53    inference(forward_demodulation,[],[f647,f366])).
% 1.21/0.53  fof(f366,plain,(
% 1.21/0.53    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))) )),
% 1.21/0.53    inference(forward_demodulation,[],[f358,f34])).
% 1.21/0.53  fof(f358,plain,(
% 1.21/0.53    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5))) )),
% 1.21/0.53    inference(superposition,[],[f34,f341])).
% 1.21/0.53  fof(f647,plain,(
% 1.21/0.53    k1_xboole_0 = k2_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK0,sK2))))),
% 1.21/0.53    inference(forward_demodulation,[],[f646,f365])).
% 1.21/0.53  fof(f365,plain,(
% 1.21/0.53    k2_xboole_0(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 1.21/0.53    inference(backward_demodulation,[],[f191,f357])).
% 1.21/0.53  fof(f191,plain,(
% 1.21/0.53    k2_xboole_0(sK0,sK2) = k5_xboole_0(sK2,sK0)),
% 1.21/0.53    inference(superposition,[],[f95,f185])).
% 1.21/0.53  fof(f185,plain,(
% 1.21/0.53    sK0 = k5_xboole_0(sK2,k2_xboole_0(sK0,sK2))),
% 1.21/0.53    inference(forward_demodulation,[],[f183,f25])).
% 1.21/0.53  fof(f183,plain,(
% 1.21/0.53    k5_xboole_0(sK2,k2_xboole_0(sK0,sK2)) = k5_xboole_0(sK0,k1_xboole_0)),
% 1.21/0.53    inference(superposition,[],[f95,f182])).
% 1.21/0.53  fof(f182,plain,(
% 1.21/0.53    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK2,k2_xboole_0(sK0,sK2)))),
% 1.21/0.53    inference(resolution,[],[f181,f46])).
% 1.21/0.53  fof(f46,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 1.21/0.53    inference(backward_demodulation,[],[f43,f34])).
% 1.21/0.53  fof(f43,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.21/0.53    inference(definition_unfolding,[],[f32,f30])).
% 1.21/0.53  fof(f32,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f21])).
% 1.21/0.53  fof(f21,plain,(
% 1.21/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.21/0.53    inference(nnf_transformation,[],[f1])).
% 1.21/0.53  fof(f1,axiom,(
% 1.21/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.21/0.53  fof(f646,plain,(
% 1.21/0.53    k1_xboole_0 = k2_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK2,k2_xboole_0(sK0,sK2))))),
% 1.21/0.53    inference(forward_demodulation,[],[f645,f24])).
% 1.21/0.53  fof(f645,plain,(
% 1.21/0.53    k2_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK2,k2_xboole_0(sK0,sK2)))) = k5_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))),
% 1.21/0.53    inference(forward_demodulation,[],[f644,f366])).
% 1.21/0.53  fof(f644,plain,(
% 1.21/0.53    k2_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK2,k2_xboole_0(sK0,sK2)))) = k5_xboole_0(sK2,k5_xboole_0(k2_xboole_0(sK1,sK2),k5_xboole_0(sK2,k2_xboole_0(sK1,sK2))))),
% 1.21/0.53    inference(forward_demodulation,[],[f635,f95])).
% 1.21/0.53  fof(f635,plain,(
% 1.21/0.53    k2_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK2,k2_xboole_0(sK0,sK2)))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(k2_xboole_0(sK1,sK2),k5_xboole_0(sK2,k2_xboole_0(sK1,sK2))))))),
% 1.21/0.53    inference(superposition,[],[f107,f106])).
% 1.21/0.53  fof(f106,plain,(
% 1.21/0.53    k5_xboole_0(sK2,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2)))),
% 1.21/0.53    inference(backward_demodulation,[],[f71,f94])).
% 1.21/0.53  fof(f71,plain,(
% 1.21/0.53    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2))))),
% 1.21/0.53    inference(backward_demodulation,[],[f59,f60])).
% 1.21/0.53  fof(f59,plain,(
% 1.21/0.53    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2)))) = k2_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k2_xboole_0(sK1,sK2)))))),
% 1.21/0.53    inference(resolution,[],[f45,f31])).
% 1.21/0.53  fof(f102,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X0,X1)))),X2)) )),
% 1.21/0.53    inference(backward_demodulation,[],[f84,f94])).
% 1.21/0.53  fof(f84,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X0,X1))))),X2)) )),
% 1.21/0.53    inference(superposition,[],[f69,f34])).
% 1.21/0.53  % SZS output end Proof for theBenchmark
% 1.21/0.53  % (29550)------------------------------
% 1.21/0.53  % (29550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (29550)Termination reason: Refutation
% 1.21/0.53  
% 1.21/0.53  % (29550)Memory used [KB]: 2558
% 1.21/0.53  % (29550)Time elapsed: 0.106 s
% 1.21/0.53  % (29550)------------------------------
% 1.21/0.53  % (29550)------------------------------
% 1.21/0.54  % (29548)Success in time 0.17 s
%------------------------------------------------------------------------------
