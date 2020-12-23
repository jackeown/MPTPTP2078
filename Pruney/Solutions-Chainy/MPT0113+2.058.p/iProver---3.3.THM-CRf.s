%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:52 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 664 expanded)
%              Number of clauses        :   53 ( 211 expanded)
%              Number of leaves         :   14 ( 176 expanded)
%              Depth                    :   19
%              Number of atoms          :  144 (1028 expanded)
%              Number of equality atoms :   92 ( 585 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f34,f26])).

fof(f40,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(definition_unfolding,[],[f27,f37,f37])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f30,f26,f26])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f29,f26,f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f32,f26])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).

fof(f35,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f35,f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f24,f26])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_426,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_5,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_8,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_283,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(demodulation,[status(thm)],[c_5,c_8])).

cnf(c_1545,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))) ),
    inference(superposition,[status(thm)],[c_426,c_283])).

cnf(c_7,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_79,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_10,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_140,plain,
    ( X0 != X1
    | k3_xboole_0(X2,X1) = k1_xboole_0
    | k5_xboole_0(X3,k3_xboole_0(X3,X0)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_79,c_10])).

cnf(c_141,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_140])).

cnf(c_838,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_141])).

cnf(c_1025,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_838,c_838])).

cnf(c_1577,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_1545,c_426,c_1025])).

cnf(c_1578,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1577,c_9,c_1025])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1928,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1578,c_11])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_201,plain,
    ( k3_xboole_0(X0,X1) = X0
    | k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_202,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
    inference(unflattening,[status(thm)],[c_201])).

cnf(c_430,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_202,c_7])).

cnf(c_846,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_430,c_141])).

cnf(c_1493,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_430,c_846])).

cnf(c_3896,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0)))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1928,c_1493])).

cnf(c_481,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_202,c_8])).

cnf(c_486,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_481,c_430])).

cnf(c_611,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))) ),
    inference(superposition,[status(thm)],[c_430,c_486])).

cnf(c_613,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_611,c_430])).

cnf(c_823,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_202,c_613])).

cnf(c_830,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK0))) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_823,c_202])).

cnf(c_831,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_830,c_9,c_11])).

cnf(c_907,plain,
    ( k3_xboole_0(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_831,c_141])).

cnf(c_3930,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3896,c_907])).

cnf(c_484,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X2)))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_8,c_7])).

cnf(c_2628,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_141,c_484])).

cnf(c_2700,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_2628,c_9,c_1928])).

cnf(c_3931,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3930,c_9,c_11,c_430,c_2700])).

cnf(c_855,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0)) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_141,c_430])).

cnf(c_856,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_855,c_9,c_202])).

cnf(c_914,plain,
    ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_856,c_141])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_81,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_77,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_146,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k3_xboole_0(X0,X1) != k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_77,c_12])).

cnf(c_147,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_146])).

cnf(c_193,plain,
    ( k3_xboole_0(sK0,sK2) != k1_xboole_0
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_81,c_147])).

cnf(c_194,plain,
    ( k3_xboole_0(sK0,sK2) != k1_xboole_0
    | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3931,c_914,c_194])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:17:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.92/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/0.95  
% 3.92/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.92/0.95  
% 3.92/0.95  ------  iProver source info
% 3.92/0.95  
% 3.92/0.95  git: date: 2020-06-30 10:37:57 +0100
% 3.92/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.92/0.95  git: non_committed_changes: false
% 3.92/0.95  git: last_make_outside_of_git: false
% 3.92/0.95  
% 3.92/0.95  ------ 
% 3.92/0.95  
% 3.92/0.95  ------ Input Options
% 3.92/0.95  
% 3.92/0.95  --out_options                           all
% 3.92/0.95  --tptp_safe_out                         true
% 3.92/0.95  --problem_path                          ""
% 3.92/0.95  --include_path                          ""
% 3.92/0.95  --clausifier                            res/vclausify_rel
% 3.92/0.95  --clausifier_options                    ""
% 3.92/0.95  --stdin                                 false
% 3.92/0.95  --stats_out                             all
% 3.92/0.95  
% 3.92/0.95  ------ General Options
% 3.92/0.95  
% 3.92/0.95  --fof                                   false
% 3.92/0.95  --time_out_real                         305.
% 3.92/0.95  --time_out_virtual                      -1.
% 3.92/0.95  --symbol_type_check                     false
% 3.92/0.95  --clausify_out                          false
% 3.92/0.95  --sig_cnt_out                           false
% 3.92/0.95  --trig_cnt_out                          false
% 3.92/0.95  --trig_cnt_out_tolerance                1.
% 3.92/0.95  --trig_cnt_out_sk_spl                   false
% 3.92/0.95  --abstr_cl_out                          false
% 3.92/0.95  
% 3.92/0.95  ------ Global Options
% 3.92/0.95  
% 3.92/0.95  --schedule                              default
% 3.92/0.95  --add_important_lit                     false
% 3.92/0.95  --prop_solver_per_cl                    1000
% 3.92/0.95  --min_unsat_core                        false
% 3.92/0.95  --soft_assumptions                      false
% 3.92/0.95  --soft_lemma_size                       3
% 3.92/0.95  --prop_impl_unit_size                   0
% 3.92/0.95  --prop_impl_unit                        []
% 3.92/0.95  --share_sel_clauses                     true
% 3.92/0.95  --reset_solvers                         false
% 3.92/0.95  --bc_imp_inh                            [conj_cone]
% 3.92/0.95  --conj_cone_tolerance                   3.
% 3.92/0.95  --extra_neg_conj                        none
% 3.92/0.95  --large_theory_mode                     true
% 3.92/0.95  --prolific_symb_bound                   200
% 3.92/0.95  --lt_threshold                          2000
% 3.92/0.95  --clause_weak_htbl                      true
% 3.92/0.95  --gc_record_bc_elim                     false
% 3.92/0.95  
% 3.92/0.95  ------ Preprocessing Options
% 3.92/0.95  
% 3.92/0.95  --preprocessing_flag                    true
% 3.92/0.95  --time_out_prep_mult                    0.1
% 3.92/0.95  --splitting_mode                        input
% 3.92/0.95  --splitting_grd                         true
% 3.92/0.95  --splitting_cvd                         false
% 3.92/0.95  --splitting_cvd_svl                     false
% 3.92/0.95  --splitting_nvd                         32
% 3.92/0.95  --sub_typing                            true
% 3.92/0.95  --prep_gs_sim                           true
% 3.92/0.95  --prep_unflatten                        true
% 3.92/0.95  --prep_res_sim                          true
% 3.92/0.95  --prep_upred                            true
% 3.92/0.95  --prep_sem_filter                       exhaustive
% 3.92/0.95  --prep_sem_filter_out                   false
% 3.92/0.95  --pred_elim                             true
% 3.92/0.95  --res_sim_input                         true
% 3.92/0.95  --eq_ax_congr_red                       true
% 3.92/0.95  --pure_diseq_elim                       true
% 3.92/0.95  --brand_transform                       false
% 3.92/0.95  --non_eq_to_eq                          false
% 3.92/0.95  --prep_def_merge                        true
% 3.92/0.95  --prep_def_merge_prop_impl              false
% 3.92/0.95  --prep_def_merge_mbd                    true
% 3.92/0.95  --prep_def_merge_tr_red                 false
% 3.92/0.95  --prep_def_merge_tr_cl                  false
% 3.92/0.95  --smt_preprocessing                     true
% 3.92/0.95  --smt_ac_axioms                         fast
% 3.92/0.95  --preprocessed_out                      false
% 3.92/0.95  --preprocessed_stats                    false
% 3.92/0.95  
% 3.92/0.95  ------ Abstraction refinement Options
% 3.92/0.95  
% 3.92/0.95  --abstr_ref                             []
% 3.92/0.95  --abstr_ref_prep                        false
% 3.92/0.95  --abstr_ref_until_sat                   false
% 3.92/0.95  --abstr_ref_sig_restrict                funpre
% 3.92/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 3.92/0.95  --abstr_ref_under                       []
% 3.92/0.95  
% 3.92/0.95  ------ SAT Options
% 3.92/0.95  
% 3.92/0.95  --sat_mode                              false
% 3.92/0.95  --sat_fm_restart_options                ""
% 3.92/0.95  --sat_gr_def                            false
% 3.92/0.95  --sat_epr_types                         true
% 3.92/0.95  --sat_non_cyclic_types                  false
% 3.92/0.95  --sat_finite_models                     false
% 3.92/0.95  --sat_fm_lemmas                         false
% 3.92/0.95  --sat_fm_prep                           false
% 3.92/0.95  --sat_fm_uc_incr                        true
% 3.92/0.95  --sat_out_model                         small
% 3.92/0.95  --sat_out_clauses                       false
% 3.92/0.95  
% 3.92/0.95  ------ QBF Options
% 3.92/0.95  
% 3.92/0.95  --qbf_mode                              false
% 3.92/0.95  --qbf_elim_univ                         false
% 3.92/0.95  --qbf_dom_inst                          none
% 3.92/0.95  --qbf_dom_pre_inst                      false
% 3.92/0.95  --qbf_sk_in                             false
% 3.92/0.95  --qbf_pred_elim                         true
% 3.92/0.95  --qbf_split                             512
% 3.92/0.95  
% 3.92/0.95  ------ BMC1 Options
% 3.92/0.95  
% 3.92/0.95  --bmc1_incremental                      false
% 3.92/0.95  --bmc1_axioms                           reachable_all
% 3.92/0.95  --bmc1_min_bound                        0
% 3.92/0.95  --bmc1_max_bound                        -1
% 3.92/0.95  --bmc1_max_bound_default                -1
% 3.92/0.95  --bmc1_symbol_reachability              true
% 3.92/0.95  --bmc1_property_lemmas                  false
% 3.92/0.95  --bmc1_k_induction                      false
% 3.92/0.95  --bmc1_non_equiv_states                 false
% 3.92/0.95  --bmc1_deadlock                         false
% 3.92/0.95  --bmc1_ucm                              false
% 3.92/0.95  --bmc1_add_unsat_core                   none
% 3.92/0.95  --bmc1_unsat_core_children              false
% 3.92/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 3.92/0.95  --bmc1_out_stat                         full
% 3.92/0.95  --bmc1_ground_init                      false
% 3.92/0.95  --bmc1_pre_inst_next_state              false
% 3.92/0.95  --bmc1_pre_inst_state                   false
% 3.92/0.95  --bmc1_pre_inst_reach_state             false
% 3.92/0.95  --bmc1_out_unsat_core                   false
% 3.92/0.95  --bmc1_aig_witness_out                  false
% 3.92/0.95  --bmc1_verbose                          false
% 3.92/0.95  --bmc1_dump_clauses_tptp                false
% 3.92/0.95  --bmc1_dump_unsat_core_tptp             false
% 3.92/0.95  --bmc1_dump_file                        -
% 3.92/0.95  --bmc1_ucm_expand_uc_limit              128
% 3.92/0.95  --bmc1_ucm_n_expand_iterations          6
% 3.92/0.95  --bmc1_ucm_extend_mode                  1
% 3.92/0.95  --bmc1_ucm_init_mode                    2
% 3.92/0.95  --bmc1_ucm_cone_mode                    none
% 3.92/0.95  --bmc1_ucm_reduced_relation_type        0
% 3.92/0.95  --bmc1_ucm_relax_model                  4
% 3.92/0.95  --bmc1_ucm_full_tr_after_sat            true
% 3.92/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 3.92/0.95  --bmc1_ucm_layered_model                none
% 3.92/0.95  --bmc1_ucm_max_lemma_size               10
% 3.92/0.95  
% 3.92/0.95  ------ AIG Options
% 3.92/0.95  
% 3.92/0.95  --aig_mode                              false
% 3.92/0.95  
% 3.92/0.95  ------ Instantiation Options
% 3.92/0.95  
% 3.92/0.95  --instantiation_flag                    true
% 3.92/0.95  --inst_sos_flag                         true
% 3.92/0.95  --inst_sos_phase                        true
% 3.92/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.92/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.92/0.95  --inst_lit_sel_side                     num_symb
% 3.92/0.95  --inst_solver_per_active                1400
% 3.92/0.95  --inst_solver_calls_frac                1.
% 3.92/0.95  --inst_passive_queue_type               priority_queues
% 3.92/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.92/0.95  --inst_passive_queues_freq              [25;2]
% 3.92/0.95  --inst_dismatching                      true
% 3.92/0.95  --inst_eager_unprocessed_to_passive     true
% 3.92/0.95  --inst_prop_sim_given                   true
% 3.92/0.95  --inst_prop_sim_new                     false
% 3.92/0.95  --inst_subs_new                         false
% 3.92/0.95  --inst_eq_res_simp                      false
% 3.92/0.95  --inst_subs_given                       false
% 3.92/0.95  --inst_orphan_elimination               true
% 3.92/0.95  --inst_learning_loop_flag               true
% 3.92/0.95  --inst_learning_start                   3000
% 3.92/0.95  --inst_learning_factor                  2
% 3.92/0.95  --inst_start_prop_sim_after_learn       3
% 3.92/0.95  --inst_sel_renew                        solver
% 3.92/0.95  --inst_lit_activity_flag                true
% 3.92/0.95  --inst_restr_to_given                   false
% 3.92/0.95  --inst_activity_threshold               500
% 3.92/0.95  --inst_out_proof                        true
% 3.92/0.95  
% 3.92/0.95  ------ Resolution Options
% 3.92/0.95  
% 3.92/0.95  --resolution_flag                       true
% 3.92/0.95  --res_lit_sel                           adaptive
% 3.92/0.95  --res_lit_sel_side                      none
% 3.92/0.95  --res_ordering                          kbo
% 3.92/0.95  --res_to_prop_solver                    active
% 3.92/0.95  --res_prop_simpl_new                    false
% 3.92/0.95  --res_prop_simpl_given                  true
% 3.92/0.95  --res_passive_queue_type                priority_queues
% 3.92/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.92/0.95  --res_passive_queues_freq               [15;5]
% 3.92/0.95  --res_forward_subs                      full
% 3.92/0.95  --res_backward_subs                     full
% 3.92/0.95  --res_forward_subs_resolution           true
% 3.92/0.95  --res_backward_subs_resolution          true
% 3.92/0.95  --res_orphan_elimination                true
% 3.92/0.95  --res_time_limit                        2.
% 3.92/0.95  --res_out_proof                         true
% 3.92/0.95  
% 3.92/0.95  ------ Superposition Options
% 3.92/0.95  
% 3.92/0.95  --superposition_flag                    true
% 3.92/0.95  --sup_passive_queue_type                priority_queues
% 3.92/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.92/0.95  --sup_passive_queues_freq               [8;1;4]
% 3.92/0.95  --demod_completeness_check              fast
% 3.92/0.95  --demod_use_ground                      true
% 3.92/0.95  --sup_to_prop_solver                    passive
% 3.92/0.95  --sup_prop_simpl_new                    true
% 3.92/0.95  --sup_prop_simpl_given                  true
% 3.92/0.95  --sup_fun_splitting                     true
% 3.92/0.95  --sup_smt_interval                      50000
% 3.92/0.95  
% 3.92/0.95  ------ Superposition Simplification Setup
% 3.92/0.95  
% 3.92/0.95  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.92/0.95  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.92/0.95  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.92/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.92/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 3.92/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.92/0.95  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.92/0.95  --sup_immed_triv                        [TrivRules]
% 3.92/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.92/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.92/0.95  --sup_immed_bw_main                     []
% 3.92/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.92/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 3.92/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.92/0.95  --sup_input_bw                          []
% 3.92/0.95  
% 3.92/0.95  ------ Combination Options
% 3.92/0.95  
% 3.92/0.95  --comb_res_mult                         3
% 3.92/0.95  --comb_sup_mult                         2
% 3.92/0.95  --comb_inst_mult                        10
% 3.92/0.95  
% 3.92/0.95  ------ Debug Options
% 3.92/0.95  
% 3.92/0.95  --dbg_backtrace                         false
% 3.92/0.95  --dbg_dump_prop_clauses                 false
% 3.92/0.95  --dbg_dump_prop_clauses_file            -
% 3.92/0.95  --dbg_out_stat                          false
% 3.92/0.95  ------ Parsing...
% 3.92/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.92/0.95  
% 3.92/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.92/0.95  
% 3.92/0.95  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.92/0.95  
% 3.92/0.95  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.92/0.95  ------ Proving...
% 3.92/0.95  ------ Problem Properties 
% 3.92/0.95  
% 3.92/0.95  
% 3.92/0.95  clauses                                 15
% 3.92/0.95  conjectures                             0
% 3.92/0.95  EPR                                     0
% 3.92/0.95  Horn                                    15
% 3.92/0.95  unary                                   9
% 3.92/0.95  binary                                  4
% 3.92/0.95  lits                                    23
% 3.92/0.95  lits eq                                 21
% 3.92/0.95  fd_pure                                 0
% 3.92/0.95  fd_pseudo                               0
% 3.92/0.95  fd_cond                                 0
% 3.92/0.95  fd_pseudo_cond                          0
% 3.92/0.95  AC symbols                              0
% 3.92/0.95  
% 3.92/0.95  ------ Schedule dynamic 5 is on 
% 3.92/0.95  
% 3.92/0.95  ------ no conjectures: strip conj schedule 
% 3.92/0.95  
% 3.92/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 3.92/0.95  
% 3.92/0.95  
% 3.92/0.95  ------ 
% 3.92/0.95  Current options:
% 3.92/0.95  ------ 
% 3.92/0.95  
% 3.92/0.95  ------ Input Options
% 3.92/0.95  
% 3.92/0.95  --out_options                           all
% 3.92/0.95  --tptp_safe_out                         true
% 3.92/0.95  --problem_path                          ""
% 3.92/0.95  --include_path                          ""
% 3.92/0.95  --clausifier                            res/vclausify_rel
% 3.92/0.95  --clausifier_options                    ""
% 3.92/0.95  --stdin                                 false
% 3.92/0.95  --stats_out                             all
% 3.92/0.95  
% 3.92/0.95  ------ General Options
% 3.92/0.95  
% 3.92/0.95  --fof                                   false
% 3.92/0.95  --time_out_real                         305.
% 3.92/0.95  --time_out_virtual                      -1.
% 3.92/0.95  --symbol_type_check                     false
% 3.92/0.95  --clausify_out                          false
% 3.92/0.95  --sig_cnt_out                           false
% 3.92/0.95  --trig_cnt_out                          false
% 3.92/0.95  --trig_cnt_out_tolerance                1.
% 3.92/0.95  --trig_cnt_out_sk_spl                   false
% 3.92/0.95  --abstr_cl_out                          false
% 3.92/0.95  
% 3.92/0.95  ------ Global Options
% 3.92/0.95  
% 3.92/0.95  --schedule                              default
% 3.92/0.95  --add_important_lit                     false
% 3.92/0.95  --prop_solver_per_cl                    1000
% 3.92/0.95  --min_unsat_core                        false
% 3.92/0.95  --soft_assumptions                      false
% 3.92/0.95  --soft_lemma_size                       3
% 3.92/0.95  --prop_impl_unit_size                   0
% 3.92/0.95  --prop_impl_unit                        []
% 3.92/0.95  --share_sel_clauses                     true
% 3.92/0.95  --reset_solvers                         false
% 3.92/0.95  --bc_imp_inh                            [conj_cone]
% 3.92/0.95  --conj_cone_tolerance                   3.
% 3.92/0.95  --extra_neg_conj                        none
% 3.92/0.95  --large_theory_mode                     true
% 3.92/0.95  --prolific_symb_bound                   200
% 3.92/0.95  --lt_threshold                          2000
% 3.92/0.95  --clause_weak_htbl                      true
% 3.92/0.95  --gc_record_bc_elim                     false
% 3.92/0.95  
% 3.92/0.95  ------ Preprocessing Options
% 3.92/0.95  
% 3.92/0.95  --preprocessing_flag                    true
% 3.92/0.95  --time_out_prep_mult                    0.1
% 3.92/0.95  --splitting_mode                        input
% 3.92/0.95  --splitting_grd                         true
% 3.92/0.95  --splitting_cvd                         false
% 3.92/0.95  --splitting_cvd_svl                     false
% 3.92/0.95  --splitting_nvd                         32
% 3.92/0.95  --sub_typing                            true
% 3.92/0.95  --prep_gs_sim                           true
% 3.92/0.95  --prep_unflatten                        true
% 3.92/0.95  --prep_res_sim                          true
% 3.92/0.95  --prep_upred                            true
% 3.92/0.95  --prep_sem_filter                       exhaustive
% 3.92/0.95  --prep_sem_filter_out                   false
% 3.92/0.95  --pred_elim                             true
% 3.92/0.95  --res_sim_input                         true
% 3.92/0.95  --eq_ax_congr_red                       true
% 3.92/0.95  --pure_diseq_elim                       true
% 3.92/0.95  --brand_transform                       false
% 3.92/0.95  --non_eq_to_eq                          false
% 3.92/0.95  --prep_def_merge                        true
% 3.92/0.95  --prep_def_merge_prop_impl              false
% 3.92/0.95  --prep_def_merge_mbd                    true
% 3.92/0.95  --prep_def_merge_tr_red                 false
% 3.92/0.95  --prep_def_merge_tr_cl                  false
% 3.92/0.95  --smt_preprocessing                     true
% 3.92/0.95  --smt_ac_axioms                         fast
% 3.92/0.95  --preprocessed_out                      false
% 3.92/0.95  --preprocessed_stats                    false
% 3.92/0.95  
% 3.92/0.95  ------ Abstraction refinement Options
% 3.92/0.95  
% 3.92/0.95  --abstr_ref                             []
% 3.92/0.95  --abstr_ref_prep                        false
% 3.92/0.95  --abstr_ref_until_sat                   false
% 3.92/0.95  --abstr_ref_sig_restrict                funpre
% 3.92/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 3.92/0.95  --abstr_ref_under                       []
% 3.92/0.95  
% 3.92/0.95  ------ SAT Options
% 3.92/0.95  
% 3.92/0.95  --sat_mode                              false
% 3.92/0.95  --sat_fm_restart_options                ""
% 3.92/0.95  --sat_gr_def                            false
% 3.92/0.95  --sat_epr_types                         true
% 3.92/0.95  --sat_non_cyclic_types                  false
% 3.92/0.95  --sat_finite_models                     false
% 3.92/0.95  --sat_fm_lemmas                         false
% 3.92/0.95  --sat_fm_prep                           false
% 3.92/0.95  --sat_fm_uc_incr                        true
% 3.92/0.95  --sat_out_model                         small
% 3.92/0.95  --sat_out_clauses                       false
% 3.92/0.95  
% 3.92/0.95  ------ QBF Options
% 3.92/0.95  
% 3.92/0.95  --qbf_mode                              false
% 3.92/0.95  --qbf_elim_univ                         false
% 3.92/0.95  --qbf_dom_inst                          none
% 3.92/0.95  --qbf_dom_pre_inst                      false
% 3.92/0.95  --qbf_sk_in                             false
% 3.92/0.95  --qbf_pred_elim                         true
% 3.92/0.95  --qbf_split                             512
% 3.92/0.95  
% 3.92/0.95  ------ BMC1 Options
% 3.92/0.95  
% 3.92/0.95  --bmc1_incremental                      false
% 3.92/0.95  --bmc1_axioms                           reachable_all
% 3.92/0.95  --bmc1_min_bound                        0
% 3.92/0.95  --bmc1_max_bound                        -1
% 3.92/0.95  --bmc1_max_bound_default                -1
% 3.92/0.95  --bmc1_symbol_reachability              true
% 3.92/0.95  --bmc1_property_lemmas                  false
% 3.92/0.95  --bmc1_k_induction                      false
% 3.92/0.95  --bmc1_non_equiv_states                 false
% 3.92/0.95  --bmc1_deadlock                         false
% 3.92/0.95  --bmc1_ucm                              false
% 3.92/0.95  --bmc1_add_unsat_core                   none
% 3.92/0.95  --bmc1_unsat_core_children              false
% 3.92/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 3.92/0.95  --bmc1_out_stat                         full
% 3.92/0.95  --bmc1_ground_init                      false
% 3.92/0.95  --bmc1_pre_inst_next_state              false
% 3.92/0.95  --bmc1_pre_inst_state                   false
% 3.92/0.95  --bmc1_pre_inst_reach_state             false
% 3.92/0.95  --bmc1_out_unsat_core                   false
% 3.92/0.95  --bmc1_aig_witness_out                  false
% 3.92/0.95  --bmc1_verbose                          false
% 3.92/0.95  --bmc1_dump_clauses_tptp                false
% 3.92/0.95  --bmc1_dump_unsat_core_tptp             false
% 3.92/0.95  --bmc1_dump_file                        -
% 3.92/0.95  --bmc1_ucm_expand_uc_limit              128
% 3.92/0.95  --bmc1_ucm_n_expand_iterations          6
% 3.92/0.95  --bmc1_ucm_extend_mode                  1
% 3.92/0.95  --bmc1_ucm_init_mode                    2
% 3.92/0.95  --bmc1_ucm_cone_mode                    none
% 3.92/0.95  --bmc1_ucm_reduced_relation_type        0
% 3.92/0.95  --bmc1_ucm_relax_model                  4
% 3.92/0.95  --bmc1_ucm_full_tr_after_sat            true
% 3.92/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 3.92/0.95  --bmc1_ucm_layered_model                none
% 3.92/0.95  --bmc1_ucm_max_lemma_size               10
% 3.92/0.95  
% 3.92/0.95  ------ AIG Options
% 3.92/0.95  
% 3.92/0.95  --aig_mode                              false
% 3.92/0.95  
% 3.92/0.95  ------ Instantiation Options
% 3.92/0.95  
% 3.92/0.95  --instantiation_flag                    true
% 3.92/0.95  --inst_sos_flag                         true
% 3.92/0.95  --inst_sos_phase                        true
% 3.92/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.92/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.92/0.95  --inst_lit_sel_side                     none
% 3.92/0.95  --inst_solver_per_active                1400
% 3.92/0.95  --inst_solver_calls_frac                1.
% 3.92/0.95  --inst_passive_queue_type               priority_queues
% 3.92/0.95  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 3.92/0.95  --inst_passive_queues_freq              [25;2]
% 3.92/0.95  --inst_dismatching                      true
% 3.92/0.95  --inst_eager_unprocessed_to_passive     true
% 3.92/0.95  --inst_prop_sim_given                   true
% 3.92/0.95  --inst_prop_sim_new                     false
% 3.92/0.95  --inst_subs_new                         false
% 3.92/0.95  --inst_eq_res_simp                      false
% 3.92/0.95  --inst_subs_given                       false
% 3.92/0.95  --inst_orphan_elimination               true
% 3.92/0.95  --inst_learning_loop_flag               true
% 3.92/0.95  --inst_learning_start                   3000
% 3.92/0.95  --inst_learning_factor                  2
% 3.92/0.95  --inst_start_prop_sim_after_learn       3
% 3.92/0.95  --inst_sel_renew                        solver
% 3.92/0.95  --inst_lit_activity_flag                true
% 3.92/0.95  --inst_restr_to_given                   false
% 3.92/0.95  --inst_activity_threshold               500
% 3.92/0.95  --inst_out_proof                        true
% 3.92/0.95  
% 3.92/0.95  ------ Resolution Options
% 3.92/0.95  
% 3.92/0.95  --resolution_flag                       false
% 3.92/0.95  --res_lit_sel                           adaptive
% 3.92/0.95  --res_lit_sel_side                      none
% 3.92/0.95  --res_ordering                          kbo
% 3.92/0.95  --res_to_prop_solver                    active
% 3.92/0.95  --res_prop_simpl_new                    false
% 3.92/0.95  --res_prop_simpl_given                  true
% 3.92/0.95  --res_passive_queue_type                priority_queues
% 3.92/0.95  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 3.92/0.95  --res_passive_queues_freq               [15;5]
% 3.92/0.95  --res_forward_subs                      full
% 3.92/0.95  --res_backward_subs                     full
% 3.92/0.95  --res_forward_subs_resolution           true
% 3.92/0.95  --res_backward_subs_resolution          true
% 3.92/0.95  --res_orphan_elimination                true
% 3.92/0.95  --res_time_limit                        2.
% 3.92/0.95  --res_out_proof                         true
% 3.92/0.95  
% 3.92/0.95  ------ Superposition Options
% 3.92/0.95  
% 3.92/0.95  --superposition_flag                    true
% 3.92/0.95  --sup_passive_queue_type                priority_queues
% 3.92/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.92/0.95  --sup_passive_queues_freq               [8;1;4]
% 3.92/0.95  --demod_completeness_check              fast
% 3.92/0.95  --demod_use_ground                      true
% 3.92/0.95  --sup_to_prop_solver                    passive
% 3.92/0.95  --sup_prop_simpl_new                    true
% 3.92/0.95  --sup_prop_simpl_given                  true
% 3.92/0.95  --sup_fun_splitting                     true
% 3.92/0.95  --sup_smt_interval                      50000
% 3.92/0.95  
% 3.92/0.95  ------ Superposition Simplification Setup
% 3.92/0.95  
% 3.92/0.95  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.92/0.95  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.92/0.95  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.92/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.92/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 3.92/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.92/0.95  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.92/0.95  --sup_immed_triv                        [TrivRules]
% 3.92/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.92/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.92/0.95  --sup_immed_bw_main                     []
% 3.92/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.92/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 3.92/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.92/0.95  --sup_input_bw                          []
% 3.92/0.95  
% 3.92/0.95  ------ Combination Options
% 3.92/0.95  
% 3.92/0.95  --comb_res_mult                         3
% 3.92/0.95  --comb_sup_mult                         2
% 3.92/0.95  --comb_inst_mult                        10
% 3.92/0.95  
% 3.92/0.95  ------ Debug Options
% 3.92/0.95  
% 3.92/0.95  --dbg_backtrace                         false
% 3.92/0.95  --dbg_dump_prop_clauses                 false
% 3.92/0.95  --dbg_dump_prop_clauses_file            -
% 3.92/0.95  --dbg_out_stat                          false
% 3.92/0.95  
% 3.92/0.95  
% 3.92/0.95  
% 3.92/0.95  
% 3.92/0.95  ------ Proving...
% 3.92/0.95  
% 3.92/0.95  
% 3.92/0.95  % SZS status Theorem for theBenchmark.p
% 3.92/0.95  
% 3.92/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 3.92/0.95  
% 3.92/0.95  fof(f9,axiom,(
% 3.92/0.95    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.95  
% 3.92/0.95  fof(f31,plain,(
% 3.92/0.95    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.92/0.95    inference(cnf_transformation,[],[f9])).
% 3.92/0.95  
% 3.92/0.95  fof(f1,axiom,(
% 3.92/0.95    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.95  
% 3.92/0.95  fof(f21,plain,(
% 3.92/0.95    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.92/0.95    inference(cnf_transformation,[],[f1])).
% 3.92/0.95  
% 3.92/0.95  fof(f5,axiom,(
% 3.92/0.95    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 3.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.95  
% 3.92/0.95  fof(f27,plain,(
% 3.92/0.95    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 3.92/0.95    inference(cnf_transformation,[],[f5])).
% 3.92/0.95  
% 3.92/0.95  fof(f12,axiom,(
% 3.92/0.95    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.95  
% 3.92/0.95  fof(f34,plain,(
% 3.92/0.95    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.92/0.95    inference(cnf_transformation,[],[f12])).
% 3.92/0.95  
% 3.92/0.95  fof(f4,axiom,(
% 3.92/0.95    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.95  
% 3.92/0.95  fof(f26,plain,(
% 3.92/0.95    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.92/0.95    inference(cnf_transformation,[],[f4])).
% 3.92/0.95  
% 3.92/0.95  fof(f37,plain,(
% 3.92/0.95    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.92/0.95    inference(definition_unfolding,[],[f34,f26])).
% 3.92/0.95  
% 3.92/0.95  fof(f40,plain,(
% 3.92/0.95    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) )),
% 3.92/0.95    inference(definition_unfolding,[],[f27,f37,f37])).
% 3.92/0.95  
% 3.92/0.95  fof(f8,axiom,(
% 3.92/0.95    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 3.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.95  
% 3.92/0.95  fof(f30,plain,(
% 3.92/0.95    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 3.92/0.95    inference(cnf_transformation,[],[f8])).
% 3.92/0.95  
% 3.92/0.95  fof(f42,plain,(
% 3.92/0.95    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 3.92/0.95    inference(definition_unfolding,[],[f30,f26,f26])).
% 3.92/0.95  
% 3.92/0.95  fof(f7,axiom,(
% 3.92/0.95    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.95  
% 3.92/0.95  fof(f29,plain,(
% 3.92/0.95    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.92/0.95    inference(cnf_transformation,[],[f7])).
% 3.92/0.95  
% 3.92/0.95  fof(f41,plain,(
% 3.92/0.95    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 3.92/0.95    inference(definition_unfolding,[],[f29,f26,f26])).
% 3.92/0.95  
% 3.92/0.95  fof(f2,axiom,(
% 3.92/0.95    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.95  
% 3.92/0.95  fof(f17,plain,(
% 3.92/0.95    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.92/0.95    inference(nnf_transformation,[],[f2])).
% 3.92/0.95  
% 3.92/0.95  fof(f22,plain,(
% 3.92/0.95    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.92/0.95    inference(cnf_transformation,[],[f17])).
% 3.92/0.95  
% 3.92/0.95  fof(f10,axiom,(
% 3.92/0.95    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.95  
% 3.92/0.95  fof(f32,plain,(
% 3.92/0.95    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.92/0.95    inference(cnf_transformation,[],[f10])).
% 3.92/0.95  
% 3.92/0.95  fof(f43,plain,(
% 3.92/0.95    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 3.92/0.95    inference(definition_unfolding,[],[f32,f26])).
% 3.92/0.95  
% 3.92/0.95  fof(f11,axiom,(
% 3.92/0.95    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.95  
% 3.92/0.95  fof(f33,plain,(
% 3.92/0.95    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.92/0.95    inference(cnf_transformation,[],[f11])).
% 3.92/0.95  
% 3.92/0.95  fof(f6,axiom,(
% 3.92/0.95    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.95  
% 3.92/0.95  fof(f15,plain,(
% 3.92/0.95    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.92/0.95    inference(ennf_transformation,[],[f6])).
% 3.92/0.95  
% 3.92/0.95  fof(f28,plain,(
% 3.92/0.95    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.92/0.95    inference(cnf_transformation,[],[f15])).
% 3.92/0.95  
% 3.92/0.95  fof(f13,conjecture,(
% 3.92/0.95    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.95  
% 3.92/0.95  fof(f14,negated_conjecture,(
% 3.92/0.95    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.92/0.95    inference(negated_conjecture,[],[f13])).
% 3.92/0.95  
% 3.92/0.95  fof(f16,plain,(
% 3.92/0.95    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.92/0.95    inference(ennf_transformation,[],[f14])).
% 3.92/0.95  
% 3.92/0.95  fof(f19,plain,(
% 3.92/0.95    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 3.92/0.95    introduced(choice_axiom,[])).
% 3.92/0.95  
% 3.92/0.95  fof(f20,plain,(
% 3.92/0.95    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 3.92/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).
% 3.92/0.95  
% 3.92/0.95  fof(f35,plain,(
% 3.92/0.95    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 3.92/0.95    inference(cnf_transformation,[],[f20])).
% 3.92/0.95  
% 3.92/0.95  fof(f44,plain,(
% 3.92/0.95    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 3.92/0.95    inference(definition_unfolding,[],[f35,f26])).
% 3.92/0.95  
% 3.92/0.95  fof(f3,axiom,(
% 3.92/0.95    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.92/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.95  
% 3.92/0.95  fof(f18,plain,(
% 3.92/0.95    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 3.92/0.95    inference(nnf_transformation,[],[f3])).
% 3.92/0.95  
% 3.92/0.95  fof(f24,plain,(
% 3.92/0.95    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 3.92/0.95    inference(cnf_transformation,[],[f18])).
% 3.92/0.95  
% 3.92/0.95  fof(f39,plain,(
% 3.92/0.95    ( ! [X0,X1] : (r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0) )),
% 3.92/0.95    inference(definition_unfolding,[],[f24,f26])).
% 3.92/0.95  
% 3.92/0.95  fof(f23,plain,(
% 3.92/0.95    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.92/0.95    inference(cnf_transformation,[],[f17])).
% 3.92/0.95  
% 3.92/0.95  fof(f36,plain,(
% 3.92/0.95    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 3.92/0.95    inference(cnf_transformation,[],[f20])).
% 3.92/0.95  
% 3.92/0.95  cnf(c_9,plain,
% 3.92/0.95      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.92/0.95      inference(cnf_transformation,[],[f31]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_0,plain,
% 3.92/0.95      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 3.92/0.95      inference(cnf_transformation,[],[f21]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_426,plain,
% 3.92/0.95      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.92/0.95      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_5,plain,
% 3.92/0.95      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
% 3.92/0.95      inference(cnf_transformation,[],[f40]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_8,plain,
% 3.92/0.95      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.92/0.95      inference(cnf_transformation,[],[f42]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_283,plain,
% 3.92/0.95      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
% 3.92/0.95      inference(demodulation,[status(thm)],[c_5,c_8]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_1545,plain,
% 3.92/0.95      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))) ),
% 3.92/0.95      inference(superposition,[status(thm)],[c_426,c_283]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_7,plain,
% 3.92/0.95      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.92/0.95      inference(cnf_transformation,[],[f41]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_2,plain,
% 3.92/0.95      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.92/0.95      inference(cnf_transformation,[],[f22]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_79,plain,
% 3.92/0.95      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.92/0.95      inference(prop_impl,[status(thm)],[c_2]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_10,plain,
% 3.92/0.95      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 3.92/0.95      inference(cnf_transformation,[],[f43]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_140,plain,
% 3.92/0.95      ( X0 != X1
% 3.92/0.95      | k3_xboole_0(X2,X1) = k1_xboole_0
% 3.92/0.95      | k5_xboole_0(X3,k3_xboole_0(X3,X0)) != X2 ),
% 3.92/0.95      inference(resolution_lifted,[status(thm)],[c_79,c_10]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_141,plain,
% 3.92/0.95      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 3.92/0.95      inference(unflattening,[status(thm)],[c_140]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_838,plain,
% 3.92/0.95      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) = k1_xboole_0 ),
% 3.92/0.95      inference(superposition,[status(thm)],[c_7,c_141]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_1025,plain,
% 3.92/0.95      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.92/0.95      inference(superposition,[status(thm)],[c_838,c_838]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_1577,plain,
% 3.92/0.95      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k1_xboole_0)) ),
% 3.92/0.95      inference(demodulation,[status(thm)],[c_1545,c_426,c_1025]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_1578,plain,
% 3.92/0.95      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X1) ),
% 3.92/0.95      inference(demodulation,[status(thm)],[c_1577,c_9,c_1025]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_11,plain,
% 3.92/0.95      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.92/0.95      inference(cnf_transformation,[],[f33]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_1928,plain,
% 3.92/0.95      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.92/0.95      inference(superposition,[status(thm)],[c_1578,c_11]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_6,plain,
% 3.92/0.95      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.92/0.95      inference(cnf_transformation,[],[f28]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_13,negated_conjecture,
% 3.92/0.95      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 3.92/0.95      inference(cnf_transformation,[],[f44]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_201,plain,
% 3.92/0.95      ( k3_xboole_0(X0,X1) = X0
% 3.92/0.95      | k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != X1
% 3.92/0.95      | sK0 != X0 ),
% 3.92/0.95      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_202,plain,
% 3.92/0.95      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
% 3.92/0.95      inference(unflattening,[status(thm)],[c_201]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_430,plain,
% 3.92/0.95      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 3.92/0.95      inference(superposition,[status(thm)],[c_202,c_7]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_846,plain,
% 3.92/0.95      ( k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k1_xboole_0 ),
% 3.92/0.95      inference(superposition,[status(thm)],[c_430,c_141]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_1493,plain,
% 3.92/0.95      ( k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k1_xboole_0 ),
% 3.92/0.95      inference(superposition,[status(thm)],[c_430,c_846]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_3896,plain,
% 3.92/0.95      ( k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0)))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0)))) = k1_xboole_0 ),
% 3.92/0.95      inference(superposition,[status(thm)],[c_1928,c_1493]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_481,plain,
% 3.92/0.95      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
% 3.92/0.95      inference(superposition,[status(thm)],[c_202,c_8]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_486,plain,
% 3.92/0.95      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 3.92/0.95      inference(light_normalisation,[status(thm)],[c_481,c_430]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_611,plain,
% 3.92/0.95      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))) ),
% 3.92/0.95      inference(superposition,[status(thm)],[c_430,c_486]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_613,plain,
% 3.92/0.95      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
% 3.92/0.95      inference(light_normalisation,[status(thm)],[c_611,c_430]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_823,plain,
% 3.92/0.95      ( k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK0))) ),
% 3.92/0.95      inference(superposition,[status(thm)],[c_202,c_613]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_830,plain,
% 3.92/0.95      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK0))) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK0)) ),
% 3.92/0.95      inference(light_normalisation,[status(thm)],[c_823,c_202]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_831,plain,
% 3.92/0.95      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0)) = sK0 ),
% 3.92/0.95      inference(demodulation,[status(thm)],[c_830,c_9,c_11]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_907,plain,
% 3.92/0.95      ( k3_xboole_0(sK0,k1_xboole_0) = k1_xboole_0 ),
% 3.92/0.95      inference(superposition,[status(thm)],[c_831,c_141]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_3930,plain,
% 3.92/0.95      ( k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0)))) = k1_xboole_0 ),
% 3.92/0.95      inference(light_normalisation,[status(thm)],[c_3896,c_907]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_484,plain,
% 3.92/0.95      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X2)))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.92/0.95      inference(superposition,[status(thm)],[c_8,c_7]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_2628,plain,
% 3.92/0.95      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0))) ),
% 3.92/0.95      inference(superposition,[status(thm)],[c_141,c_484]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_2700,plain,
% 3.92/0.95      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
% 3.92/0.95      inference(demodulation,[status(thm)],[c_2628,c_9,c_1928]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_3931,plain,
% 3.92/0.95      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 3.92/0.95      inference(demodulation,
% 3.92/0.95                [status(thm)],
% 3.92/0.95                [c_3930,c_9,c_11,c_430,c_2700]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_855,plain,
% 3.92/0.95      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0)) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
% 3.92/0.95      inference(superposition,[status(thm)],[c_141,c_430]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_856,plain,
% 3.92/0.95      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = sK0 ),
% 3.92/0.95      inference(demodulation,[status(thm)],[c_855,c_9,c_202]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_914,plain,
% 3.92/0.95      ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
% 3.92/0.95      inference(superposition,[status(thm)],[c_856,c_141]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_4,plain,
% 3.92/0.95      ( r1_tarski(X0,X1)
% 3.92/0.95      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.92/0.95      inference(cnf_transformation,[],[f39]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_81,plain,
% 3.92/0.95      ( r1_tarski(X0,X1)
% 3.92/0.95      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.92/0.95      inference(prop_impl,[status(thm)],[c_4]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_1,plain,
% 3.92/0.95      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.92/0.95      inference(cnf_transformation,[],[f23]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_77,plain,
% 3.92/0.95      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.92/0.95      inference(prop_impl,[status(thm)],[c_1]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_12,negated_conjecture,
% 3.92/0.95      ( ~ r1_tarski(sK0,sK1) | ~ r1_xboole_0(sK0,sK2) ),
% 3.92/0.95      inference(cnf_transformation,[],[f36]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_146,plain,
% 3.92/0.95      ( ~ r1_tarski(sK0,sK1)
% 3.92/0.95      | k3_xboole_0(X0,X1) != k1_xboole_0
% 3.92/0.95      | sK2 != X1
% 3.92/0.95      | sK0 != X0 ),
% 3.92/0.95      inference(resolution_lifted,[status(thm)],[c_77,c_12]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_147,plain,
% 3.92/0.95      ( ~ r1_tarski(sK0,sK1) | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
% 3.92/0.95      inference(unflattening,[status(thm)],[c_146]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_193,plain,
% 3.92/0.95      ( k3_xboole_0(sK0,sK2) != k1_xboole_0
% 3.92/0.95      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 3.92/0.95      | sK1 != X1
% 3.92/0.95      | sK0 != X0 ),
% 3.92/0.95      inference(resolution_lifted,[status(thm)],[c_81,c_147]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(c_194,plain,
% 3.92/0.95      ( k3_xboole_0(sK0,sK2) != k1_xboole_0
% 3.92/0.95      | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 3.92/0.95      inference(unflattening,[status(thm)],[c_193]) ).
% 3.92/0.95  
% 3.92/0.95  cnf(contradiction,plain,
% 3.92/0.95      ( $false ),
% 3.92/0.95      inference(minisat,[status(thm)],[c_3931,c_914,c_194]) ).
% 3.92/0.95  
% 3.92/0.95  
% 3.92/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 3.92/0.95  
% 3.92/0.95  ------                               Statistics
% 3.92/0.95  
% 3.92/0.95  ------ General
% 3.92/0.95  
% 3.92/0.95  abstr_ref_over_cycles:                  0
% 3.92/0.95  abstr_ref_under_cycles:                 0
% 3.92/0.95  gc_basic_clause_elim:                   0
% 3.92/0.95  forced_gc_time:                         0
% 3.92/0.95  parsing_time:                           0.008
% 3.92/0.95  unif_index_cands_time:                  0.
% 3.92/0.95  unif_index_add_time:                    0.
% 3.92/0.95  orderings_time:                         0.
% 3.92/0.95  out_proof_time:                         0.007
% 3.92/0.95  total_time:                             0.234
% 3.92/0.95  num_of_symbols:                         40
% 3.92/0.95  num_of_terms:                           6892
% 3.92/0.95  
% 3.92/0.95  ------ Preprocessing
% 3.92/0.95  
% 3.92/0.95  num_of_splits:                          1
% 3.92/0.95  num_of_split_atoms:                     1
% 3.92/0.95  num_of_reused_defs:                     0
% 3.92/0.95  num_eq_ax_congr_red:                    0
% 3.92/0.95  num_of_sem_filtered_clauses:            0
% 3.92/0.95  num_of_subtypes:                        0
% 3.92/0.95  monotx_restored_types:                  0
% 3.92/0.95  sat_num_of_epr_types:                   0
% 3.92/0.95  sat_num_of_non_cyclic_types:            0
% 3.92/0.95  sat_guarded_non_collapsed_types:        0
% 3.92/0.95  num_pure_diseq_elim:                    0
% 3.92/0.95  simp_replaced_by:                       0
% 3.92/0.95  res_preprocessed:                       33
% 3.92/0.95  prep_upred:                             0
% 3.92/0.95  prep_unflattend:                        13
% 3.92/0.95  smt_new_axioms:                         0
% 3.92/0.95  pred_elim_cands:                        2
% 3.92/0.95  pred_elim:                              2
% 3.92/0.95  pred_elim_cl:                           0
% 3.92/0.95  pred_elim_cycles:                       3
% 3.92/0.95  merged_defs:                            4
% 3.92/0.95  merged_defs_ncl:                        0
% 3.92/0.95  bin_hyper_res:                          4
% 3.92/0.95  prep_cycles:                            2
% 3.92/0.95  pred_elim_time:                         0.002
% 3.92/0.95  splitting_time:                         0.
% 3.92/0.95  sem_filter_time:                        0.
% 3.92/0.95  monotx_time:                            0.
% 3.92/0.95  subtype_inf_time:                       0.
% 3.92/0.95  
% 3.92/0.95  ------ Problem properties
% 3.92/0.95  
% 3.92/0.95  clauses:                                15
% 3.92/0.95  conjectures:                            0
% 3.92/0.95  epr:                                    0
% 3.92/0.95  horn:                                   15
% 3.92/0.95  ground:                                 5
% 3.92/0.95  unary:                                  9
% 3.92/0.95  binary:                                 4
% 3.92/0.95  lits:                                   23
% 3.92/0.95  lits_eq:                                21
% 3.92/0.95  fd_pure:                                0
% 3.92/0.95  fd_pseudo:                              0
% 3.92/0.95  fd_cond:                                0
% 3.92/0.95  fd_pseudo_cond:                         0
% 3.92/0.95  ac_symbols:                             0
% 3.92/0.95  
% 3.92/0.95  ------ Propositional Solver
% 3.92/0.95  
% 3.92/0.95  prop_solver_calls:                      23
% 3.92/0.95  prop_fast_solver_calls:                 195
% 3.92/0.95  smt_solver_calls:                       0
% 3.92/0.95  smt_fast_solver_calls:                  0
% 3.92/0.95  prop_num_of_clauses:                    1492
% 3.92/0.95  prop_preprocess_simplified:             2022
% 3.92/0.95  prop_fo_subsumed:                       1
% 3.92/0.95  prop_solver_time:                       0.
% 3.92/0.95  smt_solver_time:                        0.
% 3.92/0.95  smt_fast_solver_time:                   0.
% 3.92/0.95  prop_fast_solver_time:                  0.
% 3.92/0.95  prop_unsat_core_time:                   0.
% 3.92/0.95  
% 3.92/0.95  ------ QBF
% 3.92/0.95  
% 3.92/0.95  qbf_q_res:                              0
% 3.92/0.95  qbf_num_tautologies:                    0
% 3.92/0.95  qbf_prep_cycles:                        0
% 3.92/0.95  
% 3.92/0.95  ------ BMC1
% 3.92/0.95  
% 3.92/0.95  bmc1_current_bound:                     -1
% 3.92/0.95  bmc1_last_solved_bound:                 -1
% 3.92/0.95  bmc1_unsat_core_size:                   -1
% 3.92/0.95  bmc1_unsat_core_parents_size:           -1
% 3.92/0.95  bmc1_merge_next_fun:                    0
% 3.92/0.95  bmc1_unsat_core_clauses_time:           0.
% 3.92/0.95  
% 3.92/0.95  ------ Instantiation
% 3.92/0.95  
% 3.92/0.95  inst_num_of_clauses:                    616
% 3.92/0.95  inst_num_in_passive:                    128
% 3.92/0.95  inst_num_in_active:                     224
% 3.92/0.95  inst_num_in_unprocessed:                264
% 3.92/0.95  inst_num_of_loops:                      280
% 3.92/0.95  inst_num_of_learning_restarts:          0
% 3.92/0.95  inst_num_moves_active_passive:          51
% 3.92/0.95  inst_lit_activity:                      0
% 3.92/0.95  inst_lit_activity_moves:                0
% 3.92/0.95  inst_num_tautologies:                   0
% 3.92/0.95  inst_num_prop_implied:                  0
% 3.92/0.95  inst_num_existing_simplified:           0
% 3.92/0.95  inst_num_eq_res_simplified:             0
% 3.92/0.95  inst_num_child_elim:                    0
% 3.92/0.95  inst_num_of_dismatching_blockings:      233
% 3.92/0.95  inst_num_of_non_proper_insts:           542
% 3.92/0.95  inst_num_of_duplicates:                 0
% 3.92/0.95  inst_inst_num_from_inst_to_res:         0
% 3.92/0.95  inst_dismatching_checking_time:         0.
% 3.92/0.95  
% 3.92/0.95  ------ Resolution
% 3.92/0.95  
% 3.92/0.95  res_num_of_clauses:                     0
% 3.92/0.95  res_num_in_passive:                     0
% 3.92/0.95  res_num_in_active:                      0
% 3.92/0.95  res_num_of_loops:                       35
% 3.92/0.95  res_forward_subset_subsumed:            184
% 3.92/0.95  res_backward_subset_subsumed:           0
% 3.92/0.95  res_forward_subsumed:                   0
% 3.92/0.95  res_backward_subsumed:                  0
% 3.92/0.95  res_forward_subsumption_resolution:     0
% 3.92/0.95  res_backward_subsumption_resolution:    0
% 3.92/0.95  res_clause_to_clause_subsumption:       801
% 3.92/0.95  res_orphan_elimination:                 0
% 3.92/0.95  res_tautology_del:                      71
% 3.92/0.95  res_num_eq_res_simplified:              2
% 3.92/0.95  res_num_sel_changes:                    0
% 3.92/0.95  res_moves_from_active_to_pass:          0
% 3.92/0.95  
% 3.92/0.95  ------ Superposition
% 3.92/0.95  
% 3.92/0.95  sup_time_total:                         0.
% 3.92/0.95  sup_time_generating:                    0.
% 3.92/0.95  sup_time_sim_full:                      0.
% 3.92/0.95  sup_time_sim_immed:                     0.
% 3.92/0.95  
% 3.92/0.95  sup_num_of_clauses:                     280
% 3.92/0.95  sup_num_in_active:                      44
% 3.92/0.95  sup_num_in_passive:                     236
% 3.92/0.95  sup_num_of_loops:                       54
% 3.92/0.95  sup_fw_superposition:                   371
% 3.92/0.95  sup_bw_superposition:                   356
% 3.92/0.95  sup_immediate_simplified:               641
% 3.92/0.95  sup_given_eliminated:                   4
% 3.92/0.95  comparisons_done:                       0
% 3.92/0.95  comparisons_avoided:                    0
% 3.92/0.95  
% 3.92/0.95  ------ Simplifications
% 3.92/0.95  
% 3.92/0.95  
% 3.92/0.95  sim_fw_subset_subsumed:                 8
% 3.92/0.95  sim_bw_subset_subsumed:                 1
% 3.92/0.95  sim_fw_subsumed:                        78
% 3.92/0.95  sim_bw_subsumed:                        12
% 3.92/0.95  sim_fw_subsumption_res:                 0
% 3.92/0.95  sim_bw_subsumption_res:                 0
% 3.92/0.95  sim_tautology_del:                      30
% 3.92/0.95  sim_eq_tautology_del:                   167
% 3.92/0.95  sim_eq_res_simp:                        4
% 3.92/0.95  sim_fw_demodulated:                     516
% 3.92/0.95  sim_bw_demodulated:                     11
% 3.92/0.95  sim_light_normalised:                   181
% 3.92/0.95  sim_joinable_taut:                      0
% 3.92/0.95  sim_joinable_simp:                      0
% 3.92/0.95  sim_ac_normalised:                      0
% 3.92/0.95  sim_smt_subsumption:                    0
% 3.92/0.95  
%------------------------------------------------------------------------------
