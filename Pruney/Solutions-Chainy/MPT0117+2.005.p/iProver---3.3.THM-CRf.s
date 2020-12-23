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
% DateTime   : Thu Dec  3 11:26:05 EST 2020

% Result     : Theorem 19.64s
% Output     : CNFRefutation 19.64s
% Verified   : 
% Statistics : Number of formulae       :   94 (4425 expanded)
%              Number of clauses        :   62 (1130 expanded)
%              Number of leaves         :   11 (1330 expanded)
%              Depth                    :   33
%              Number of atoms          :  120 (5299 expanded)
%              Number of equality atoms :   84 (4137 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f26,f20])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) ),
    inference(definition_unfolding,[],[f27,f31,f20,f31,f20,f31,f20])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f18,f31,f31])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).

fof(f29,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f28,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_5,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_82,plain,
    ( X0 != X1
    | k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))) != X3
    | k3_xboole_0(X1,X3) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_5])).

cnf(c_83,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(unflattening,[status(thm)],[c_82])).

cnf(c_1734,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_83])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1465,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_3095,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))))),k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))))),k5_xboole_0(X0,X0)))) = k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X0)) ),
    inference(superposition,[status(thm)],[c_1734,c_1465])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_3208,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))))),k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_3095,c_6])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1958,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))),k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1))) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(superposition,[status(thm)],[c_7,c_1734])).

cnf(c_2028,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1958,c_6,c_83])).

cnf(c_2398,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2028,c_2028])).

cnf(c_2400,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2398,c_4])).

cnf(c_3209,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3208,c_4,c_6,c_1734,c_2400])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1431,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_4440,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3209,c_1431])).

cnf(c_4557,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4440,c_4])).

cnf(c_7029,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_1734,c_4557])).

cnf(c_7082,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7029,c_4557])).

cnf(c_7084,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7082,c_4])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_88,plain,
    ( k3_xboole_0(X0,X1) = X0
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_89,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(unflattening,[status(thm)],[c_88])).

cnf(c_1467,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))),X1)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))),X1)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_4134,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))),sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))),sK1)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))))))) = k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(k5_xboole_0(X0,sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_89,c_1467])).

cnf(c_4223,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))),sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))),sK1)),k5_xboole_0(X0,k3_xboole_0(X0,sK1))))) = k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(k5_xboole_0(X0,sK1),sK2)) ),
    inference(demodulation,[status(thm)],[c_4134,c_4,c_6])).

cnf(c_7216,plain,
    ( k5_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0))),sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0))),sK1)),k3_xboole_0(k1_xboole_0,sK1)))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k3_xboole_0(k5_xboole_0(k1_xboole_0,sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_7084,c_4223])).

cnf(c_7305,plain,
    ( k5_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0)),sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0)),sK1)),k3_xboole_0(k1_xboole_0,sK1)))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_7216,c_7084])).

cnf(c_4426,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_3209])).

cnf(c_7238,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7084,c_4426])).

cnf(c_7306,plain,
    ( k5_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k1_xboole_0),sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k1_xboole_0),sK1)),k3_xboole_0(k1_xboole_0,sK1)))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_7305,c_7238])).

cnf(c_7308,plain,
    ( k5_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,sK1)))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_7306,c_4,c_89])).

cnf(c_7515,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[status(thm)],[c_7308,c_83])).

cnf(c_7850,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[status(thm)],[c_1,c_7515])).

cnf(c_7922,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(sK1,sK2)) = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_7850,c_89])).

cnf(c_7947,plain,
    ( k5_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,sK1)))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k3_xboole_0(k1_xboole_0,sK1))) ),
    inference(superposition,[status(thm)],[c_7922,c_0])).

cnf(c_7998,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k3_xboole_0(k1_xboole_0,sK1))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_7947,c_7308])).

cnf(c_7999,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_7998,c_4,c_6])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_93,plain,
    ( k3_xboole_0(X0,X1) = X0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_94,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_93])).

cnf(c_1409,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_94,c_0])).

cnf(c_1415,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = sK1 ),
    inference(demodulation,[status(thm)],[c_1409,c_4,c_6])).

cnf(c_1542,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))))))) = k5_xboole_0(k5_xboole_0(sK0,X0),k3_xboole_0(k5_xboole_0(sK0,X0),sK1)) ),
    inference(superposition,[status(thm)],[c_1415,c_7])).

cnf(c_24866,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) ),
    inference(superposition,[status(thm)],[c_7999,c_1542])).

cnf(c_1408,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_89,c_0])).

cnf(c_1418,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK1 ),
    inference(demodulation,[status(thm)],[c_1408,c_4,c_6])).

cnf(c_1560,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_1,c_1418])).

cnf(c_1571,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1560,c_89])).

cnf(c_25039,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK0),k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK0,sK0)))) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) ),
    inference(light_normalisation,[status(thm)],[c_24866,c_89,c_94,c_1571])).

cnf(c_25040,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_25039,c_6,c_2400,c_7084])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_103,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != sK1
    | k5_xboole_0(sK0,sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_8])).

cnf(c_104,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK2),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,sK2)))) != sK1 ),
    inference(unflattening,[status(thm)],[c_103])).

cnf(c_1410,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),X0))) != sK1 ),
    inference(superposition,[status(thm)],[c_0,c_104])).

cnf(c_25830,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) != sK1 ),
    inference(superposition,[status(thm)],[c_25040,c_1410])).

cnf(c_25868,plain,
    ( sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_25830,c_4])).

cnf(c_25869,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_25868])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 19.64/3.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.64/3.01  
% 19.64/3.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.64/3.01  
% 19.64/3.01  ------  iProver source info
% 19.64/3.01  
% 19.64/3.01  git: date: 2020-06-30 10:37:57 +0100
% 19.64/3.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.64/3.01  git: non_committed_changes: false
% 19.64/3.01  git: last_make_outside_of_git: false
% 19.64/3.01  
% 19.64/3.01  ------ 
% 19.64/3.01  ------ Parsing...
% 19.64/3.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.64/3.01  
% 19.64/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 19.64/3.01  
% 19.64/3.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.64/3.01  
% 19.64/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.64/3.01  ------ Proving...
% 19.64/3.01  ------ Problem Properties 
% 19.64/3.01  
% 19.64/3.01  
% 19.64/3.01  clauses                                 13
% 19.64/3.01  conjectures                             0
% 19.64/3.01  EPR                                     0
% 19.64/3.01  Horn                                    13
% 19.64/3.01  unary                                   11
% 19.64/3.01  binary                                  2
% 19.64/3.01  lits                                    15
% 19.64/3.01  lits eq                                 15
% 19.64/3.01  fd_pure                                 0
% 19.64/3.01  fd_pseudo                               0
% 19.64/3.01  fd_cond                                 0
% 19.64/3.01  fd_pseudo_cond                          0
% 19.64/3.01  AC symbols                              0
% 19.64/3.01  
% 19.64/3.01  ------ Input Options Time Limit: Unbounded
% 19.64/3.01  
% 19.64/3.01  
% 19.64/3.01  
% 19.64/3.01  
% 19.64/3.01  ------ Preprocessing...
% 19.64/3.01  
% 19.64/3.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 19.64/3.01  Current options:
% 19.64/3.01  ------ 
% 19.64/3.01  
% 19.64/3.01  
% 19.64/3.01  
% 19.64/3.01  
% 19.64/3.01  ------ Proving...
% 19.64/3.01  
% 19.64/3.01  
% 19.64/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.64/3.01  
% 19.64/3.01  ------ Proving...
% 19.64/3.01  
% 19.64/3.01  
% 19.64/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.64/3.01  
% 19.64/3.01  ------ Proving...
% 19.64/3.01  
% 19.64/3.01  
% 19.64/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.64/3.01  
% 19.64/3.01  ------ Proving...
% 19.64/3.01  
% 19.64/3.01  
% 19.64/3.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.64/3.01  
% 19.64/3.01  ------ Proving...
% 19.64/3.01  
% 19.64/3.01  
% 19.64/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.64/3.01  
% 19.64/3.01  ------ Proving...
% 19.64/3.01  
% 19.64/3.01  
% 19.64/3.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.64/3.01  
% 19.64/3.01  ------ Proving...
% 19.64/3.01  
% 19.64/3.01  
% 19.64/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.64/3.01  
% 19.64/3.01  ------ Proving...
% 19.64/3.01  
% 19.64/3.01  
% 19.64/3.01  % SZS status Theorem for theBenchmark.p
% 19.64/3.01  
% 19.64/3.01   Resolution empty clause
% 19.64/3.01  
% 19.64/3.01  % SZS output start CNFRefutation for theBenchmark.p
% 19.64/3.01  
% 19.64/3.01  fof(f2,axiom,(
% 19.64/3.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 19.64/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.64/3.01  
% 19.64/3.01  fof(f19,plain,(
% 19.64/3.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 19.64/3.01    inference(cnf_transformation,[],[f2])).
% 19.64/3.01  
% 19.64/3.01  fof(f4,axiom,(
% 19.64/3.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 19.64/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.64/3.01  
% 19.64/3.01  fof(f13,plain,(
% 19.64/3.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 19.64/3.01    inference(ennf_transformation,[],[f4])).
% 19.64/3.01  
% 19.64/3.01  fof(f21,plain,(
% 19.64/3.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 19.64/3.01    inference(cnf_transformation,[],[f13])).
% 19.64/3.01  
% 19.64/3.01  fof(f7,axiom,(
% 19.64/3.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 19.64/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.64/3.01  
% 19.64/3.01  fof(f24,plain,(
% 19.64/3.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 19.64/3.01    inference(cnf_transformation,[],[f7])).
% 19.64/3.01  
% 19.64/3.01  fof(f9,axiom,(
% 19.64/3.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 19.64/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.64/3.01  
% 19.64/3.01  fof(f26,plain,(
% 19.64/3.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 19.64/3.01    inference(cnf_transformation,[],[f9])).
% 19.64/3.01  
% 19.64/3.01  fof(f3,axiom,(
% 19.64/3.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 19.64/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.64/3.01  
% 19.64/3.01  fof(f20,plain,(
% 19.64/3.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 19.64/3.01    inference(cnf_transformation,[],[f3])).
% 19.64/3.01  
% 19.64/3.01  fof(f31,plain,(
% 19.64/3.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 19.64/3.01    inference(definition_unfolding,[],[f26,f20])).
% 19.64/3.01  
% 19.64/3.01  fof(f33,plain,(
% 19.64/3.01    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 19.64/3.01    inference(definition_unfolding,[],[f24,f31])).
% 19.64/3.01  
% 19.64/3.01  fof(f10,axiom,(
% 19.64/3.01    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2)),
% 19.64/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.64/3.01  
% 19.64/3.01  fof(f27,plain,(
% 19.64/3.01    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 19.64/3.01    inference(cnf_transformation,[],[f10])).
% 19.64/3.01  
% 19.64/3.01  fof(f34,plain,(
% 19.64/3.01    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))))) )),
% 19.64/3.01    inference(definition_unfolding,[],[f27,f31,f20,f31,f20,f31,f20])).
% 19.64/3.01  
% 19.64/3.01  fof(f8,axiom,(
% 19.64/3.01    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 19.64/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.64/3.01  
% 19.64/3.01  fof(f25,plain,(
% 19.64/3.01    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 19.64/3.01    inference(cnf_transformation,[],[f8])).
% 19.64/3.01  
% 19.64/3.01  fof(f6,axiom,(
% 19.64/3.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 19.64/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.64/3.01  
% 19.64/3.01  fof(f23,plain,(
% 19.64/3.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.64/3.01    inference(cnf_transformation,[],[f6])).
% 19.64/3.01  
% 19.64/3.01  fof(f1,axiom,(
% 19.64/3.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 19.64/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.64/3.01  
% 19.64/3.01  fof(f18,plain,(
% 19.64/3.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 19.64/3.01    inference(cnf_transformation,[],[f1])).
% 19.64/3.01  
% 19.64/3.01  fof(f32,plain,(
% 19.64/3.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 19.64/3.01    inference(definition_unfolding,[],[f18,f31,f31])).
% 19.64/3.01  
% 19.64/3.01  fof(f11,conjecture,(
% 19.64/3.01    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 19.64/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.64/3.01  
% 19.64/3.01  fof(f12,negated_conjecture,(
% 19.64/3.01    ~! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 19.64/3.01    inference(negated_conjecture,[],[f11])).
% 19.64/3.01  
% 19.64/3.01  fof(f14,plain,(
% 19.64/3.01    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & (r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 19.64/3.01    inference(ennf_transformation,[],[f12])).
% 19.64/3.01  
% 19.64/3.01  fof(f15,plain,(
% 19.64/3.01    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 19.64/3.01    inference(flattening,[],[f14])).
% 19.64/3.01  
% 19.64/3.01  fof(f16,plain,(
% 19.64/3.01    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => (~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1))),
% 19.64/3.01    introduced(choice_axiom,[])).
% 19.64/3.01  
% 19.64/3.01  fof(f17,plain,(
% 19.64/3.01    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1)),
% 19.64/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).
% 19.64/3.01  
% 19.64/3.01  fof(f29,plain,(
% 19.64/3.01    r1_tarski(sK2,sK1)),
% 19.64/3.01    inference(cnf_transformation,[],[f17])).
% 19.64/3.01  
% 19.64/3.01  fof(f28,plain,(
% 19.64/3.01    r1_tarski(sK0,sK1)),
% 19.64/3.01    inference(cnf_transformation,[],[f17])).
% 19.64/3.01  
% 19.64/3.01  fof(f30,plain,(
% 19.64/3.01    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 19.64/3.01    inference(cnf_transformation,[],[f17])).
% 19.64/3.01  
% 19.64/3.01  cnf(c_1,plain,
% 19.64/3.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 19.64/3.01      inference(cnf_transformation,[],[f19]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_2,plain,
% 19.64/3.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 19.64/3.01      inference(cnf_transformation,[],[f21]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_5,plain,
% 19.64/3.01      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 19.64/3.01      inference(cnf_transformation,[],[f33]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_82,plain,
% 19.64/3.01      ( X0 != X1
% 19.64/3.01      | k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))) != X3
% 19.64/3.01      | k3_xboole_0(X1,X3) = X1 ),
% 19.64/3.01      inference(resolution_lifted,[status(thm)],[c_2,c_5]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_83,plain,
% 19.64/3.01      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 19.64/3.01      inference(unflattening,[status(thm)],[c_82]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_1734,plain,
% 19.64/3.01      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_1,c_83]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_7,plain,
% 19.64/3.01      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) ),
% 19.64/3.01      inference(cnf_transformation,[],[f34]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_1465,plain,
% 19.64/3.01      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_3095,plain,
% 19.64/3.01      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))))),k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))))),k5_xboole_0(X0,X0)))) = k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X0)) ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_1734,c_1465]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_6,plain,
% 19.64/3.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.64/3.01      inference(cnf_transformation,[],[f25]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_3208,plain,
% 19.64/3.01      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))))),k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 19.64/3.01      inference(light_normalisation,[status(thm)],[c_3095,c_6]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_4,plain,
% 19.64/3.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.64/3.01      inference(cnf_transformation,[],[f23]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_1958,plain,
% 19.64/3.01      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))),k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1))) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_7,c_1734]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_2028,plain,
% 19.64/3.01      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k1_xboole_0 ),
% 19.64/3.01      inference(light_normalisation,[status(thm)],[c_1958,c_6,c_83]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_2398,plain,
% 19.64/3.01      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_2028,c_2028]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_2400,plain,
% 19.64/3.01      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 19.64/3.01      inference(demodulation,[status(thm)],[c_2398,c_4]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_3209,plain,
% 19.64/3.01      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 19.64/3.01      inference(demodulation,[status(thm)],[c_3208,c_4,c_6,c_1734,c_2400]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_0,plain,
% 19.64/3.01      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 19.64/3.01      inference(cnf_transformation,[],[f32]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_1431,plain,
% 19.64/3.01      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_4440,plain,
% 19.64/3.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,k1_xboole_0) ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_3209,c_1431]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_4557,plain,
% 19.64/3.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 19.64/3.01      inference(light_normalisation,[status(thm)],[c_4440,c_4]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_7029,plain,
% 19.64/3.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_1734,c_4557]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_7082,plain,
% 19.64/3.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = X0 ),
% 19.64/3.01      inference(light_normalisation,[status(thm)],[c_7029,c_4557]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_7084,plain,
% 19.64/3.01      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 19.64/3.01      inference(light_normalisation,[status(thm)],[c_7082,c_4]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_9,negated_conjecture,
% 19.64/3.01      ( r1_tarski(sK2,sK1) ),
% 19.64/3.01      inference(cnf_transformation,[],[f29]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_88,plain,
% 19.64/3.01      ( k3_xboole_0(X0,X1) = X0 | sK1 != X1 | sK2 != X0 ),
% 19.64/3.01      inference(resolution_lifted,[status(thm)],[c_2,c_9]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_89,plain,
% 19.64/3.01      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 19.64/3.01      inference(unflattening,[status(thm)],[c_88]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_1467,plain,
% 19.64/3.01      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))),X1)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))),X1)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_4134,plain,
% 19.64/3.01      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))),sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))),sK1)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))))))) = k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(k5_xboole_0(X0,sK1),sK2)) ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_89,c_1467]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_4223,plain,
% 19.64/3.01      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK1)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))),sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))),sK1)),k5_xboole_0(X0,k3_xboole_0(X0,sK1))))) = k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(k5_xboole_0(X0,sK1),sK2)) ),
% 19.64/3.01      inference(demodulation,[status(thm)],[c_4134,c_4,c_6]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_7216,plain,
% 19.64/3.01      ( k5_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0))),sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0))),sK1)),k3_xboole_0(k1_xboole_0,sK1)))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k3_xboole_0(k5_xboole_0(k1_xboole_0,sK1),sK2)) ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_7084,c_4223]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_7305,plain,
% 19.64/3.01      ( k5_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0)),sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_xboole_0)),sK1)),k3_xboole_0(k1_xboole_0,sK1)))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 19.64/3.01      inference(demodulation,[status(thm)],[c_7216,c_7084]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_4426,plain,
% 19.64/3.01      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_1,c_3209]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_7238,plain,
% 19.64/3.01      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_7084,c_4426]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_7306,plain,
% 19.64/3.01      ( k5_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k1_xboole_0),sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k1_xboole_0),sK1)),k3_xboole_0(k1_xboole_0,sK1)))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 19.64/3.01      inference(demodulation,[status(thm)],[c_7305,c_7238]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_7308,plain,
% 19.64/3.01      ( k5_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,sK1)))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 19.64/3.01      inference(demodulation,[status(thm)],[c_7306,c_4,c_89]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_7515,plain,
% 19.64/3.01      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k3_xboole_0(k1_xboole_0,sK1) ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_7308,c_83]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_7850,plain,
% 19.64/3.01      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k3_xboole_0(k1_xboole_0,sK1) ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_1,c_7515]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_7922,plain,
% 19.64/3.01      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(sK1,sK2)) = k3_xboole_0(k1_xboole_0,sK1) ),
% 19.64/3.01      inference(light_normalisation,[status(thm)],[c_7850,c_89]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_7947,plain,
% 19.64/3.01      ( k5_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,sK1)))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k3_xboole_0(k1_xboole_0,sK1))) ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_7922,c_0]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_7998,plain,
% 19.64/3.01      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k3_xboole_0(k1_xboole_0,sK1))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 19.64/3.01      inference(light_normalisation,[status(thm)],[c_7947,c_7308]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_7999,plain,
% 19.64/3.01      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,sK2) ),
% 19.64/3.01      inference(demodulation,[status(thm)],[c_7998,c_4,c_6]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_10,negated_conjecture,
% 19.64/3.01      ( r1_tarski(sK0,sK1) ),
% 19.64/3.01      inference(cnf_transformation,[],[f28]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_93,plain,
% 19.64/3.01      ( k3_xboole_0(X0,X1) = X0 | sK1 != X1 | sK0 != X0 ),
% 19.64/3.01      inference(resolution_lifted,[status(thm)],[c_2,c_10]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_94,plain,
% 19.64/3.01      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 19.64/3.01      inference(unflattening,[status(thm)],[c_93]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_1409,plain,
% 19.64/3.01      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK0)) ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_94,c_0]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_1415,plain,
% 19.64/3.01      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = sK1 ),
% 19.64/3.01      inference(demodulation,[status(thm)],[c_1409,c_4,c_6]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_1542,plain,
% 19.64/3.01      ( k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))))))) = k5_xboole_0(k5_xboole_0(sK0,X0),k3_xboole_0(k5_xboole_0(sK0,X0),sK1)) ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_1415,c_7]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_24866,plain,
% 19.64/3.01      ( k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_7999,c_1542]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_1408,plain,
% 19.64/3.01      ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_89,c_0]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_1418,plain,
% 19.64/3.01      ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK1 ),
% 19.64/3.01      inference(demodulation,[status(thm)],[c_1408,c_4,c_6]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_1560,plain,
% 19.64/3.01      ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK1 ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_1,c_1418]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_1571,plain,
% 19.64/3.01      ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK1 ),
% 19.64/3.01      inference(light_normalisation,[status(thm)],[c_1560,c_89]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_25039,plain,
% 19.64/3.01      ( k5_xboole_0(k5_xboole_0(sK0,sK0),k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK0,sK0)))) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) ),
% 19.64/3.01      inference(light_normalisation,[status(thm)],[c_24866,c_89,c_94,c_1571]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_25040,plain,
% 19.64/3.01      ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) = k1_xboole_0 ),
% 19.64/3.01      inference(demodulation,[status(thm)],[c_25039,c_6,c_2400,c_7084]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_8,negated_conjecture,
% 19.64/3.01      ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
% 19.64/3.01      inference(cnf_transformation,[],[f30]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_103,plain,
% 19.64/3.01      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != sK1
% 19.64/3.01      | k5_xboole_0(sK0,sK2) != X0 ),
% 19.64/3.01      inference(resolution_lifted,[status(thm)],[c_5,c_8]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_104,plain,
% 19.64/3.01      ( k5_xboole_0(k5_xboole_0(sK0,sK2),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,sK2)))) != sK1 ),
% 19.64/3.01      inference(unflattening,[status(thm)],[c_103]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_1410,plain,
% 19.64/3.01      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),X0))) != sK1 ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_0,c_104]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_25830,plain,
% 19.64/3.01      ( k5_xboole_0(sK1,k1_xboole_0) != sK1 ),
% 19.64/3.01      inference(superposition,[status(thm)],[c_25040,c_1410]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_25868,plain,
% 19.64/3.01      ( sK1 != sK1 ),
% 19.64/3.01      inference(demodulation,[status(thm)],[c_25830,c_4]) ).
% 19.64/3.01  
% 19.64/3.01  cnf(c_25869,plain,
% 19.64/3.01      ( $false ),
% 19.64/3.01      inference(equality_resolution_simp,[status(thm)],[c_25868]) ).
% 19.64/3.01  
% 19.64/3.01  
% 19.64/3.01  % SZS output end CNFRefutation for theBenchmark.p
% 19.64/3.01  
% 19.64/3.01  ------                               Statistics
% 19.64/3.01  
% 19.64/3.01  ------ Selected
% 19.64/3.01  
% 19.64/3.01  total_time:                             2.13
% 19.64/3.01  
%------------------------------------------------------------------------------
