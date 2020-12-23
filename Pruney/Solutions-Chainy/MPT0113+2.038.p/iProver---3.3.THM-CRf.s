%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:48 EST 2020

% Result     : Theorem 39.24s
% Output     : CNFRefutation 39.24s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 168 expanded)
%              Number of clauses        :   49 (  63 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  162 ( 296 expanded)
%              Number of equality atoms :   95 ( 147 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f30,f25])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).

fof(f32,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f32,f25])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f27,f25,f25])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f31,f25])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f26,f34])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f33,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_349,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_572,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_349])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_347,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_466,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_347])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_350,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1481,plain,
    ( r1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0) != iProver_top
    | r1_xboole_0(sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_466,c_350])).

cnf(c_1933,plain,
    ( r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_572,c_1481])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_353,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1941,plain,
    ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1933,c_353])).

cnf(c_6,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_627,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_8686,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_627,c_6])).

cnf(c_96191,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_8686])).

cnf(c_158394,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(sK2,X0))) = k3_xboole_0(X0,k5_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1941,c_96191])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_363,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_7])).

cnf(c_161379,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(sK2,X0))) = k3_xboole_0(X0,sK0) ),
    inference(demodulation,[status(thm)],[c_158394,c_363])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_352,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3839,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_466,c_352])).

cnf(c_167046,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_161379,c_3839])).

cnf(c_116,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_932,plain,
    ( k5_xboole_0(X0,X1) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k5_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_3203,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_932])).

cnf(c_3204,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3203])).

cnf(c_673,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != X0
    | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_807,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k5_xboole_0(X0,X1)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0
    | k1_xboole_0 != k5_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_1867,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,k3_xboole_0(sK1,sK0))
    | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0
    | k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_1415,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_119,plain,
    ( X0 != X1
    | X2 != X3
    | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_808,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(X0,X1)
    | k3_xboole_0(sK0,sK1) != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_943,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,X0)
    | k3_xboole_0(sK0,sK1) != X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_1414,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0))
    | k3_xboole_0(sK0,sK1) != k3_xboole_0(sK1,sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_115,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_675,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_115])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_522,plain,
    ( r1_tarski(sK0,sK1)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_518,plain,
    ( r1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_447,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | r1_xboole_0(X0,X2)
    | ~ r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_489,plain,
    ( ~ r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ r1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK2)
    | r1_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(c_125,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_115])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_167046,c_3204,c_1867,c_1415,c_1414,c_675,c_522,c_518,c_489,c_125,c_10,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 39.24/5.53  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.24/5.53  
% 39.24/5.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.24/5.53  
% 39.24/5.53  ------  iProver source info
% 39.24/5.53  
% 39.24/5.53  git: date: 2020-06-30 10:37:57 +0100
% 39.24/5.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.24/5.53  git: non_committed_changes: false
% 39.24/5.53  git: last_make_outside_of_git: false
% 39.24/5.53  
% 39.24/5.53  ------ 
% 39.24/5.53  ------ Parsing...
% 39.24/5.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.24/5.53  
% 39.24/5.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 39.24/5.53  
% 39.24/5.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.24/5.53  
% 39.24/5.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.24/5.53  ------ Proving...
% 39.24/5.53  ------ Problem Properties 
% 39.24/5.53  
% 39.24/5.53  
% 39.24/5.53  clauses                                 12
% 39.24/5.53  conjectures                             2
% 39.24/5.53  EPR                                     2
% 39.24/5.53  Horn                                    12
% 39.24/5.53  unary                                   6
% 39.24/5.53  binary                                  5
% 39.24/5.53  lits                                    19
% 39.24/5.53  lits eq                                 8
% 39.24/5.53  fd_pure                                 0
% 39.24/5.54  fd_pseudo                               0
% 39.24/5.54  fd_cond                                 0
% 39.24/5.54  fd_pseudo_cond                          0
% 39.24/5.54  AC symbols                              0
% 39.24/5.54  
% 39.24/5.54  ------ Input Options Time Limit: Unbounded
% 39.24/5.54  
% 39.24/5.54  
% 39.24/5.54  ------ 
% 39.24/5.54  Current options:
% 39.24/5.54  ------ 
% 39.24/5.54  
% 39.24/5.54  
% 39.24/5.54  
% 39.24/5.54  
% 39.24/5.54  ------ Proving...
% 39.24/5.54  
% 39.24/5.54  
% 39.24/5.54  % SZS status Theorem for theBenchmark.p
% 39.24/5.54  
% 39.24/5.54  % SZS output start CNFRefutation for theBenchmark.p
% 39.24/5.54  
% 39.24/5.54  fof(f1,axiom,(
% 39.24/5.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 39.24/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.24/5.54  
% 39.24/5.54  fof(f20,plain,(
% 39.24/5.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 39.24/5.54    inference(cnf_transformation,[],[f1])).
% 39.24/5.54  
% 39.24/5.54  fof(f9,axiom,(
% 39.24/5.54    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 39.24/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.24/5.54  
% 39.24/5.54  fof(f30,plain,(
% 39.24/5.54    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 39.24/5.54    inference(cnf_transformation,[],[f9])).
% 39.24/5.54  
% 39.24/5.54  fof(f4,axiom,(
% 39.24/5.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 39.24/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.24/5.54  
% 39.24/5.54  fof(f25,plain,(
% 39.24/5.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 39.24/5.54    inference(cnf_transformation,[],[f4])).
% 39.24/5.54  
% 39.24/5.54  fof(f40,plain,(
% 39.24/5.54    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 39.24/5.54    inference(definition_unfolding,[],[f30,f25])).
% 39.24/5.54  
% 39.24/5.54  fof(f11,conjecture,(
% 39.24/5.54    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 39.24/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.24/5.54  
% 39.24/5.54  fof(f12,negated_conjecture,(
% 39.24/5.54    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 39.24/5.54    inference(negated_conjecture,[],[f11])).
% 39.24/5.54  
% 39.24/5.54  fof(f15,plain,(
% 39.24/5.54    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 39.24/5.54    inference(ennf_transformation,[],[f12])).
% 39.24/5.54  
% 39.24/5.54  fof(f18,plain,(
% 39.24/5.54    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 39.24/5.54    introduced(choice_axiom,[])).
% 39.24/5.54  
% 39.24/5.54  fof(f19,plain,(
% 39.24/5.54    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 39.24/5.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).
% 39.24/5.54  
% 39.24/5.54  fof(f32,plain,(
% 39.24/5.54    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 39.24/5.54    inference(cnf_transformation,[],[f19])).
% 39.24/5.54  
% 39.24/5.54  fof(f41,plain,(
% 39.24/5.54    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 39.24/5.54    inference(definition_unfolding,[],[f32,f25])).
% 39.24/5.54  
% 39.24/5.54  fof(f8,axiom,(
% 39.24/5.54    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 39.24/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.24/5.54  
% 39.24/5.54  fof(f13,plain,(
% 39.24/5.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 39.24/5.54    inference(ennf_transformation,[],[f8])).
% 39.24/5.54  
% 39.24/5.54  fof(f14,plain,(
% 39.24/5.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 39.24/5.54    inference(flattening,[],[f13])).
% 39.24/5.54  
% 39.24/5.54  fof(f29,plain,(
% 39.24/5.54    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 39.24/5.54    inference(cnf_transformation,[],[f14])).
% 39.24/5.54  
% 39.24/5.54  fof(f2,axiom,(
% 39.24/5.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 39.24/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.24/5.54  
% 39.24/5.54  fof(f16,plain,(
% 39.24/5.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 39.24/5.54    inference(nnf_transformation,[],[f2])).
% 39.24/5.54  
% 39.24/5.54  fof(f21,plain,(
% 39.24/5.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 39.24/5.54    inference(cnf_transformation,[],[f16])).
% 39.24/5.54  
% 39.24/5.54  fof(f6,axiom,(
% 39.24/5.54    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 39.24/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.24/5.54  
% 39.24/5.54  fof(f27,plain,(
% 39.24/5.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 39.24/5.54    inference(cnf_transformation,[],[f6])).
% 39.24/5.54  
% 39.24/5.54  fof(f38,plain,(
% 39.24/5.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 39.24/5.54    inference(definition_unfolding,[],[f27,f25,f25])).
% 39.24/5.54  
% 39.24/5.54  fof(f5,axiom,(
% 39.24/5.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 39.24/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.24/5.54  
% 39.24/5.54  fof(f26,plain,(
% 39.24/5.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.24/5.54    inference(cnf_transformation,[],[f5])).
% 39.24/5.54  
% 39.24/5.54  fof(f10,axiom,(
% 39.24/5.54    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 39.24/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.24/5.54  
% 39.24/5.54  fof(f31,plain,(
% 39.24/5.54    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 39.24/5.54    inference(cnf_transformation,[],[f10])).
% 39.24/5.54  
% 39.24/5.54  fof(f34,plain,(
% 39.24/5.54    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 39.24/5.54    inference(definition_unfolding,[],[f31,f25])).
% 39.24/5.54  
% 39.24/5.54  fof(f37,plain,(
% 39.24/5.54    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 39.24/5.54    inference(definition_unfolding,[],[f26,f34])).
% 39.24/5.54  
% 39.24/5.54  fof(f7,axiom,(
% 39.24/5.54    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 39.24/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.24/5.54  
% 39.24/5.54  fof(f28,plain,(
% 39.24/5.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 39.24/5.54    inference(cnf_transformation,[],[f7])).
% 39.24/5.54  
% 39.24/5.54  fof(f39,plain,(
% 39.24/5.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 39.24/5.54    inference(definition_unfolding,[],[f28,f25])).
% 39.24/5.54  
% 39.24/5.54  fof(f3,axiom,(
% 39.24/5.54    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 39.24/5.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.24/5.54  
% 39.24/5.54  fof(f17,plain,(
% 39.24/5.54    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 39.24/5.54    inference(nnf_transformation,[],[f3])).
% 39.24/5.54  
% 39.24/5.54  fof(f24,plain,(
% 39.24/5.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 39.24/5.54    inference(cnf_transformation,[],[f17])).
% 39.24/5.54  
% 39.24/5.54  fof(f35,plain,(
% 39.24/5.54    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 39.24/5.54    inference(definition_unfolding,[],[f24,f25])).
% 39.24/5.54  
% 39.24/5.54  fof(f23,plain,(
% 39.24/5.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 39.24/5.54    inference(cnf_transformation,[],[f17])).
% 39.24/5.54  
% 39.24/5.54  fof(f36,plain,(
% 39.24/5.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 39.24/5.54    inference(definition_unfolding,[],[f23,f25])).
% 39.24/5.54  
% 39.24/5.54  fof(f33,plain,(
% 39.24/5.54    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 39.24/5.54    inference(cnf_transformation,[],[f19])).
% 39.24/5.54  
% 39.24/5.54  cnf(c_0,plain,
% 39.24/5.54      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 39.24/5.54      inference(cnf_transformation,[],[f20]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_9,plain,
% 39.24/5.54      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 39.24/5.54      inference(cnf_transformation,[],[f40]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_349,plain,
% 39.24/5.54      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 39.24/5.54      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_572,plain,
% 39.24/5.54      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
% 39.24/5.54      inference(superposition,[status(thm)],[c_0,c_349]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_11,negated_conjecture,
% 39.24/5.54      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 39.24/5.54      inference(cnf_transformation,[],[f41]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_347,plain,
% 39.24/5.54      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 39.24/5.54      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_466,plain,
% 39.24/5.54      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
% 39.24/5.54      inference(demodulation,[status(thm)],[c_0,c_347]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_8,plain,
% 39.24/5.54      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 39.24/5.54      inference(cnf_transformation,[],[f29]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_350,plain,
% 39.24/5.54      ( r1_tarski(X0,X1) != iProver_top
% 39.24/5.54      | r1_xboole_0(X1,X2) != iProver_top
% 39.24/5.54      | r1_xboole_0(X0,X2) = iProver_top ),
% 39.24/5.54      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_1481,plain,
% 39.24/5.54      ( r1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),X0) != iProver_top
% 39.24/5.54      | r1_xboole_0(sK0,X0) = iProver_top ),
% 39.24/5.54      inference(superposition,[status(thm)],[c_466,c_350]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_1933,plain,
% 39.24/5.54      ( r1_xboole_0(sK0,sK2) = iProver_top ),
% 39.24/5.54      inference(superposition,[status(thm)],[c_572,c_1481]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_2,plain,
% 39.24/5.54      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 39.24/5.54      inference(cnf_transformation,[],[f21]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_353,plain,
% 39.24/5.54      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 39.24/5.54      | r1_xboole_0(X0,X1) != iProver_top ),
% 39.24/5.54      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_1941,plain,
% 39.24/5.54      ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
% 39.24/5.54      inference(superposition,[status(thm)],[c_1933,c_353]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_6,plain,
% 39.24/5.54      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 39.24/5.54      inference(cnf_transformation,[],[f38]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_627,plain,
% 39.24/5.54      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 39.24/5.54      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_8686,plain,
% 39.24/5.54      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 39.24/5.54      inference(superposition,[status(thm)],[c_627,c_6]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_96191,plain,
% 39.24/5.54      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 39.24/5.54      inference(superposition,[status(thm)],[c_0,c_8686]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_158394,plain,
% 39.24/5.54      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(sK2,X0))) = k3_xboole_0(X0,k5_xboole_0(sK0,k1_xboole_0)) ),
% 39.24/5.54      inference(superposition,[status(thm)],[c_1941,c_96191]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_5,plain,
% 39.24/5.54      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 39.24/5.54      inference(cnf_transformation,[],[f37]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_7,plain,
% 39.24/5.54      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 39.24/5.54      inference(cnf_transformation,[],[f39]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_363,plain,
% 39.24/5.54      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.24/5.54      inference(light_normalisation,[status(thm)],[c_5,c_7]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_161379,plain,
% 39.24/5.54      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(sK2,X0))) = k3_xboole_0(X0,sK0) ),
% 39.24/5.54      inference(demodulation,[status(thm)],[c_158394,c_363]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_3,plain,
% 39.24/5.54      ( ~ r1_tarski(X0,X1)
% 39.24/5.54      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 39.24/5.54      inference(cnf_transformation,[],[f35]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_352,plain,
% 39.24/5.54      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 39.24/5.54      | r1_tarski(X0,X1) != iProver_top ),
% 39.24/5.54      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_3839,plain,
% 39.24/5.54      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = k1_xboole_0 ),
% 39.24/5.54      inference(superposition,[status(thm)],[c_466,c_352]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_167046,plain,
% 39.24/5.54      ( k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 39.24/5.54      inference(demodulation,[status(thm)],[c_161379,c_3839]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_116,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_932,plain,
% 39.24/5.54      ( k5_xboole_0(X0,X1) != X2
% 39.24/5.54      | k1_xboole_0 != X2
% 39.24/5.54      | k1_xboole_0 = k5_xboole_0(X0,X1) ),
% 39.24/5.54      inference(instantiation,[status(thm)],[c_116]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_3203,plain,
% 39.24/5.54      ( k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) != X0
% 39.24/5.54      | k1_xboole_0 != X0
% 39.24/5.54      | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
% 39.24/5.54      inference(instantiation,[status(thm)],[c_932]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_3204,plain,
% 39.24/5.54      ( k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) != k1_xboole_0
% 39.24/5.54      | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0))
% 39.24/5.54      | k1_xboole_0 != k1_xboole_0 ),
% 39.24/5.54      inference(instantiation,[status(thm)],[c_3203]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_673,plain,
% 39.24/5.54      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != X0
% 39.24/5.54      | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0
% 39.24/5.54      | k1_xboole_0 != X0 ),
% 39.24/5.54      inference(instantiation,[status(thm)],[c_116]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_807,plain,
% 39.24/5.54      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k5_xboole_0(X0,X1)
% 39.24/5.54      | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0
% 39.24/5.54      | k1_xboole_0 != k5_xboole_0(X0,X1) ),
% 39.24/5.54      inference(instantiation,[status(thm)],[c_673]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_1867,plain,
% 39.24/5.54      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,k3_xboole_0(sK1,sK0))
% 39.24/5.54      | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0
% 39.24/5.54      | k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
% 39.24/5.54      inference(instantiation,[status(thm)],[c_807]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_1415,plain,
% 39.24/5.54      ( k3_xboole_0(sK0,sK1) = k3_xboole_0(sK1,sK0) ),
% 39.24/5.54      inference(instantiation,[status(thm)],[c_0]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_119,plain,
% 39.24/5.54      ( X0 != X1 | X2 != X3 | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
% 39.24/5.54      theory(equality) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_808,plain,
% 39.24/5.54      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(X0,X1)
% 39.24/5.54      | k3_xboole_0(sK0,sK1) != X1
% 39.24/5.54      | sK0 != X0 ),
% 39.24/5.54      inference(instantiation,[status(thm)],[c_119]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_943,plain,
% 39.24/5.54      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,X0)
% 39.24/5.54      | k3_xboole_0(sK0,sK1) != X0
% 39.24/5.54      | sK0 != sK0 ),
% 39.24/5.54      inference(instantiation,[status(thm)],[c_808]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_1414,plain,
% 39.24/5.54      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0))
% 39.24/5.54      | k3_xboole_0(sK0,sK1) != k3_xboole_0(sK1,sK0)
% 39.24/5.54      | sK0 != sK0 ),
% 39.24/5.54      inference(instantiation,[status(thm)],[c_943]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_115,plain,( X0 = X0 ),theory(equality) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_675,plain,
% 39.24/5.54      ( sK0 = sK0 ),
% 39.24/5.54      inference(instantiation,[status(thm)],[c_115]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_4,plain,
% 39.24/5.54      ( r1_tarski(X0,X1)
% 39.24/5.54      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 39.24/5.54      inference(cnf_transformation,[],[f36]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_522,plain,
% 39.24/5.54      ( r1_tarski(sK0,sK1)
% 39.24/5.54      | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 39.24/5.54      inference(instantiation,[status(thm)],[c_4]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_518,plain,
% 39.24/5.54      ( r1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK2) ),
% 39.24/5.54      inference(instantiation,[status(thm)],[c_9]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_447,plain,
% 39.24/5.54      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 39.24/5.54      | r1_xboole_0(X0,X2)
% 39.24/5.54      | ~ r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
% 39.24/5.54      inference(instantiation,[status(thm)],[c_8]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_489,plain,
% 39.24/5.54      ( ~ r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
% 39.24/5.54      | ~ r1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK2)
% 39.24/5.54      | r1_xboole_0(sK0,sK2) ),
% 39.24/5.54      inference(instantiation,[status(thm)],[c_447]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_125,plain,
% 39.24/5.54      ( k1_xboole_0 = k1_xboole_0 ),
% 39.24/5.54      inference(instantiation,[status(thm)],[c_115]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(c_10,negated_conjecture,
% 39.24/5.54      ( ~ r1_tarski(sK0,sK1) | ~ r1_xboole_0(sK0,sK2) ),
% 39.24/5.54      inference(cnf_transformation,[],[f33]) ).
% 39.24/5.54  
% 39.24/5.54  cnf(contradiction,plain,
% 39.24/5.54      ( $false ),
% 39.24/5.54      inference(minisat,
% 39.24/5.54                [status(thm)],
% 39.24/5.54                [c_167046,c_3204,c_1867,c_1415,c_1414,c_675,c_522,c_518,
% 39.24/5.54                 c_489,c_125,c_10,c_11]) ).
% 39.24/5.54  
% 39.24/5.54  
% 39.24/5.54  % SZS output end CNFRefutation for theBenchmark.p
% 39.24/5.54  
% 39.24/5.54  ------                               Statistics
% 39.24/5.54  
% 39.24/5.54  ------ Selected
% 39.24/5.54  
% 39.24/5.54  total_time:                             4.765
% 39.24/5.54  
%------------------------------------------------------------------------------
