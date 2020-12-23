%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:48 EST 2020

% Result     : Theorem 31.75s
% Output     : CNFRefutation 31.75s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 226 expanded)
%              Number of clauses        :   43 (  54 expanded)
%              Number of leaves         :   19 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  165 ( 352 expanded)
%              Number of equality atoms :  149 ( 336 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 )
   => ( k1_tarski(sK1) != sK0
      & k1_xboole_0 != sK0
      & k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k1_tarski(sK1) != sK0
    & k1_xboole_0 != sK0
    & k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f37,plain,(
    k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f32,f40])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f31,f41])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f43])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f44])).

fof(f49,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f37,f24,f45])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f45,f45])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
     => k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f36,f24,f45])).

fof(f39,plain,(
    k1_tarski(sK1) != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK0 ),
    inference(definition_unfolding,[],[f39,f45])).

fof(f38,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_53,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_125,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != X0
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_167488,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
    | sK0 != k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_132,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_135,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_167359,plain,
    ( k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != sK0
    | sK0 = k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_135])).

cnf(c_167369,plain,
    ( k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != sK0
    | sK0 = k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_167359])).

cnf(c_302,plain,
    ( X0 != X1
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != X1
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_458,plain,
    ( X0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = X0
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_2213,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_458])).

cnf(c_8,negated_conjecture,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_119,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_354,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3,c_119])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_367,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_354,c_1])).

cnf(c_384,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k1_xboole_0) = sK0 ),
    inference(superposition,[status(thm)],[c_8,c_367])).

cnf(c_650,plain,
    ( k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_384,c_1])).

cnf(c_221,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_414,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_221])).

cnf(c_415,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_414])).

cnf(c_52,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_264,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_127,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_172,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
    | k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_127])).

cnf(c_175,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_167,plain,
    ( ~ r2_hidden(X0,sK0)
    | k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_169,plain,
    ( ~ r2_hidden(sK1,sK0)
    | k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_167])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_147,plain,
    ( r2_hidden(X0,sK0)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = sK0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_150,plain,
    ( r2_hidden(sK1,sK0)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = sK0 ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_146,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != sK0
    | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_135])).

cnf(c_148,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != sK0
    | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_136,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_60,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_55,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
    theory(equality)).

cnf(c_57,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_6,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_167488,c_167369,c_2213,c_650,c_415,c_264,c_175,c_169,c_150,c_148,c_136,c_60,c_57,c_6,c_7,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:35:37 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.34  % Running in FOF mode
% 31.75/4.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.75/4.49  
% 31.75/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.75/4.49  
% 31.75/4.49  ------  iProver source info
% 31.75/4.49  
% 31.75/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.75/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.75/4.49  git: non_committed_changes: false
% 31.75/4.49  git: last_make_outside_of_git: false
% 31.75/4.49  
% 31.75/4.49  ------ 
% 31.75/4.49  
% 31.75/4.49  ------ Input Options
% 31.75/4.49  
% 31.75/4.49  --out_options                           all
% 31.75/4.49  --tptp_safe_out                         true
% 31.75/4.49  --problem_path                          ""
% 31.75/4.49  --include_path                          ""
% 31.75/4.49  --clausifier                            res/vclausify_rel
% 31.75/4.49  --clausifier_options                    --mode clausify
% 31.75/4.49  --stdin                                 false
% 31.75/4.49  --stats_out                             all
% 31.75/4.49  
% 31.75/4.49  ------ General Options
% 31.75/4.49  
% 31.75/4.49  --fof                                   false
% 31.75/4.49  --time_out_real                         305.
% 31.75/4.49  --time_out_virtual                      -1.
% 31.75/4.49  --symbol_type_check                     false
% 31.75/4.49  --clausify_out                          false
% 31.75/4.49  --sig_cnt_out                           false
% 31.75/4.49  --trig_cnt_out                          false
% 31.75/4.49  --trig_cnt_out_tolerance                1.
% 31.75/4.49  --trig_cnt_out_sk_spl                   false
% 31.75/4.49  --abstr_cl_out                          false
% 31.75/4.49  
% 31.75/4.49  ------ Global Options
% 31.75/4.49  
% 31.75/4.49  --schedule                              default
% 31.75/4.49  --add_important_lit                     false
% 31.75/4.49  --prop_solver_per_cl                    1000
% 31.75/4.49  --min_unsat_core                        false
% 31.75/4.49  --soft_assumptions                      false
% 31.75/4.49  --soft_lemma_size                       3
% 31.75/4.49  --prop_impl_unit_size                   0
% 31.75/4.49  --prop_impl_unit                        []
% 31.75/4.49  --share_sel_clauses                     true
% 31.75/4.49  --reset_solvers                         false
% 31.75/4.49  --bc_imp_inh                            [conj_cone]
% 31.75/4.49  --conj_cone_tolerance                   3.
% 31.75/4.49  --extra_neg_conj                        none
% 31.75/4.49  --large_theory_mode                     true
% 31.75/4.49  --prolific_symb_bound                   200
% 31.75/4.49  --lt_threshold                          2000
% 31.75/4.49  --clause_weak_htbl                      true
% 31.75/4.49  --gc_record_bc_elim                     false
% 31.75/4.49  
% 31.75/4.49  ------ Preprocessing Options
% 31.75/4.49  
% 31.75/4.49  --preprocessing_flag                    true
% 31.75/4.49  --time_out_prep_mult                    0.1
% 31.75/4.49  --splitting_mode                        input
% 31.75/4.49  --splitting_grd                         true
% 31.75/4.49  --splitting_cvd                         false
% 31.75/4.49  --splitting_cvd_svl                     false
% 31.75/4.49  --splitting_nvd                         32
% 31.75/4.49  --sub_typing                            true
% 31.75/4.49  --prep_gs_sim                           true
% 31.75/4.49  --prep_unflatten                        true
% 31.75/4.49  --prep_res_sim                          true
% 31.75/4.49  --prep_upred                            true
% 31.75/4.49  --prep_sem_filter                       exhaustive
% 31.75/4.49  --prep_sem_filter_out                   false
% 31.75/4.49  --pred_elim                             true
% 31.75/4.49  --res_sim_input                         true
% 31.75/4.49  --eq_ax_congr_red                       true
% 31.75/4.49  --pure_diseq_elim                       true
% 31.75/4.49  --brand_transform                       false
% 31.75/4.49  --non_eq_to_eq                          false
% 31.75/4.49  --prep_def_merge                        true
% 31.75/4.49  --prep_def_merge_prop_impl              false
% 31.75/4.49  --prep_def_merge_mbd                    true
% 31.75/4.49  --prep_def_merge_tr_red                 false
% 31.75/4.49  --prep_def_merge_tr_cl                  false
% 31.75/4.49  --smt_preprocessing                     true
% 31.75/4.49  --smt_ac_axioms                         fast
% 31.75/4.49  --preprocessed_out                      false
% 31.75/4.49  --preprocessed_stats                    false
% 31.75/4.49  
% 31.75/4.49  ------ Abstraction refinement Options
% 31.75/4.49  
% 31.75/4.49  --abstr_ref                             []
% 31.75/4.49  --abstr_ref_prep                        false
% 31.75/4.49  --abstr_ref_until_sat                   false
% 31.75/4.49  --abstr_ref_sig_restrict                funpre
% 31.75/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.75/4.49  --abstr_ref_under                       []
% 31.75/4.49  
% 31.75/4.49  ------ SAT Options
% 31.75/4.49  
% 31.75/4.49  --sat_mode                              false
% 31.75/4.49  --sat_fm_restart_options                ""
% 31.75/4.49  --sat_gr_def                            false
% 31.75/4.49  --sat_epr_types                         true
% 31.75/4.49  --sat_non_cyclic_types                  false
% 31.75/4.49  --sat_finite_models                     false
% 31.75/4.49  --sat_fm_lemmas                         false
% 31.75/4.49  --sat_fm_prep                           false
% 31.75/4.49  --sat_fm_uc_incr                        true
% 31.75/4.49  --sat_out_model                         small
% 31.75/4.49  --sat_out_clauses                       false
% 31.75/4.49  
% 31.75/4.49  ------ QBF Options
% 31.75/4.49  
% 31.75/4.49  --qbf_mode                              false
% 31.75/4.49  --qbf_elim_univ                         false
% 31.75/4.49  --qbf_dom_inst                          none
% 31.75/4.49  --qbf_dom_pre_inst                      false
% 31.75/4.49  --qbf_sk_in                             false
% 31.75/4.49  --qbf_pred_elim                         true
% 31.75/4.49  --qbf_split                             512
% 31.75/4.49  
% 31.75/4.49  ------ BMC1 Options
% 31.75/4.49  
% 31.75/4.49  --bmc1_incremental                      false
% 31.75/4.49  --bmc1_axioms                           reachable_all
% 31.75/4.49  --bmc1_min_bound                        0
% 31.75/4.49  --bmc1_max_bound                        -1
% 31.75/4.49  --bmc1_max_bound_default                -1
% 31.75/4.49  --bmc1_symbol_reachability              true
% 31.75/4.49  --bmc1_property_lemmas                  false
% 31.75/4.49  --bmc1_k_induction                      false
% 31.75/4.49  --bmc1_non_equiv_states                 false
% 31.75/4.49  --bmc1_deadlock                         false
% 31.75/4.49  --bmc1_ucm                              false
% 31.75/4.49  --bmc1_add_unsat_core                   none
% 31.75/4.49  --bmc1_unsat_core_children              false
% 31.75/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.75/4.49  --bmc1_out_stat                         full
% 31.75/4.49  --bmc1_ground_init                      false
% 31.75/4.49  --bmc1_pre_inst_next_state              false
% 31.75/4.49  --bmc1_pre_inst_state                   false
% 31.75/4.49  --bmc1_pre_inst_reach_state             false
% 31.75/4.49  --bmc1_out_unsat_core                   false
% 31.75/4.49  --bmc1_aig_witness_out                  false
% 31.75/4.49  --bmc1_verbose                          false
% 31.75/4.49  --bmc1_dump_clauses_tptp                false
% 31.75/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.75/4.49  --bmc1_dump_file                        -
% 31.75/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.75/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.75/4.49  --bmc1_ucm_extend_mode                  1
% 31.75/4.49  --bmc1_ucm_init_mode                    2
% 31.75/4.49  --bmc1_ucm_cone_mode                    none
% 31.75/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.75/4.49  --bmc1_ucm_relax_model                  4
% 31.75/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.75/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.75/4.49  --bmc1_ucm_layered_model                none
% 31.75/4.49  --bmc1_ucm_max_lemma_size               10
% 31.75/4.49  
% 31.75/4.49  ------ AIG Options
% 31.75/4.49  
% 31.75/4.49  --aig_mode                              false
% 31.75/4.49  
% 31.75/4.49  ------ Instantiation Options
% 31.75/4.49  
% 31.75/4.49  --instantiation_flag                    true
% 31.75/4.49  --inst_sos_flag                         false
% 31.75/4.49  --inst_sos_phase                        true
% 31.75/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.75/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.75/4.49  --inst_lit_sel_side                     num_symb
% 31.75/4.49  --inst_solver_per_active                1400
% 31.75/4.49  --inst_solver_calls_frac                1.
% 31.75/4.49  --inst_passive_queue_type               priority_queues
% 31.75/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.75/4.49  --inst_passive_queues_freq              [25;2]
% 31.75/4.49  --inst_dismatching                      true
% 31.75/4.49  --inst_eager_unprocessed_to_passive     true
% 31.75/4.49  --inst_prop_sim_given                   true
% 31.75/4.49  --inst_prop_sim_new                     false
% 31.75/4.49  --inst_subs_new                         false
% 31.75/4.49  --inst_eq_res_simp                      false
% 31.75/4.49  --inst_subs_given                       false
% 31.75/4.49  --inst_orphan_elimination               true
% 31.75/4.49  --inst_learning_loop_flag               true
% 31.75/4.49  --inst_learning_start                   3000
% 31.75/4.49  --inst_learning_factor                  2
% 31.75/4.49  --inst_start_prop_sim_after_learn       3
% 31.75/4.49  --inst_sel_renew                        solver
% 31.75/4.49  --inst_lit_activity_flag                true
% 31.75/4.49  --inst_restr_to_given                   false
% 31.75/4.49  --inst_activity_threshold               500
% 31.75/4.49  --inst_out_proof                        true
% 31.75/4.49  
% 31.75/4.49  ------ Resolution Options
% 31.75/4.49  
% 31.75/4.49  --resolution_flag                       true
% 31.75/4.49  --res_lit_sel                           adaptive
% 31.75/4.49  --res_lit_sel_side                      none
% 31.75/4.49  --res_ordering                          kbo
% 31.75/4.49  --res_to_prop_solver                    active
% 31.75/4.49  --res_prop_simpl_new                    false
% 31.75/4.49  --res_prop_simpl_given                  true
% 31.75/4.49  --res_passive_queue_type                priority_queues
% 31.75/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.75/4.49  --res_passive_queues_freq               [15;5]
% 31.75/4.49  --res_forward_subs                      full
% 31.75/4.49  --res_backward_subs                     full
% 31.75/4.49  --res_forward_subs_resolution           true
% 31.75/4.49  --res_backward_subs_resolution          true
% 31.75/4.49  --res_orphan_elimination                true
% 31.75/4.49  --res_time_limit                        2.
% 31.75/4.49  --res_out_proof                         true
% 31.75/4.49  
% 31.75/4.49  ------ Superposition Options
% 31.75/4.49  
% 31.75/4.49  --superposition_flag                    true
% 31.75/4.49  --sup_passive_queue_type                priority_queues
% 31.75/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.75/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.75/4.49  --demod_completeness_check              fast
% 31.75/4.49  --demod_use_ground                      true
% 31.75/4.49  --sup_to_prop_solver                    passive
% 31.75/4.49  --sup_prop_simpl_new                    true
% 31.75/4.49  --sup_prop_simpl_given                  true
% 31.75/4.49  --sup_fun_splitting                     false
% 31.75/4.49  --sup_smt_interval                      50000
% 31.75/4.49  
% 31.75/4.49  ------ Superposition Simplification Setup
% 31.75/4.49  
% 31.75/4.49  --sup_indices_passive                   []
% 31.75/4.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.75/4.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.75/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.75/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.75/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.75/4.49  --sup_full_bw                           [BwDemod]
% 31.75/4.49  --sup_immed_triv                        [TrivRules]
% 31.75/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.75/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.75/4.49  --sup_immed_bw_main                     []
% 31.75/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.75/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.75/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.75/4.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.75/4.49  
% 31.75/4.49  ------ Combination Options
% 31.75/4.49  
% 31.75/4.49  --comb_res_mult                         3
% 31.75/4.49  --comb_sup_mult                         2
% 31.75/4.49  --comb_inst_mult                        10
% 31.75/4.49  
% 31.75/4.49  ------ Debug Options
% 31.75/4.49  
% 31.75/4.49  --dbg_backtrace                         false
% 31.75/4.49  --dbg_dump_prop_clauses                 false
% 31.75/4.49  --dbg_dump_prop_clauses_file            -
% 31.75/4.49  --dbg_out_stat                          false
% 31.75/4.49  ------ Parsing...
% 31.75/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.75/4.49  
% 31.75/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 31.75/4.49  
% 31.75/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.75/4.49  
% 31.75/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.75/4.49  ------ Proving...
% 31.75/4.49  ------ Problem Properties 
% 31.75/4.49  
% 31.75/4.49  
% 31.75/4.49  clauses                                 9
% 31.75/4.49  conjectures                             3
% 31.75/4.49  EPR                                     1
% 31.75/4.49  Horn                                    8
% 31.75/4.49  unary                                   7
% 31.75/4.49  binary                                  2
% 31.75/4.49  lits                                    11
% 31.75/4.49  lits eq                                 9
% 31.75/4.49  fd_pure                                 0
% 31.75/4.49  fd_pseudo                               0
% 31.75/4.49  fd_cond                                 0
% 31.75/4.49  fd_pseudo_cond                          0
% 31.75/4.49  AC symbols                              1
% 31.75/4.49  
% 31.75/4.49  ------ Schedule dynamic 5 is on 
% 31.75/4.49  
% 31.75/4.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.75/4.49  
% 31.75/4.49  
% 31.75/4.49  ------ 
% 31.75/4.49  Current options:
% 31.75/4.49  ------ 
% 31.75/4.49  
% 31.75/4.49  ------ Input Options
% 31.75/4.49  
% 31.75/4.49  --out_options                           all
% 31.75/4.49  --tptp_safe_out                         true
% 31.75/4.49  --problem_path                          ""
% 31.75/4.49  --include_path                          ""
% 31.75/4.49  --clausifier                            res/vclausify_rel
% 31.75/4.49  --clausifier_options                    --mode clausify
% 31.75/4.49  --stdin                                 false
% 31.75/4.49  --stats_out                             all
% 31.75/4.49  
% 31.75/4.49  ------ General Options
% 31.75/4.49  
% 31.75/4.49  --fof                                   false
% 31.75/4.49  --time_out_real                         305.
% 31.75/4.49  --time_out_virtual                      -1.
% 31.75/4.49  --symbol_type_check                     false
% 31.75/4.49  --clausify_out                          false
% 31.75/4.49  --sig_cnt_out                           false
% 31.75/4.49  --trig_cnt_out                          false
% 31.75/4.49  --trig_cnt_out_tolerance                1.
% 31.75/4.49  --trig_cnt_out_sk_spl                   false
% 31.75/4.49  --abstr_cl_out                          false
% 31.75/4.49  
% 31.75/4.49  ------ Global Options
% 31.75/4.49  
% 31.75/4.49  --schedule                              default
% 31.75/4.49  --add_important_lit                     false
% 31.75/4.49  --prop_solver_per_cl                    1000
% 31.75/4.49  --min_unsat_core                        false
% 31.75/4.49  --soft_assumptions                      false
% 31.75/4.49  --soft_lemma_size                       3
% 31.75/4.49  --prop_impl_unit_size                   0
% 31.75/4.49  --prop_impl_unit                        []
% 31.75/4.49  --share_sel_clauses                     true
% 31.75/4.49  --reset_solvers                         false
% 31.75/4.49  --bc_imp_inh                            [conj_cone]
% 31.75/4.49  --conj_cone_tolerance                   3.
% 31.75/4.49  --extra_neg_conj                        none
% 31.75/4.49  --large_theory_mode                     true
% 31.75/4.49  --prolific_symb_bound                   200
% 31.75/4.49  --lt_threshold                          2000
% 31.75/4.49  --clause_weak_htbl                      true
% 31.75/4.49  --gc_record_bc_elim                     false
% 31.75/4.49  
% 31.75/4.49  ------ Preprocessing Options
% 31.75/4.49  
% 31.75/4.49  --preprocessing_flag                    true
% 31.75/4.49  --time_out_prep_mult                    0.1
% 31.75/4.49  --splitting_mode                        input
% 31.75/4.49  --splitting_grd                         true
% 31.75/4.49  --splitting_cvd                         false
% 31.75/4.49  --splitting_cvd_svl                     false
% 31.75/4.49  --splitting_nvd                         32
% 31.75/4.49  --sub_typing                            true
% 31.75/4.49  --prep_gs_sim                           true
% 31.75/4.49  --prep_unflatten                        true
% 31.75/4.49  --prep_res_sim                          true
% 31.75/4.49  --prep_upred                            true
% 31.75/4.49  --prep_sem_filter                       exhaustive
% 31.75/4.49  --prep_sem_filter_out                   false
% 31.75/4.49  --pred_elim                             true
% 31.75/4.49  --res_sim_input                         true
% 31.75/4.49  --eq_ax_congr_red                       true
% 31.75/4.49  --pure_diseq_elim                       true
% 31.75/4.49  --brand_transform                       false
% 31.75/4.49  --non_eq_to_eq                          false
% 31.75/4.49  --prep_def_merge                        true
% 31.75/4.49  --prep_def_merge_prop_impl              false
% 31.75/4.49  --prep_def_merge_mbd                    true
% 31.75/4.49  --prep_def_merge_tr_red                 false
% 31.75/4.49  --prep_def_merge_tr_cl                  false
% 31.75/4.49  --smt_preprocessing                     true
% 31.75/4.49  --smt_ac_axioms                         fast
% 31.75/4.49  --preprocessed_out                      false
% 31.75/4.49  --preprocessed_stats                    false
% 31.75/4.49  
% 31.75/4.49  ------ Abstraction refinement Options
% 31.75/4.49  
% 31.75/4.49  --abstr_ref                             []
% 31.75/4.49  --abstr_ref_prep                        false
% 31.75/4.49  --abstr_ref_until_sat                   false
% 31.75/4.49  --abstr_ref_sig_restrict                funpre
% 31.75/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.75/4.49  --abstr_ref_under                       []
% 31.75/4.49  
% 31.75/4.49  ------ SAT Options
% 31.75/4.49  
% 31.75/4.49  --sat_mode                              false
% 31.75/4.49  --sat_fm_restart_options                ""
% 31.75/4.49  --sat_gr_def                            false
% 31.75/4.49  --sat_epr_types                         true
% 31.75/4.49  --sat_non_cyclic_types                  false
% 31.75/4.49  --sat_finite_models                     false
% 31.75/4.49  --sat_fm_lemmas                         false
% 31.75/4.49  --sat_fm_prep                           false
% 31.75/4.49  --sat_fm_uc_incr                        true
% 31.75/4.49  --sat_out_model                         small
% 31.75/4.49  --sat_out_clauses                       false
% 31.75/4.49  
% 31.75/4.49  ------ QBF Options
% 31.75/4.49  
% 31.75/4.49  --qbf_mode                              false
% 31.75/4.49  --qbf_elim_univ                         false
% 31.75/4.49  --qbf_dom_inst                          none
% 31.75/4.49  --qbf_dom_pre_inst                      false
% 31.75/4.49  --qbf_sk_in                             false
% 31.75/4.49  --qbf_pred_elim                         true
% 31.75/4.49  --qbf_split                             512
% 31.75/4.49  
% 31.75/4.49  ------ BMC1 Options
% 31.75/4.49  
% 31.75/4.49  --bmc1_incremental                      false
% 31.75/4.49  --bmc1_axioms                           reachable_all
% 31.75/4.49  --bmc1_min_bound                        0
% 31.75/4.49  --bmc1_max_bound                        -1
% 31.75/4.49  --bmc1_max_bound_default                -1
% 31.75/4.49  --bmc1_symbol_reachability              true
% 31.75/4.49  --bmc1_property_lemmas                  false
% 31.75/4.49  --bmc1_k_induction                      false
% 31.75/4.49  --bmc1_non_equiv_states                 false
% 31.75/4.49  --bmc1_deadlock                         false
% 31.75/4.49  --bmc1_ucm                              false
% 31.75/4.49  --bmc1_add_unsat_core                   none
% 31.75/4.49  --bmc1_unsat_core_children              false
% 31.75/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.75/4.49  --bmc1_out_stat                         full
% 31.75/4.49  --bmc1_ground_init                      false
% 31.75/4.49  --bmc1_pre_inst_next_state              false
% 31.75/4.49  --bmc1_pre_inst_state                   false
% 31.75/4.49  --bmc1_pre_inst_reach_state             false
% 31.75/4.49  --bmc1_out_unsat_core                   false
% 31.75/4.49  --bmc1_aig_witness_out                  false
% 31.75/4.49  --bmc1_verbose                          false
% 31.75/4.49  --bmc1_dump_clauses_tptp                false
% 31.75/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.75/4.49  --bmc1_dump_file                        -
% 31.75/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.75/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.75/4.49  --bmc1_ucm_extend_mode                  1
% 31.75/4.49  --bmc1_ucm_init_mode                    2
% 31.75/4.49  --bmc1_ucm_cone_mode                    none
% 31.75/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.75/4.49  --bmc1_ucm_relax_model                  4
% 31.75/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.75/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.75/4.49  --bmc1_ucm_layered_model                none
% 31.75/4.49  --bmc1_ucm_max_lemma_size               10
% 31.75/4.49  
% 31.75/4.49  ------ AIG Options
% 31.75/4.49  
% 31.75/4.49  --aig_mode                              false
% 31.75/4.49  
% 31.75/4.49  ------ Instantiation Options
% 31.75/4.49  
% 31.75/4.49  --instantiation_flag                    true
% 31.75/4.49  --inst_sos_flag                         false
% 31.75/4.49  --inst_sos_phase                        true
% 31.75/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.75/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.75/4.49  --inst_lit_sel_side                     none
% 31.75/4.49  --inst_solver_per_active                1400
% 31.75/4.49  --inst_solver_calls_frac                1.
% 31.75/4.49  --inst_passive_queue_type               priority_queues
% 31.75/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.75/4.49  --inst_passive_queues_freq              [25;2]
% 31.75/4.49  --inst_dismatching                      true
% 31.75/4.49  --inst_eager_unprocessed_to_passive     true
% 31.75/4.49  --inst_prop_sim_given                   true
% 31.75/4.49  --inst_prop_sim_new                     false
% 31.75/4.49  --inst_subs_new                         false
% 31.75/4.49  --inst_eq_res_simp                      false
% 31.75/4.49  --inst_subs_given                       false
% 31.75/4.49  --inst_orphan_elimination               true
% 31.75/4.49  --inst_learning_loop_flag               true
% 31.75/4.49  --inst_learning_start                   3000
% 31.75/4.49  --inst_learning_factor                  2
% 31.75/4.49  --inst_start_prop_sim_after_learn       3
% 31.75/4.49  --inst_sel_renew                        solver
% 31.75/4.49  --inst_lit_activity_flag                true
% 31.75/4.49  --inst_restr_to_given                   false
% 31.75/4.49  --inst_activity_threshold               500
% 31.75/4.49  --inst_out_proof                        true
% 31.75/4.49  
% 31.75/4.49  ------ Resolution Options
% 31.75/4.49  
% 31.75/4.49  --resolution_flag                       false
% 31.75/4.49  --res_lit_sel                           adaptive
% 31.75/4.49  --res_lit_sel_side                      none
% 31.75/4.49  --res_ordering                          kbo
% 31.75/4.49  --res_to_prop_solver                    active
% 31.75/4.49  --res_prop_simpl_new                    false
% 31.75/4.49  --res_prop_simpl_given                  true
% 31.75/4.49  --res_passive_queue_type                priority_queues
% 31.75/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.75/4.49  --res_passive_queues_freq               [15;5]
% 31.75/4.49  --res_forward_subs                      full
% 31.75/4.49  --res_backward_subs                     full
% 31.75/4.49  --res_forward_subs_resolution           true
% 31.75/4.49  --res_backward_subs_resolution          true
% 31.75/4.49  --res_orphan_elimination                true
% 31.75/4.49  --res_time_limit                        2.
% 31.75/4.49  --res_out_proof                         true
% 31.75/4.49  
% 31.75/4.49  ------ Superposition Options
% 31.75/4.49  
% 31.75/4.49  --superposition_flag                    true
% 31.75/4.49  --sup_passive_queue_type                priority_queues
% 31.75/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.75/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.75/4.49  --demod_completeness_check              fast
% 31.75/4.49  --demod_use_ground                      true
% 31.75/4.49  --sup_to_prop_solver                    passive
% 31.75/4.49  --sup_prop_simpl_new                    true
% 31.75/4.49  --sup_prop_simpl_given                  true
% 31.75/4.49  --sup_fun_splitting                     false
% 31.75/4.49  --sup_smt_interval                      50000
% 31.75/4.49  
% 31.75/4.49  ------ Superposition Simplification Setup
% 31.75/4.49  
% 31.75/4.49  --sup_indices_passive                   []
% 31.75/4.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.75/4.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.75/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.75/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.75/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.75/4.49  --sup_full_bw                           [BwDemod]
% 31.75/4.49  --sup_immed_triv                        [TrivRules]
% 31.75/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.75/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.75/4.49  --sup_immed_bw_main                     []
% 31.75/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.75/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.75/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.75/4.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.75/4.49  
% 31.75/4.49  ------ Combination Options
% 31.75/4.49  
% 31.75/4.49  --comb_res_mult                         3
% 31.75/4.49  --comb_sup_mult                         2
% 31.75/4.49  --comb_inst_mult                        10
% 31.75/4.49  
% 31.75/4.49  ------ Debug Options
% 31.75/4.49  
% 31.75/4.49  --dbg_backtrace                         false
% 31.75/4.49  --dbg_dump_prop_clauses                 false
% 31.75/4.49  --dbg_dump_prop_clauses_file            -
% 31.75/4.49  --dbg_out_stat                          false
% 31.75/4.49  
% 31.75/4.49  
% 31.75/4.49  
% 31.75/4.49  
% 31.75/4.49  ------ Proving...
% 31.75/4.49  
% 31.75/4.49  
% 31.75/4.49  % SZS status Theorem for theBenchmark.p
% 31.75/4.49  
% 31.75/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.75/4.49  
% 31.75/4.49  fof(f15,conjecture,(
% 31.75/4.49    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 31.75/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.75/4.49  
% 31.75/4.49  fof(f16,negated_conjecture,(
% 31.75/4.49    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 31.75/4.49    inference(negated_conjecture,[],[f15])).
% 31.75/4.49  
% 31.75/4.49  fof(f20,plain,(
% 31.75/4.49    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 31.75/4.49    inference(ennf_transformation,[],[f16])).
% 31.75/4.49  
% 31.75/4.49  fof(f21,plain,(
% 31.75/4.49    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0) => (k1_tarski(sK1) != sK0 & k1_xboole_0 != sK0 & k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0)),
% 31.75/4.49    introduced(choice_axiom,[])).
% 31.75/4.49  
% 31.75/4.49  fof(f22,plain,(
% 31.75/4.49    k1_tarski(sK1) != sK0 & k1_xboole_0 != sK0 & k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0),
% 31.75/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).
% 31.75/4.49  
% 31.75/4.49  fof(f37,plain,(
% 31.75/4.49    k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0),
% 31.75/4.49    inference(cnf_transformation,[],[f22])).
% 31.75/4.49  
% 31.75/4.49  fof(f2,axiom,(
% 31.75/4.49    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 31.75/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.75/4.49  
% 31.75/4.49  fof(f24,plain,(
% 31.75/4.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 31.75/4.49    inference(cnf_transformation,[],[f2])).
% 31.75/4.49  
% 31.75/4.49  fof(f6,axiom,(
% 31.75/4.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 31.75/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.75/4.49  
% 31.75/4.49  fof(f28,plain,(
% 31.75/4.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 31.75/4.49    inference(cnf_transformation,[],[f6])).
% 31.75/4.49  
% 31.75/4.49  fof(f7,axiom,(
% 31.75/4.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 31.75/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.75/4.49  
% 31.75/4.49  fof(f29,plain,(
% 31.75/4.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 31.75/4.49    inference(cnf_transformation,[],[f7])).
% 31.75/4.49  
% 31.75/4.49  fof(f8,axiom,(
% 31.75/4.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 31.75/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.75/4.49  
% 31.75/4.49  fof(f30,plain,(
% 31.75/4.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 31.75/4.49    inference(cnf_transformation,[],[f8])).
% 31.75/4.49  
% 31.75/4.49  fof(f9,axiom,(
% 31.75/4.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 31.75/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.75/4.49  
% 31.75/4.49  fof(f31,plain,(
% 31.75/4.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 31.75/4.49    inference(cnf_transformation,[],[f9])).
% 31.75/4.49  
% 31.75/4.49  fof(f10,axiom,(
% 31.75/4.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 31.75/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.75/4.49  
% 31.75/4.49  fof(f32,plain,(
% 31.75/4.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 31.75/4.49    inference(cnf_transformation,[],[f10])).
% 31.75/4.49  
% 31.75/4.49  fof(f11,axiom,(
% 31.75/4.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 31.75/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.75/4.49  
% 31.75/4.49  fof(f33,plain,(
% 31.75/4.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 31.75/4.49    inference(cnf_transformation,[],[f11])).
% 31.75/4.49  
% 31.75/4.49  fof(f12,axiom,(
% 31.75/4.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 31.75/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.75/4.49  
% 31.75/4.49  fof(f34,plain,(
% 31.75/4.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 31.75/4.49    inference(cnf_transformation,[],[f12])).
% 31.75/4.49  
% 31.75/4.49  fof(f40,plain,(
% 31.75/4.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 31.75/4.49    inference(definition_unfolding,[],[f33,f34])).
% 31.75/4.49  
% 31.75/4.49  fof(f41,plain,(
% 31.75/4.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 31.75/4.49    inference(definition_unfolding,[],[f32,f40])).
% 31.75/4.49  
% 31.75/4.49  fof(f42,plain,(
% 31.75/4.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 31.75/4.49    inference(definition_unfolding,[],[f31,f41])).
% 31.75/4.49  
% 31.75/4.49  fof(f43,plain,(
% 31.75/4.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 31.75/4.49    inference(definition_unfolding,[],[f30,f42])).
% 31.75/4.49  
% 31.75/4.49  fof(f44,plain,(
% 31.75/4.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 31.75/4.49    inference(definition_unfolding,[],[f29,f43])).
% 31.75/4.49  
% 31.75/4.49  fof(f45,plain,(
% 31.75/4.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 31.75/4.49    inference(definition_unfolding,[],[f28,f44])).
% 31.75/4.49  
% 31.75/4.49  fof(f49,plain,(
% 31.75/4.49    k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0),
% 31.75/4.49    inference(definition_unfolding,[],[f37,f24,f45])).
% 31.75/4.49  
% 31.75/4.49  fof(f5,axiom,(
% 31.75/4.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 31.75/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.75/4.49  
% 31.75/4.49  fof(f27,plain,(
% 31.75/4.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 31.75/4.49    inference(cnf_transformation,[],[f5])).
% 31.75/4.49  
% 31.75/4.49  fof(f4,axiom,(
% 31.75/4.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 31.75/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.75/4.49  
% 31.75/4.49  fof(f26,plain,(
% 31.75/4.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 31.75/4.49    inference(cnf_transformation,[],[f4])).
% 31.75/4.49  
% 31.75/4.49  fof(f1,axiom,(
% 31.75/4.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 31.75/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.75/4.49  
% 31.75/4.49  fof(f23,plain,(
% 31.75/4.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 31.75/4.49    inference(cnf_transformation,[],[f1])).
% 31.75/4.49  
% 31.75/4.49  fof(f3,axiom,(
% 31.75/4.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 31.75/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.75/4.49  
% 31.75/4.49  fof(f25,plain,(
% 31.75/4.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 31.75/4.49    inference(cnf_transformation,[],[f3])).
% 31.75/4.49  
% 31.75/4.49  fof(f13,axiom,(
% 31.75/4.49    ! [X0,X1] : (r2_hidden(X0,X1) => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0))),
% 31.75/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.75/4.49  
% 31.75/4.49  fof(f18,plain,(
% 31.75/4.49    ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1))),
% 31.75/4.49    inference(ennf_transformation,[],[f13])).
% 31.75/4.49  
% 31.75/4.49  fof(f35,plain,(
% 31.75/4.49    ( ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1)) )),
% 31.75/4.49    inference(cnf_transformation,[],[f18])).
% 31.75/4.49  
% 31.75/4.49  fof(f46,plain,(
% 31.75/4.49    ( ! [X0,X1] : (k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,X1)) )),
% 31.75/4.49    inference(definition_unfolding,[],[f35,f45,f45])).
% 31.75/4.49  
% 31.75/4.49  fof(f14,axiom,(
% 31.75/4.49    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 31.75/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.75/4.49  
% 31.75/4.49  fof(f17,plain,(
% 31.75/4.49    ! [X0,X1] : (~r2_hidden(X1,X0) => k4_xboole_0(X0,k1_tarski(X1)) = X0)),
% 31.75/4.49    inference(unused_predicate_definition_removal,[],[f14])).
% 31.75/4.49  
% 31.75/4.49  fof(f19,plain,(
% 31.75/4.49    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0))),
% 31.75/4.49    inference(ennf_transformation,[],[f17])).
% 31.75/4.49  
% 31.75/4.49  fof(f36,plain,(
% 31.75/4.49    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 31.75/4.49    inference(cnf_transformation,[],[f19])).
% 31.75/4.49  
% 31.75/4.49  fof(f47,plain,(
% 31.75/4.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X0 | r2_hidden(X1,X0)) )),
% 31.75/4.49    inference(definition_unfolding,[],[f36,f24,f45])).
% 31.75/4.49  
% 31.75/4.49  fof(f39,plain,(
% 31.75/4.49    k1_tarski(sK1) != sK0),
% 31.75/4.49    inference(cnf_transformation,[],[f22])).
% 31.75/4.49  
% 31.75/4.49  fof(f48,plain,(
% 31.75/4.49    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK0),
% 31.75/4.49    inference(definition_unfolding,[],[f39,f45])).
% 31.75/4.49  
% 31.75/4.49  fof(f38,plain,(
% 31.75/4.49    k1_xboole_0 != sK0),
% 31.75/4.49    inference(cnf_transformation,[],[f22])).
% 31.75/4.49  
% 31.75/4.49  cnf(c_53,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_125,plain,
% 31.75/4.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != X0
% 31.75/4.49      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
% 31.75/4.49      | sK0 != X0 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_53]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_167488,plain,
% 31.75/4.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 31.75/4.49      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
% 31.75/4.49      | sK0 != k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_125]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_132,plain,
% 31.75/4.49      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_53]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_135,plain,
% 31.75/4.49      ( X0 != sK0 | sK0 = X0 | sK0 != sK0 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_132]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_167359,plain,
% 31.75/4.49      ( k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != sK0
% 31.75/4.49      | sK0 = k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 31.75/4.49      | sK0 != sK0 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_135]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_167369,plain,
% 31.75/4.49      ( k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != sK0
% 31.75/4.49      | sK0 = k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 31.75/4.49      | sK0 != sK0 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_167359]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_302,plain,
% 31.75/4.49      ( X0 != X1
% 31.75/4.49      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != X1
% 31.75/4.49      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = X0 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_53]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_458,plain,
% 31.75/4.49      ( X0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 31.75/4.49      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = X0
% 31.75/4.49      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_302]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_2213,plain,
% 31.75/4.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 31.75/4.49      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 31.75/4.49      | k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_458]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_8,negated_conjecture,
% 31.75/4.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0 ),
% 31.75/4.49      inference(cnf_transformation,[],[f49]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_3,plain,
% 31.75/4.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 31.75/4.49      inference(cnf_transformation,[],[f27]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_2,plain,
% 31.75/4.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 31.75/4.49      inference(cnf_transformation,[],[f26]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_0,plain,
% 31.75/4.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 31.75/4.49      inference(cnf_transformation,[],[f23]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_119,plain,
% 31.75/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 31.75/4.49      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_354,plain,
% 31.75/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 31.75/4.49      inference(superposition,[status(thm)],[c_3,c_119]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_1,plain,
% 31.75/4.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 31.75/4.49      inference(cnf_transformation,[],[f25]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_367,plain,
% 31.75/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 31.75/4.49      inference(demodulation,[status(thm)],[c_354,c_1]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_384,plain,
% 31.75/4.49      ( k5_xboole_0(k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k1_xboole_0) = sK0 ),
% 31.75/4.49      inference(superposition,[status(thm)],[c_8,c_367]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_650,plain,
% 31.75/4.49      ( k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = sK0 ),
% 31.75/4.49      inference(superposition,[status(thm)],[c_384,c_1]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_221,plain,
% 31.75/4.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != X1
% 31.75/4.49      | k1_xboole_0 != X1
% 31.75/4.49      | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_53]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_414,plain,
% 31.75/4.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k1_xboole_0
% 31.75/4.49      | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
% 31.75/4.49      | k1_xboole_0 != k1_xboole_0 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_221]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_415,plain,
% 31.75/4.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != k1_xboole_0
% 31.75/4.49      | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
% 31.75/4.49      | k1_xboole_0 != k1_xboole_0 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_414]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_52,plain,( X0 = X0 ),theory(equality) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_264,plain,
% 31.75/4.49      ( k1_xboole_0 = k1_xboole_0 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_52]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_127,plain,
% 31.75/4.49      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_53]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_172,plain,
% 31.75/4.49      ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
% 31.75/4.49      | k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
% 31.75/4.49      | k1_xboole_0 = sK0 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_127]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_175,plain,
% 31.75/4.49      ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
% 31.75/4.49      | k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
% 31.75/4.49      | k1_xboole_0 = sK0 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_172]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_4,plain,
% 31.75/4.49      ( ~ r2_hidden(X0,X1)
% 31.75/4.49      | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 31.75/4.49      inference(cnf_transformation,[],[f46]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_167,plain,
% 31.75/4.49      ( ~ r2_hidden(X0,sK0)
% 31.75/4.49      | k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_4]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_169,plain,
% 31.75/4.49      ( ~ r2_hidden(sK1,sK0)
% 31.75/4.49      | k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_167]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_5,plain,
% 31.75/4.49      ( r2_hidden(X0,X1)
% 31.75/4.49      | k5_xboole_0(X1,k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X1 ),
% 31.75/4.49      inference(cnf_transformation,[],[f47]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_147,plain,
% 31.75/4.49      ( r2_hidden(X0,sK0)
% 31.75/4.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = sK0 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_5]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_150,plain,
% 31.75/4.49      ( r2_hidden(sK1,sK0)
% 31.75/4.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = sK0 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_147]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_146,plain,
% 31.75/4.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != sK0
% 31.75/4.49      | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
% 31.75/4.49      | sK0 != sK0 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_135]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_148,plain,
% 31.75/4.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != sK0
% 31.75/4.49      | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
% 31.75/4.49      | sK0 != sK0 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_146]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_136,plain,
% 31.75/4.49      ( sK0 = sK0 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_52]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_60,plain,
% 31.75/4.49      ( sK1 = sK1 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_52]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_55,plain,
% 31.75/4.49      ( X0 != X1
% 31.75/4.49      | X2 != X3
% 31.75/4.49      | X4 != X5
% 31.75/4.49      | X6 != X7
% 31.75/4.49      | X8 != X9
% 31.75/4.49      | X10 != X11
% 31.75/4.49      | X12 != X13
% 31.75/4.49      | X14 != X15
% 31.75/4.49      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 31.75/4.49      theory(equality) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_57,plain,
% 31.75/4.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 31.75/4.49      | sK1 != sK1 ),
% 31.75/4.49      inference(instantiation,[status(thm)],[c_55]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_6,negated_conjecture,
% 31.75/4.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK0 ),
% 31.75/4.49      inference(cnf_transformation,[],[f48]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(c_7,negated_conjecture,
% 31.75/4.49      ( k1_xboole_0 != sK0 ),
% 31.75/4.49      inference(cnf_transformation,[],[f38]) ).
% 31.75/4.49  
% 31.75/4.49  cnf(contradiction,plain,
% 31.75/4.49      ( $false ),
% 31.75/4.49      inference(minisat,
% 31.75/4.49                [status(thm)],
% 31.75/4.49                [c_167488,c_167369,c_2213,c_650,c_415,c_264,c_175,c_169,
% 31.75/4.49                 c_150,c_148,c_136,c_60,c_57,c_6,c_7,c_8]) ).
% 31.75/4.49  
% 31.75/4.49  
% 31.75/4.49  % SZS output end CNFRefutation for theBenchmark.p
% 31.75/4.49  
% 31.75/4.49  ------                               Statistics
% 31.75/4.49  
% 31.75/4.49  ------ General
% 31.75/4.49  
% 31.75/4.49  abstr_ref_over_cycles:                  0
% 31.75/4.49  abstr_ref_under_cycles:                 0
% 31.75/4.49  gc_basic_clause_elim:                   0
% 31.75/4.49  forced_gc_time:                         0
% 31.75/4.49  parsing_time:                           0.009
% 31.75/4.49  unif_index_cands_time:                  0.
% 31.75/4.49  unif_index_add_time:                    0.
% 31.75/4.49  orderings_time:                         0.
% 31.75/4.49  out_proof_time:                         0.01
% 31.75/4.49  total_time:                             3.717
% 31.75/4.49  num_of_symbols:                         38
% 31.75/4.49  num_of_terms:                           175071
% 31.75/4.49  
% 31.75/4.49  ------ Preprocessing
% 31.75/4.49  
% 31.75/4.49  num_of_splits:                          0
% 31.75/4.49  num_of_split_atoms:                     0
% 31.75/4.49  num_of_reused_defs:                     0
% 31.75/4.49  num_eq_ax_congr_red:                    4
% 31.75/4.49  num_of_sem_filtered_clauses:            1
% 31.75/4.49  num_of_subtypes:                        0
% 31.75/4.49  monotx_restored_types:                  0
% 31.75/4.49  sat_num_of_epr_types:                   0
% 31.75/4.49  sat_num_of_non_cyclic_types:            0
% 31.75/4.49  sat_guarded_non_collapsed_types:        0
% 31.75/4.49  num_pure_diseq_elim:                    0
% 31.75/4.49  simp_replaced_by:                       0
% 31.75/4.49  res_preprocessed:                       38
% 31.75/4.49  prep_upred:                             0
% 31.75/4.49  prep_unflattend:                        0
% 31.75/4.49  smt_new_axioms:                         0
% 31.75/4.49  pred_elim_cands:                        1
% 31.75/4.49  pred_elim:                              0
% 31.75/4.49  pred_elim_cl:                           0
% 31.75/4.49  pred_elim_cycles:                       1
% 31.75/4.49  merged_defs:                            0
% 31.75/4.49  merged_defs_ncl:                        0
% 31.75/4.49  bin_hyper_res:                          0
% 31.75/4.49  prep_cycles:                            3
% 31.75/4.49  pred_elim_time:                         0.
% 31.75/4.49  splitting_time:                         0.
% 31.75/4.49  sem_filter_time:                        0.
% 31.75/4.49  monotx_time:                            0.
% 31.75/4.49  subtype_inf_time:                       0.
% 31.75/4.49  
% 31.75/4.49  ------ Problem properties
% 31.75/4.49  
% 31.75/4.49  clauses:                                9
% 31.75/4.49  conjectures:                            3
% 31.75/4.49  epr:                                    1
% 31.75/4.49  horn:                                   8
% 31.75/4.49  ground:                                 3
% 31.75/4.49  unary:                                  7
% 31.75/4.49  binary:                                 2
% 31.75/4.49  lits:                                   11
% 31.75/4.49  lits_eq:                                9
% 31.75/4.49  fd_pure:                                0
% 31.75/4.49  fd_pseudo:                              0
% 31.75/4.49  fd_cond:                                0
% 31.75/4.49  fd_pseudo_cond:                         0
% 31.75/4.49  ac_symbols:                             1
% 31.75/4.49  
% 31.75/4.49  ------ Propositional Solver
% 31.75/4.49  
% 31.75/4.49  prop_solver_calls:                      29
% 31.75/4.49  prop_fast_solver_calls:                 452
% 31.75/4.49  smt_solver_calls:                       0
% 31.75/4.49  smt_fast_solver_calls:                  0
% 31.75/4.49  prop_num_of_clauses:                    20090
% 31.75/4.49  prop_preprocess_simplified:             15895
% 31.75/4.49  prop_fo_subsumed:                       0
% 31.75/4.49  prop_solver_time:                       0.
% 31.75/4.49  smt_solver_time:                        0.
% 31.75/4.49  smt_fast_solver_time:                   0.
% 31.75/4.49  prop_fast_solver_time:                  0.
% 31.75/4.49  prop_unsat_core_time:                   0.002
% 31.75/4.49  
% 31.75/4.49  ------ QBF
% 31.75/4.49  
% 31.75/4.49  qbf_q_res:                              0
% 31.75/4.49  qbf_num_tautologies:                    0
% 31.75/4.49  qbf_prep_cycles:                        0
% 31.75/4.49  
% 31.75/4.49  ------ BMC1
% 31.75/4.49  
% 31.75/4.49  bmc1_current_bound:                     -1
% 31.75/4.49  bmc1_last_solved_bound:                 -1
% 31.75/4.49  bmc1_unsat_core_size:                   -1
% 31.75/4.49  bmc1_unsat_core_parents_size:           -1
% 31.75/4.49  bmc1_merge_next_fun:                    0
% 31.75/4.49  bmc1_unsat_core_clauses_time:           0.
% 31.75/4.49  
% 31.75/4.49  ------ Instantiation
% 31.75/4.49  
% 31.75/4.49  inst_num_of_clauses:                    3800
% 31.75/4.49  inst_num_in_passive:                    1484
% 31.75/4.49  inst_num_in_active:                     917
% 31.75/4.49  inst_num_in_unprocessed:                1403
% 31.75/4.49  inst_num_of_loops:                      1088
% 31.75/4.49  inst_num_of_learning_restarts:          0
% 31.75/4.49  inst_num_moves_active_passive:          162
% 31.75/4.49  inst_lit_activity:                      0
% 31.75/4.49  inst_lit_activity_moves:                1
% 31.75/4.49  inst_num_tautologies:                   0
% 31.75/4.49  inst_num_prop_implied:                  0
% 31.75/4.49  inst_num_existing_simplified:           0
% 31.75/4.49  inst_num_eq_res_simplified:             0
% 31.75/4.49  inst_num_child_elim:                    0
% 31.75/4.49  inst_num_of_dismatching_blockings:      3163
% 31.75/4.49  inst_num_of_non_proper_insts:           4057
% 31.75/4.49  inst_num_of_duplicates:                 0
% 31.75/4.49  inst_inst_num_from_inst_to_res:         0
% 31.75/4.49  inst_dismatching_checking_time:         0.
% 31.75/4.49  
% 31.75/4.49  ------ Resolution
% 31.75/4.49  
% 31.75/4.49  res_num_of_clauses:                     0
% 31.75/4.49  res_num_in_passive:                     0
% 31.75/4.49  res_num_in_active:                      0
% 31.75/4.49  res_num_of_loops:                       41
% 31.75/4.49  res_forward_subset_subsumed:            411
% 31.75/4.49  res_backward_subset_subsumed:           14
% 31.75/4.49  res_forward_subsumed:                   0
% 31.75/4.49  res_backward_subsumed:                  0
% 31.75/4.49  res_forward_subsumption_resolution:     0
% 31.75/4.49  res_backward_subsumption_resolution:    0
% 31.75/4.49  res_clause_to_clause_subsumption:       360342
% 31.75/4.49  res_orphan_elimination:                 0
% 31.75/4.49  res_tautology_del:                      174
% 31.75/4.49  res_num_eq_res_simplified:              0
% 31.75/4.49  res_num_sel_changes:                    0
% 31.75/4.49  res_moves_from_active_to_pass:          0
% 31.75/4.49  
% 31.75/4.49  ------ Superposition
% 31.75/4.49  
% 31.75/4.49  sup_time_total:                         0.
% 31.75/4.49  sup_time_generating:                    0.
% 31.75/4.49  sup_time_sim_full:                      0.
% 31.75/4.49  sup_time_sim_immed:                     0.
% 31.75/4.49  
% 31.75/4.49  sup_num_of_clauses:                     9257
% 31.75/4.49  sup_num_in_active:                      178
% 31.75/4.49  sup_num_in_passive:                     9079
% 31.75/4.49  sup_num_of_loops:                       216
% 31.75/4.49  sup_fw_superposition:                   38144
% 31.75/4.49  sup_bw_superposition:                   29572
% 31.75/4.49  sup_immediate_simplified:               32175
% 31.75/4.49  sup_given_eliminated:                   19
% 31.75/4.49  comparisons_done:                       0
% 31.75/4.49  comparisons_avoided:                    0
% 31.75/4.49  
% 31.75/4.49  ------ Simplifications
% 31.75/4.49  
% 31.75/4.49  
% 31.75/4.49  sim_fw_subset_subsumed:                 0
% 31.75/4.49  sim_bw_subset_subsumed:                 0
% 31.75/4.49  sim_fw_subsumed:                        1905
% 31.75/4.49  sim_bw_subsumed:                        199
% 31.75/4.49  sim_fw_subsumption_res:                 0
% 31.75/4.49  sim_bw_subsumption_res:                 0
% 31.75/4.49  sim_tautology_del:                      0
% 31.75/4.49  sim_eq_tautology_del:                   6936
% 31.75/4.49  sim_eq_res_simp:                        0
% 31.75/4.49  sim_fw_demodulated:                     22905
% 31.75/4.49  sim_bw_demodulated:                     1203
% 31.75/4.49  sim_light_normalised:                   11164
% 31.75/4.49  sim_joinable_taut:                      1808
% 31.75/4.49  sim_joinable_simp:                      0
% 31.75/4.49  sim_ac_normalised:                      0
% 31.75/4.49  sim_smt_subsumption:                    0
% 31.75/4.49  
%------------------------------------------------------------------------------
