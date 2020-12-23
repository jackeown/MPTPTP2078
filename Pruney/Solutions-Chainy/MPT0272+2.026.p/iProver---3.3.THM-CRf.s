%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:15 EST 2020

% Result     : Theorem 12.08s
% Output     : CNFRefutation 12.08s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 231 expanded)
%              Number of clauses        :   48 (  64 expanded)
%              Number of leaves         :   17 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  180 ( 359 expanded)
%              Number of equality atoms :  171 ( 350 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f28,f33])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f14,axiom,(
    ! [X0,X1] : k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f43])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f39,f44,f43])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f37,f44,f44,f44])).

fof(f55,plain,(
    ! [X1] : k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k5_xboole_0(X1,k4_xboole_0(X2,X1)) != k2_enumset1(X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f40,f33,f44])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f38,f44,f44,f44])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
      & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
        & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
   => ( k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)
      & k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)
    & k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).

fof(f42,plain,(
    k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f42,f44,f44])).

fof(f41,plain,(
    k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f41,f44])).

cnf(c_63,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_160,plain,
    ( X0 != X1
    | k2_enumset1(X2,X2,X2,X2) != X1
    | k2_enumset1(X2,X2,X2,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_3986,plain,
    ( k2_enumset1(X0,X0,X0,X0) != X1
    | k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),X2))
    | k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),X2)) != X1 ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_15335,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X1)
    | k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)))
    | k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X1) ),
    inference(instantiation,[status(thm)],[c_3986])).

cnf(c_53379,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)))
    | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)
    | k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_15335])).

cnf(c_53380,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)))
    | k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)
    | k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_53379])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_50,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k4_xboole_0(X3,X1) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_51,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_50])).

cnf(c_4581,plain,
    ( k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_65,plain,
    ( X0 != X1
    | k5_xboole_0(X2,X0) = k5_xboole_0(X2,X1) ),
    theory(equality)).

cnf(c_1251,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)
    | k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_4580,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)
    | k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1251])).

cnf(c_62,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_289,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_63,c_62])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_301,plain,
    ( X0 = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[status(thm)],[c_289,c_3])).

cnf(c_510,plain,
    ( X0 = X1
    | X1 != k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[status(thm)],[c_301,c_63])).

cnf(c_1508,plain,
    ( X0 = k5_xboole_0(X0,X1)
    | X1 != k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_510,c_65])).

cnf(c_6,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_305,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_289,c_6])).

cnf(c_2517,plain,
    ( X0 = k5_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1508,c_305])).

cnf(c_2528,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_2517,c_289])).

cnf(c_66,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_453,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != k2_enumset1(X1,X3,X5,X7)
    | k2_enumset1(X0,X2,X4,X6) = X8 ),
    inference(resolution,[status(thm)],[c_66,c_63])).

cnf(c_2681,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k5_xboole_0(k2_enumset1(X1,X3,X5,X7),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2528,c_453])).

cnf(c_2682,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2681])).

cnf(c_701,plain,
    ( X0 != k2_enumset1(X1,X2,X3,X4)
    | k2_enumset1(X5,X5,X5,X5) = X0
    | k2_enumset1(X5,X5,X5,X5) != k2_enumset1(X1,X2,X3,X4) ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_1798,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k2_enumset1(X1,X1,X1,X1)
    | k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | k1_xboole_0 != k2_enumset1(X1,X1,X1,X1) ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_1799,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_xboole_0
    | k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_1798])).

cnf(c_9,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_432,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_8])).

cnf(c_433,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_79,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) != X0
    | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_218,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_10,plain,
    ( X0 = X1
    | k2_enumset1(X2,X2,X2,X2) != k5_xboole_0(X1,k4_xboole_0(X0,X1))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_135,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)))
    | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_136,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)))
    | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_135])).

cnf(c_123,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_69,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_7,plain,
    ( X0 = X1
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_15,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_11,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_12,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_53380,c_4581,c_4580,c_2682,c_1799,c_433,c_218,c_136,c_123,c_69,c_16,c_15,c_11,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:58:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 12.08/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.08/1.98  
% 12.08/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.08/1.98  
% 12.08/1.98  ------  iProver source info
% 12.08/1.98  
% 12.08/1.98  git: date: 2020-06-30 10:37:57 +0100
% 12.08/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.08/1.98  git: non_committed_changes: false
% 12.08/1.98  git: last_make_outside_of_git: false
% 12.08/1.98  
% 12.08/1.98  ------ 
% 12.08/1.98  ------ Parsing...
% 12.08/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.08/1.98  
% 12.08/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 12.08/1.98  
% 12.08/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.08/1.98  
% 12.08/1.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.08/1.98  ------ Proving...
% 12.08/1.98  ------ Problem Properties 
% 12.08/1.98  
% 12.08/1.98  
% 12.08/1.98  clauses                                 12
% 12.08/1.98  conjectures                             2
% 12.08/1.98  EPR                                     0
% 12.08/1.98  Horn                                    10
% 12.08/1.98  unary                                   10
% 12.08/1.98  binary                                  1
% 12.08/1.98  lits                                    16
% 12.08/1.98  lits eq                                 16
% 12.08/1.98  fd_pure                                 0
% 12.08/1.98  fd_pseudo                               0
% 12.08/1.98  fd_cond                                 0
% 12.08/1.98  fd_pseudo_cond                          2
% 12.08/1.98  AC symbols                              0
% 12.08/1.98  
% 12.08/1.98  ------ Input Options Time Limit: Unbounded
% 12.08/1.98  
% 12.08/1.98  
% 12.08/1.98  ------ 
% 12.08/1.98  Current options:
% 12.08/1.98  ------ 
% 12.08/1.98  
% 12.08/1.98  
% 12.08/1.98  
% 12.08/1.98  
% 12.08/1.98  ------ Proving...
% 12.08/1.98  
% 12.08/1.98  
% 12.08/1.98  % SZS status Theorem for theBenchmark.p
% 12.08/1.98  
% 12.08/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 12.08/1.98  
% 12.08/1.98  fof(f2,axiom,(
% 12.08/1.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 12.08/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/1.98  
% 12.08/1.98  fof(f18,plain,(
% 12.08/1.98    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 12.08/1.98    inference(unused_predicate_definition_removal,[],[f2])).
% 12.08/1.98  
% 12.08/1.98  fof(f19,plain,(
% 12.08/1.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 12.08/1.98    inference(ennf_transformation,[],[f18])).
% 12.08/1.98  
% 12.08/1.98  fof(f26,plain,(
% 12.08/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 12.08/1.98    inference(cnf_transformation,[],[f19])).
% 12.08/1.98  
% 12.08/1.98  fof(f5,axiom,(
% 12.08/1.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 12.08/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/1.98  
% 12.08/1.98  fof(f29,plain,(
% 12.08/1.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 12.08/1.98    inference(cnf_transformation,[],[f5])).
% 12.08/1.98  
% 12.08/1.98  fof(f4,axiom,(
% 12.08/1.98    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 12.08/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/1.98  
% 12.08/1.98  fof(f28,plain,(
% 12.08/1.98    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.08/1.98    inference(cnf_transformation,[],[f4])).
% 12.08/1.98  
% 12.08/1.98  fof(f9,axiom,(
% 12.08/1.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 12.08/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/1.98  
% 12.08/1.98  fof(f33,plain,(
% 12.08/1.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 12.08/1.98    inference(cnf_transformation,[],[f9])).
% 12.08/1.98  
% 12.08/1.98  fof(f47,plain,(
% 12.08/1.98    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 12.08/1.98    inference(definition_unfolding,[],[f28,f33])).
% 12.08/1.98  
% 12.08/1.98  fof(f8,axiom,(
% 12.08/1.98    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 12.08/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/1.98  
% 12.08/1.98  fof(f32,plain,(
% 12.08/1.98    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 12.08/1.98    inference(cnf_transformation,[],[f8])).
% 12.08/1.98  
% 12.08/1.98  fof(f14,axiom,(
% 12.08/1.98    ! [X0,X1] : k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_xboole_0),
% 12.08/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/1.98  
% 12.08/1.98  fof(f39,plain,(
% 12.08/1.98    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_xboole_0) )),
% 12.08/1.98    inference(cnf_transformation,[],[f14])).
% 12.08/1.98  
% 12.08/1.98  fof(f10,axiom,(
% 12.08/1.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 12.08/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/1.98  
% 12.08/1.98  fof(f34,plain,(
% 12.08/1.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 12.08/1.98    inference(cnf_transformation,[],[f10])).
% 12.08/1.98  
% 12.08/1.98  fof(f44,plain,(
% 12.08/1.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 12.08/1.98    inference(definition_unfolding,[],[f34,f43])).
% 12.08/1.98  
% 12.08/1.98  fof(f11,axiom,(
% 12.08/1.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 12.08/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/1.98  
% 12.08/1.98  fof(f35,plain,(
% 12.08/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 12.08/1.98    inference(cnf_transformation,[],[f11])).
% 12.08/1.98  
% 12.08/1.98  fof(f12,axiom,(
% 12.08/1.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 12.08/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/1.98  
% 12.08/1.98  fof(f36,plain,(
% 12.08/1.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 12.08/1.98    inference(cnf_transformation,[],[f12])).
% 12.08/1.98  
% 12.08/1.98  fof(f43,plain,(
% 12.08/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 12.08/1.98    inference(definition_unfolding,[],[f35,f36])).
% 12.08/1.98  
% 12.08/1.98  fof(f51,plain,(
% 12.08/1.98    ( ! [X0,X1] : (k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0) )),
% 12.08/1.98    inference(definition_unfolding,[],[f39,f44,f43])).
% 12.08/1.98  
% 12.08/1.98  fof(f13,axiom,(
% 12.08/1.98    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 12.08/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/1.98  
% 12.08/1.98  fof(f22,plain,(
% 12.08/1.98    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 12.08/1.98    inference(nnf_transformation,[],[f13])).
% 12.08/1.98  
% 12.08/1.98  fof(f37,plain,(
% 12.08/1.98    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 12.08/1.98    inference(cnf_transformation,[],[f22])).
% 12.08/1.98  
% 12.08/1.98  fof(f50,plain,(
% 12.08/1.98    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X0,X0,X0,X0)) )),
% 12.08/1.98    inference(definition_unfolding,[],[f37,f44,f44,f44])).
% 12.08/1.98  
% 12.08/1.98  fof(f55,plain,(
% 12.08/1.98    ( ! [X1] : (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1)) )),
% 12.08/1.98    inference(equality_resolution,[],[f50])).
% 12.08/1.98  
% 12.08/1.98  fof(f15,axiom,(
% 12.08/1.98    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 12.08/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/1.98  
% 12.08/1.98  fof(f20,plain,(
% 12.08/1.98    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0))),
% 12.08/1.98    inference(ennf_transformation,[],[f15])).
% 12.08/1.98  
% 12.08/1.98  fof(f40,plain,(
% 12.08/1.98    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0)) )),
% 12.08/1.98    inference(cnf_transformation,[],[f20])).
% 12.08/1.98  
% 12.08/1.98  fof(f52,plain,(
% 12.08/1.98    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k5_xboole_0(X1,k4_xboole_0(X2,X1)) != k2_enumset1(X0,X0,X0,X0)) )),
% 12.08/1.98    inference(definition_unfolding,[],[f40,f33,f44])).
% 12.08/1.98  
% 12.08/1.98  fof(f38,plain,(
% 12.08/1.98    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 12.08/1.98    inference(cnf_transformation,[],[f22])).
% 12.08/1.98  
% 12.08/1.98  fof(f49,plain,(
% 12.08/1.98    ( ! [X0,X1] : (k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(X0,X0,X0,X0) | X0 = X1) )),
% 12.08/1.98    inference(definition_unfolding,[],[f38,f44,f44,f44])).
% 12.08/1.98  
% 12.08/1.98  fof(f16,conjecture,(
% 12.08/1.98    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)),
% 12.08/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.08/1.98  
% 12.08/1.98  fof(f17,negated_conjecture,(
% 12.08/1.98    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)),
% 12.08/1.98    inference(negated_conjecture,[],[f16])).
% 12.08/1.98  
% 12.08/1.98  fof(f21,plain,(
% 12.08/1.98    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0)),
% 12.08/1.98    inference(ennf_transformation,[],[f17])).
% 12.08/1.98  
% 12.08/1.98  fof(f23,plain,(
% 12.08/1.98    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) => (k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) & k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0)),
% 12.08/1.98    introduced(choice_axiom,[])).
% 12.08/1.98  
% 12.08/1.98  fof(f24,plain,(
% 12.08/1.98    k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) & k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0),
% 12.08/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).
% 12.08/1.98  
% 12.08/1.98  fof(f42,plain,(
% 12.08/1.98    k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)),
% 12.08/1.98    inference(cnf_transformation,[],[f24])).
% 12.08/1.98  
% 12.08/1.98  fof(f53,plain,(
% 12.08/1.98    k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 12.08/1.98    inference(definition_unfolding,[],[f42,f44,f44])).
% 12.08/1.98  
% 12.08/1.98  fof(f41,plain,(
% 12.08/1.98    k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0),
% 12.08/1.98    inference(cnf_transformation,[],[f24])).
% 12.08/1.98  
% 12.08/1.98  fof(f54,plain,(
% 12.08/1.98    k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) != k1_xboole_0),
% 12.08/1.98    inference(definition_unfolding,[],[f41,f44])).
% 12.08/1.98  
% 12.08/1.98  cnf(c_63,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_160,plain,
% 12.08/1.98      ( X0 != X1
% 12.08/1.98      | k2_enumset1(X2,X2,X2,X2) != X1
% 12.08/1.98      | k2_enumset1(X2,X2,X2,X2) = X0 ),
% 12.08/1.98      inference(instantiation,[status(thm)],[c_63]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_3986,plain,
% 12.08/1.98      ( k2_enumset1(X0,X0,X0,X0) != X1
% 12.08/1.98      | k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),X2))
% 12.08/1.98      | k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),X2)) != X1 ),
% 12.08/1.98      inference(instantiation,[status(thm)],[c_160]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_15335,plain,
% 12.08/1.98      ( k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X1)
% 12.08/1.98      | k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)))
% 12.08/1.98      | k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X1) ),
% 12.08/1.98      inference(instantiation,[status(thm)],[c_3986]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_53379,plain,
% 12.08/1.98      ( k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)))
% 12.08/1.98      | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)
% 12.08/1.98      | k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) ),
% 12.08/1.98      inference(instantiation,[status(thm)],[c_15335]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_53380,plain,
% 12.08/1.98      ( k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)))
% 12.08/1.98      | k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)
% 12.08/1.98      | k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) ),
% 12.08/1.98      inference(instantiation,[status(thm)],[c_53379]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_2,plain,
% 12.08/1.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 12.08/1.98      inference(cnf_transformation,[],[f26]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_4,plain,
% 12.08/1.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 12.08/1.98      inference(cnf_transformation,[],[f29]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_50,plain,
% 12.08/1.98      ( X0 != X1
% 12.08/1.98      | k4_xboole_0(X0,X2) != X3
% 12.08/1.98      | k4_xboole_0(X3,X1) = k1_xboole_0 ),
% 12.08/1.98      inference(resolution_lifted,[status(thm)],[c_2,c_4]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_51,plain,
% 12.08/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 12.08/1.98      inference(unflattening,[status(thm)],[c_50]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_4581,plain,
% 12.08/1.98      ( k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 12.08/1.98      inference(instantiation,[status(thm)],[c_51]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_65,plain,
% 12.08/1.98      ( X0 != X1 | k5_xboole_0(X2,X0) = k5_xboole_0(X2,X1) ),
% 12.08/1.98      theory(equality) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_1251,plain,
% 12.08/1.98      ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)
% 12.08/1.98      | k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)) != X0 ),
% 12.08/1.98      inference(instantiation,[status(thm)],[c_65]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_4580,plain,
% 12.08/1.98      ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)
% 12.08/1.98      | k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)) != k1_xboole_0 ),
% 12.08/1.98      inference(instantiation,[status(thm)],[c_1251]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_62,plain,( X0 = X0 ),theory(equality) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_289,plain,
% 12.08/1.98      ( X0 != X1 | X1 = X0 ),
% 12.08/1.98      inference(resolution,[status(thm)],[c_63,c_62]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_3,plain,
% 12.08/1.98      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 12.08/1.98      inference(cnf_transformation,[],[f47]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_301,plain,
% 12.08/1.98      ( X0 = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
% 12.08/1.98      inference(resolution,[status(thm)],[c_289,c_3]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_510,plain,
% 12.08/1.98      ( X0 = X1 | X1 != k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
% 12.08/1.98      inference(resolution,[status(thm)],[c_301,c_63]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_1508,plain,
% 12.08/1.98      ( X0 = k5_xboole_0(X0,X1) | X1 != k4_xboole_0(k1_xboole_0,X0) ),
% 12.08/1.98      inference(resolution,[status(thm)],[c_510,c_65]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_6,plain,
% 12.08/1.98      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 12.08/1.98      inference(cnf_transformation,[],[f32]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_305,plain,
% 12.08/1.98      ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
% 12.08/1.98      inference(resolution,[status(thm)],[c_289,c_6]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_2517,plain,
% 12.08/1.98      ( X0 = k5_xboole_0(X0,k1_xboole_0) ),
% 12.08/1.98      inference(resolution,[status(thm)],[c_1508,c_305]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_2528,plain,
% 12.08/1.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 12.08/1.98      inference(resolution,[status(thm)],[c_2517,c_289]) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_66,plain,
% 12.08/1.98      ( X0 != X1
% 12.08/1.98      | X2 != X3
% 12.08/1.98      | X4 != X5
% 12.08/1.98      | X6 != X7
% 12.08/1.98      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 12.08/1.98      theory(equality) ).
% 12.08/1.98  
% 12.08/1.98  cnf(c_453,plain,
% 12.08/1.98      ( X0 != X1
% 12.08/1.98      | X2 != X3
% 12.08/1.98      | X4 != X5
% 12.08/1.98      | X6 != X7
% 12.08/1.98      | X8 != k2_enumset1(X1,X3,X5,X7)
% 12.08/1.99      | k2_enumset1(X0,X2,X4,X6) = X8 ),
% 12.08/1.99      inference(resolution,[status(thm)],[c_66,c_63]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_2681,plain,
% 12.08/1.99      ( X0 != X1
% 12.08/1.99      | X2 != X3
% 12.08/1.99      | X4 != X5
% 12.08/1.99      | X6 != X7
% 12.08/1.99      | k2_enumset1(X0,X2,X4,X6) = k5_xboole_0(k2_enumset1(X1,X3,X5,X7),k1_xboole_0) ),
% 12.08/1.99      inference(resolution,[status(thm)],[c_2528,c_453]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_2682,plain,
% 12.08/1.99      ( k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)
% 12.08/1.99      | sK0 != sK0 ),
% 12.08/1.99      inference(instantiation,[status(thm)],[c_2681]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_701,plain,
% 12.08/1.99      ( X0 != k2_enumset1(X1,X2,X3,X4)
% 12.08/1.99      | k2_enumset1(X5,X5,X5,X5) = X0
% 12.08/1.99      | k2_enumset1(X5,X5,X5,X5) != k2_enumset1(X1,X2,X3,X4) ),
% 12.08/1.99      inference(instantiation,[status(thm)],[c_160]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_1798,plain,
% 12.08/1.99      ( k2_enumset1(X0,X0,X0,X0) != k2_enumset1(X1,X1,X1,X1)
% 12.08/1.99      | k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 12.08/1.99      | k1_xboole_0 != k2_enumset1(X1,X1,X1,X1) ),
% 12.08/1.99      inference(instantiation,[status(thm)],[c_701]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_1799,plain,
% 12.08/1.99      ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
% 12.08/1.99      | k2_enumset1(sK0,sK0,sK0,sK0) = k1_xboole_0
% 12.08/1.99      | k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0) ),
% 12.08/1.99      inference(instantiation,[status(thm)],[c_1798]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_9,plain,
% 12.08/1.99      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
% 12.08/1.99      inference(cnf_transformation,[],[f51]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_8,plain,
% 12.08/1.99      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
% 12.08/1.99      inference(cnf_transformation,[],[f55]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_432,plain,
% 12.08/1.99      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
% 12.08/1.99      inference(superposition,[status(thm)],[c_9,c_8]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_433,plain,
% 12.08/1.99      ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0 ),
% 12.08/1.99      inference(instantiation,[status(thm)],[c_432]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_79,plain,
% 12.08/1.99      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) != X0
% 12.08/1.99      | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k1_xboole_0
% 12.08/1.99      | k1_xboole_0 != X0 ),
% 12.08/1.99      inference(instantiation,[status(thm)],[c_63]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_218,plain,
% 12.08/1.99      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
% 12.08/1.99      | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k1_xboole_0
% 12.08/1.99      | k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
% 12.08/1.99      inference(instantiation,[status(thm)],[c_79]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_10,plain,
% 12.08/1.99      ( X0 = X1
% 12.08/1.99      | k2_enumset1(X2,X2,X2,X2) != k5_xboole_0(X1,k4_xboole_0(X0,X1))
% 12.08/1.99      | k1_xboole_0 = X0
% 12.08/1.99      | k1_xboole_0 = X1 ),
% 12.08/1.99      inference(cnf_transformation,[],[f52]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_135,plain,
% 12.08/1.99      ( k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)))
% 12.08/1.99      | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k2_enumset1(sK0,sK0,sK0,sK0)
% 12.08/1.99      | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
% 12.08/1.99      | k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
% 12.08/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_136,plain,
% 12.08/1.99      ( k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)))
% 12.08/1.99      | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k2_enumset1(sK0,sK0,sK0,sK0)
% 12.08/1.99      | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
% 12.08/1.99      | k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
% 12.08/1.99      inference(instantiation,[status(thm)],[c_135]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_123,plain,
% 12.08/1.99      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
% 12.08/1.99      inference(instantiation,[status(thm)],[c_62]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_69,plain,
% 12.08/1.99      ( k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK0,sK0,sK0,sK0)
% 12.08/1.99      | sK0 != sK0 ),
% 12.08/1.99      inference(instantiation,[status(thm)],[c_66]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_7,plain,
% 12.08/1.99      ( X0 = X1
% 12.08/1.99      | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X1) ),
% 12.08/1.99      inference(cnf_transformation,[],[f49]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_16,plain,
% 12.08/1.99      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) = k2_enumset1(sK0,sK0,sK0,sK0)
% 12.08/1.99      | sK0 = sK0 ),
% 12.08/1.99      inference(instantiation,[status(thm)],[c_7]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_15,plain,
% 12.08/1.99      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) != k2_enumset1(sK0,sK0,sK0,sK0) ),
% 12.08/1.99      inference(instantiation,[status(thm)],[c_8]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_11,negated_conjecture,
% 12.08/1.99      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) != k2_enumset1(sK0,sK0,sK0,sK0) ),
% 12.08/1.99      inference(cnf_transformation,[],[f53]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(c_12,negated_conjecture,
% 12.08/1.99      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) != k1_xboole_0 ),
% 12.08/1.99      inference(cnf_transformation,[],[f54]) ).
% 12.08/1.99  
% 12.08/1.99  cnf(contradiction,plain,
% 12.08/1.99      ( $false ),
% 12.08/1.99      inference(minisat,
% 12.08/1.99                [status(thm)],
% 12.08/1.99                [c_53380,c_4581,c_4580,c_2682,c_1799,c_433,c_218,c_136,
% 12.08/1.99                 c_123,c_69,c_16,c_15,c_11,c_12]) ).
% 12.08/1.99  
% 12.08/1.99  
% 12.08/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 12.08/1.99  
% 12.08/1.99  ------                               Statistics
% 12.08/1.99  
% 12.08/1.99  ------ Selected
% 12.08/1.99  
% 12.08/1.99  total_time:                             1.355
% 12.08/1.99  
%------------------------------------------------------------------------------
