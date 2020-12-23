%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:08 EST 2020

% Result     : Theorem 27.69s
% Output     : CNFRefutation 27.69s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 305 expanded)
%              Number of clauses        :   72 ( 125 expanded)
%              Number of leaves         :   21 ( 100 expanded)
%              Depth                    :   17
%              Number of atoms          :  238 ( 498 expanded)
%              Number of equality atoms :  206 ( 455 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f34,f41])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f32,f43])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f44])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f45])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ) ),
    inference(definition_unfolding,[],[f37,f46,f46])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
        & ( r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 )
      & ( r2_hidden(sK0,sK1)
        | k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 )
    & ( r2_hidden(sK0,sK1)
      | k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f40,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f40,f26,f46])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f46,f46])).

fof(f39,plain,
    ( r2_hidden(sK0,sK1)
    | k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,
    ( r2_hidden(sK0,sK1)
    | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f39,f26,f46])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_129,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_191,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_153158,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_191])).

cnf(c_131,plain,
    ( X0 != X1
    | X2 != X3
    | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_501,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != k5_xboole_0(X1,X3)
    | k5_xboole_0(X0,X2) = X4 ),
    inference(resolution,[status(thm)],[c_131,c_129])).

cnf(c_128,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_225,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_129,c_128])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_236,plain,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(resolution,[status(thm)],[c_225,c_4])).

cnf(c_1910,plain,
    ( X0 != X1
    | X2 != X1
    | k5_xboole_0(X0,X2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_501,c_236])).

cnf(c_91526,plain,
    ( X0 != X1
    | k5_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1910,c_128])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_42,plain,
    ( r2_hidden(X0,X1)
    | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_7,negated_conjecture,
    ( ~ r2_hidden(sK0,sK1)
    | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_46,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_88,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0
    | k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_46])).

cnf(c_89,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0
    | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(unflattening,[status(thm)],[c_88])).

cnf(c_108,plain,
    ( k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_89])).

cnf(c_109,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0
    | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(renaming,[status(thm)],[c_108])).

cnf(c_111536,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[status(thm)],[c_91526,c_109])).

cnf(c_253,plain,
    ( X0 != X1
    | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != X1
    | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_829,plain,
    ( X0 != k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0)
    | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = X0
    | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_24017,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k1_xboole_0)) != k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0)
    | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_829])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_350,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_1035,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2,c_350])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_44,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_8,negated_conjecture,
    ( r2_hidden(sK0,sK1)
    | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_48,plain,
    ( r2_hidden(sK0,sK1)
    | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_96,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0
    | k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_44,c_48])).

cnf(c_97,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0
    | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(unflattening,[status(thm)],[c_96])).

cnf(c_110,plain,
    ( k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_97])).

cnf(c_111,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0
    | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(renaming,[status(thm)],[c_110])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_164,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_3,c_1])).

cnf(c_609,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k5_xboole_0(X0,k1_xboole_0)
    | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_111,c_164])).

cnf(c_9734,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0)
    | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_1035,c_609])).

cnf(c_132,plain,
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

cnf(c_522,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | X16 != k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15)
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = X16 ),
    inference(resolution,[status(thm)],[c_132,c_129])).

cnf(c_221,plain,
    ( X0 != k5_xboole_0(X1,k5_xboole_0(X2,X3))
    | k5_xboole_0(k5_xboole_0(X1,X2),X3) = X0 ),
    inference(resolution,[status(thm)],[c_129,c_3])).

cnf(c_232,plain,
    ( X0 = k5_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_225,c_2])).

cnf(c_242,plain,
    ( X0 = X1
    | X1 != k5_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_232,c_129])).

cnf(c_369,plain,
    ( X0 = k5_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_242,c_1])).

cnf(c_381,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[status(thm)],[c_369,c_225])).

cnf(c_676,plain,
    ( X0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_381,c_242])).

cnf(c_1612,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_221,c_676])).

cnf(c_2120,plain,
    ( X0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1612,c_225])).

cnf(c_218,plain,
    ( X0 != k5_xboole_0(X1,X2)
    | k5_xboole_0(X2,X1) = X0 ),
    inference(resolution,[status(thm)],[c_129,c_1])).

cnf(c_2137,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(resolution,[status(thm)],[c_2120,c_218])).

cnf(c_2387,plain,
    ( X0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[status(thm)],[c_2137,c_225])).

cnf(c_2405,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0) = X0 ),
    inference(resolution,[status(thm)],[c_2387,c_221])).

cnf(c_2410,plain,
    ( X0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0) ),
    inference(resolution,[status(thm)],[c_2405,c_225])).

cnf(c_2597,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(resolution,[status(thm)],[c_2410,c_218])).

cnf(c_3320,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k5_xboole_0(k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15),k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_522,c_2597])).

cnf(c_3321,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_3320])).

cnf(c_386,plain,
    ( X0 != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = X0
    | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_437,plain,
    ( k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0)
    | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_386])).

cnf(c_387,plain,
    ( k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(c_265,plain,
    ( k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_194,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_258,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_251,plain,
    ( k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_250,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_191])).

cnf(c_183,plain,
    ( k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_174,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0
    | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != X0
    | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_182,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_134,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(c_133,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_153158,c_111536,c_24017,c_9734,c_3321,c_437,c_387,c_265,c_258,c_251,c_250,c_183,c_182,c_134,c_133])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 13:07:04 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 27.69/4.07  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.69/4.07  
% 27.69/4.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.69/4.07  
% 27.69/4.07  ------  iProver source info
% 27.69/4.07  
% 27.69/4.07  git: date: 2020-06-30 10:37:57 +0100
% 27.69/4.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.69/4.07  git: non_committed_changes: false
% 27.69/4.07  git: last_make_outside_of_git: false
% 27.69/4.07  
% 27.69/4.07  ------ 
% 27.69/4.07  ------ Parsing...
% 27.69/4.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.69/4.07  
% 27.69/4.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.69/4.07  
% 27.69/4.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.69/4.07  
% 27.69/4.07  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.69/4.07  ------ Proving...
% 27.69/4.07  ------ Problem Properties 
% 27.69/4.07  
% 27.69/4.07  
% 27.69/4.07  clauses                                 7
% 27.69/4.07  conjectures                             0
% 27.69/4.07  EPR                                     0
% 27.69/4.07  Horn                                    6
% 27.69/4.07  unary                                   5
% 27.69/4.07  binary                                  2
% 27.69/4.07  lits                                    9
% 27.69/4.07  lits eq                                 9
% 27.69/4.07  fd_pure                                 0
% 27.69/4.07  fd_pseudo                               0
% 27.69/4.07  fd_cond                                 0
% 27.69/4.07  fd_pseudo_cond                          0
% 27.69/4.07  AC symbols                              1
% 27.69/4.07  
% 27.69/4.07  ------ Input Options Time Limit: Unbounded
% 27.69/4.07  
% 27.69/4.07  
% 27.69/4.07  ------ 
% 27.69/4.07  Current options:
% 27.69/4.07  ------ 
% 27.69/4.07  
% 27.69/4.07  
% 27.69/4.07  
% 27.69/4.07  
% 27.69/4.07  ------ Proving...
% 27.69/4.07  
% 27.69/4.07  
% 27.69/4.07  % SZS status Theorem for theBenchmark.p
% 27.69/4.07  
% 27.69/4.07  % SZS output start CNFRefutation for theBenchmark.p
% 27.69/4.07  
% 27.69/4.07  fof(f6,axiom,(
% 27.69/4.07    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 27.69/4.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/4.07  
% 27.69/4.07  fof(f29,plain,(
% 27.69/4.07    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 27.69/4.07    inference(cnf_transformation,[],[f6])).
% 27.69/4.07  
% 27.69/4.07  fof(f14,axiom,(
% 27.69/4.07    ! [X0,X1] : (k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1) => r2_hidden(X1,X0))),
% 27.69/4.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/4.07  
% 27.69/4.07  fof(f18,plain,(
% 27.69/4.07    ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1))),
% 27.69/4.07    inference(ennf_transformation,[],[f14])).
% 27.69/4.07  
% 27.69/4.07  fof(f37,plain,(
% 27.69/4.07    ( ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1)) )),
% 27.69/4.07    inference(cnf_transformation,[],[f18])).
% 27.69/4.07  
% 27.69/4.07  fof(f7,axiom,(
% 27.69/4.07    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 27.69/4.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/4.07  
% 27.69/4.07  fof(f30,plain,(
% 27.69/4.07    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 27.69/4.07    inference(cnf_transformation,[],[f7])).
% 27.69/4.07  
% 27.69/4.07  fof(f8,axiom,(
% 27.69/4.07    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.69/4.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/4.07  
% 27.69/4.07  fof(f31,plain,(
% 27.69/4.07    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.69/4.07    inference(cnf_transformation,[],[f8])).
% 27.69/4.07  
% 27.69/4.07  fof(f9,axiom,(
% 27.69/4.07    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.69/4.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/4.07  
% 27.69/4.07  fof(f32,plain,(
% 27.69/4.07    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.69/4.07    inference(cnf_transformation,[],[f9])).
% 27.69/4.07  
% 27.69/4.07  fof(f10,axiom,(
% 27.69/4.07    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 27.69/4.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/4.07  
% 27.69/4.07  fof(f33,plain,(
% 27.69/4.07    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.69/4.07    inference(cnf_transformation,[],[f10])).
% 27.69/4.07  
% 27.69/4.07  fof(f11,axiom,(
% 27.69/4.07    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 27.69/4.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/4.07  
% 27.69/4.07  fof(f34,plain,(
% 27.69/4.07    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 27.69/4.07    inference(cnf_transformation,[],[f11])).
% 27.69/4.07  
% 27.69/4.07  fof(f12,axiom,(
% 27.69/4.07    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 27.69/4.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/4.07  
% 27.69/4.07  fof(f35,plain,(
% 27.69/4.07    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 27.69/4.07    inference(cnf_transformation,[],[f12])).
% 27.69/4.07  
% 27.69/4.07  fof(f13,axiom,(
% 27.69/4.07    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 27.69/4.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/4.07  
% 27.69/4.07  fof(f36,plain,(
% 27.69/4.07    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 27.69/4.07    inference(cnf_transformation,[],[f13])).
% 27.69/4.07  
% 27.69/4.07  fof(f41,plain,(
% 27.69/4.07    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 27.69/4.07    inference(definition_unfolding,[],[f35,f36])).
% 27.69/4.07  
% 27.69/4.07  fof(f42,plain,(
% 27.69/4.07    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 27.69/4.07    inference(definition_unfolding,[],[f34,f41])).
% 27.69/4.07  
% 27.69/4.07  fof(f43,plain,(
% 27.69/4.07    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 27.69/4.07    inference(definition_unfolding,[],[f33,f42])).
% 27.69/4.07  
% 27.69/4.07  fof(f44,plain,(
% 27.69/4.07    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 27.69/4.07    inference(definition_unfolding,[],[f32,f43])).
% 27.69/4.07  
% 27.69/4.07  fof(f45,plain,(
% 27.69/4.07    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 27.69/4.07    inference(definition_unfolding,[],[f31,f44])).
% 27.69/4.07  
% 27.69/4.07  fof(f46,plain,(
% 27.69/4.07    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 27.69/4.07    inference(definition_unfolding,[],[f30,f45])).
% 27.69/4.07  
% 27.69/4.07  fof(f47,plain,(
% 27.69/4.07    ( ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 27.69/4.07    inference(definition_unfolding,[],[f37,f46,f46])).
% 27.69/4.07  
% 27.69/4.07  fof(f16,conjecture,(
% 27.69/4.07    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 27.69/4.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/4.07  
% 27.69/4.07  fof(f17,negated_conjecture,(
% 27.69/4.07    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 27.69/4.07    inference(negated_conjecture,[],[f16])).
% 27.69/4.07  
% 27.69/4.07  fof(f20,plain,(
% 27.69/4.07    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <~> r2_hidden(X0,X1))),
% 27.69/4.07    inference(ennf_transformation,[],[f17])).
% 27.69/4.07  
% 27.69/4.07  fof(f21,plain,(
% 27.69/4.07    ? [X0,X1] : ((~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0))),
% 27.69/4.07    inference(nnf_transformation,[],[f20])).
% 27.69/4.07  
% 27.69/4.07  fof(f22,plain,(
% 27.69/4.07    ? [X0,X1] : ((~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)) => ((~r2_hidden(sK0,sK1) | k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0) & (r2_hidden(sK0,sK1) | k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0))),
% 27.69/4.07    introduced(choice_axiom,[])).
% 27.69/4.07  
% 27.69/4.07  fof(f23,plain,(
% 27.69/4.07    (~r2_hidden(sK0,sK1) | k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0) & (r2_hidden(sK0,sK1) | k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0)),
% 27.69/4.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 27.69/4.07  
% 27.69/4.07  fof(f40,plain,(
% 27.69/4.07    ~r2_hidden(sK0,sK1) | k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0),
% 27.69/4.07    inference(cnf_transformation,[],[f23])).
% 27.69/4.07  
% 27.69/4.07  fof(f3,axiom,(
% 27.69/4.07    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 27.69/4.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/4.07  
% 27.69/4.07  fof(f26,plain,(
% 27.69/4.07    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 27.69/4.07    inference(cnf_transformation,[],[f3])).
% 27.69/4.07  
% 27.69/4.07  fof(f49,plain,(
% 27.69/4.07    ~r2_hidden(sK0,sK1) | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0),
% 27.69/4.07    inference(definition_unfolding,[],[f40,f26,f46])).
% 27.69/4.07  
% 27.69/4.07  fof(f4,axiom,(
% 27.69/4.07    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 27.69/4.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/4.07  
% 27.69/4.07  fof(f27,plain,(
% 27.69/4.07    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.69/4.07    inference(cnf_transformation,[],[f4])).
% 27.69/4.07  
% 27.69/4.07  fof(f5,axiom,(
% 27.69/4.07    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 27.69/4.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/4.07  
% 27.69/4.07  fof(f28,plain,(
% 27.69/4.07    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 27.69/4.07    inference(cnf_transformation,[],[f5])).
% 27.69/4.07  
% 27.69/4.07  fof(f15,axiom,(
% 27.69/4.07    ! [X0,X1] : (r2_hidden(X0,X1) => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0))),
% 27.69/4.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/4.07  
% 27.69/4.07  fof(f19,plain,(
% 27.69/4.07    ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1))),
% 27.69/4.07    inference(ennf_transformation,[],[f15])).
% 27.69/4.07  
% 27.69/4.07  fof(f38,plain,(
% 27.69/4.07    ( ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1)) )),
% 27.69/4.07    inference(cnf_transformation,[],[f19])).
% 27.69/4.07  
% 27.69/4.07  fof(f48,plain,(
% 27.69/4.07    ( ! [X0,X1] : (k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,X1)) )),
% 27.69/4.07    inference(definition_unfolding,[],[f38,f46,f46])).
% 27.69/4.07  
% 27.69/4.07  fof(f39,plain,(
% 27.69/4.07    r2_hidden(sK0,sK1) | k4_xboole_0(k1_tarski(sK0),sK1) = k1_xboole_0),
% 27.69/4.07    inference(cnf_transformation,[],[f23])).
% 27.69/4.07  
% 27.69/4.07  fof(f50,plain,(
% 27.69/4.07    r2_hidden(sK0,sK1) | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0),
% 27.69/4.07    inference(definition_unfolding,[],[f39,f26,f46])).
% 27.69/4.07  
% 27.69/4.07  fof(f2,axiom,(
% 27.69/4.07    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 27.69/4.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/4.07  
% 27.69/4.07  fof(f25,plain,(
% 27.69/4.07    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 27.69/4.07    inference(cnf_transformation,[],[f2])).
% 27.69/4.07  
% 27.69/4.07  fof(f1,axiom,(
% 27.69/4.07    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 27.69/4.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.69/4.07  
% 27.69/4.07  fof(f24,plain,(
% 27.69/4.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 27.69/4.07    inference(cnf_transformation,[],[f1])).
% 27.69/4.07  
% 27.69/4.07  cnf(c_129,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_191,plain,
% 27.69/4.07      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0
% 27.69/4.07      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
% 27.69/4.07      | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != X0 ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_129]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_153158,plain,
% 27.69/4.07      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k1_xboole_0))
% 27.69/4.07      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
% 27.69/4.07      | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_191]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_131,plain,
% 27.69/4.07      ( X0 != X1 | X2 != X3 | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
% 27.69/4.07      theory(equality) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_501,plain,
% 27.69/4.07      ( X0 != X1
% 27.69/4.07      | X2 != X3
% 27.69/4.07      | X4 != k5_xboole_0(X1,X3)
% 27.69/4.07      | k5_xboole_0(X0,X2) = X4 ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_131,c_129]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_128,plain,( X0 = X0 ),theory(equality) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_225,plain,
% 27.69/4.07      ( X0 != X1 | X1 = X0 ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_129,c_128]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_4,plain,
% 27.69/4.07      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.69/4.07      inference(cnf_transformation,[],[f29]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_236,plain,
% 27.69/4.07      ( k1_xboole_0 = k5_xboole_0(X0,X0) ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_225,c_4]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_1910,plain,
% 27.69/4.07      ( X0 != X1 | X2 != X1 | k5_xboole_0(X0,X2) = k1_xboole_0 ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_501,c_236]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_91526,plain,
% 27.69/4.07      ( X0 != X1 | k5_xboole_0(X0,X1) = k1_xboole_0 ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_1910,c_128]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_5,plain,
% 27.69/4.07      ( r2_hidden(X0,X1)
% 27.69/4.07      | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 27.69/4.07      inference(cnf_transformation,[],[f47]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_42,plain,
% 27.69/4.07      ( r2_hidden(X0,X1)
% 27.69/4.07      | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 27.69/4.07      inference(prop_impl,[status(thm)],[c_5]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_7,negated_conjecture,
% 27.69/4.07      ( ~ r2_hidden(sK0,sK1)
% 27.69/4.07      | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0 ),
% 27.69/4.07      inference(cnf_transformation,[],[f49]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_46,plain,
% 27.69/4.07      ( ~ r2_hidden(sK0,sK1)
% 27.69/4.07      | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0 ),
% 27.69/4.07      inference(prop_impl,[status(thm)],[c_7]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_88,plain,
% 27.69/4.07      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0
% 27.69/4.07      | k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
% 27.69/4.07      | sK1 != X0
% 27.69/4.07      | sK0 != X1 ),
% 27.69/4.07      inference(resolution_lifted,[status(thm)],[c_42,c_46]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_89,plain,
% 27.69/4.07      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0
% 27.69/4.07      | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 27.69/4.07      inference(unflattening,[status(thm)],[c_88]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_108,plain,
% 27.69/4.07      ( k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
% 27.69/4.07      | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0 ),
% 27.69/4.07      inference(prop_impl,[status(thm)],[c_89]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_109,plain,
% 27.69/4.07      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0
% 27.69/4.07      | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 27.69/4.07      inference(renaming,[status(thm)],[c_108]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_111536,plain,
% 27.69/4.07      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
% 27.69/4.07      | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_91526,c_109]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_253,plain,
% 27.69/4.07      ( X0 != X1
% 27.69/4.07      | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != X1
% 27.69/4.07      | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = X0 ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_129]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_829,plain,
% 27.69/4.07      ( X0 != k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0)
% 27.69/4.07      | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = X0
% 27.69/4.07      | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0) ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_253]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_24017,plain,
% 27.69/4.07      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k1_xboole_0)) != k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0)
% 27.69/4.07      | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k1_xboole_0))
% 27.69/4.07      | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0) ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_829]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_2,plain,
% 27.69/4.07      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.69/4.07      inference(cnf_transformation,[],[f27]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_3,plain,
% 27.69/4.07      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 27.69/4.07      inference(cnf_transformation,[],[f28]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_350,plain,
% 27.69/4.07      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 27.69/4.07      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_1035,plain,
% 27.69/4.07      ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 27.69/4.07      inference(superposition,[status(thm)],[c_2,c_350]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_6,plain,
% 27.69/4.07      ( ~ r2_hidden(X0,X1)
% 27.69/4.07      | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 27.69/4.07      inference(cnf_transformation,[],[f48]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_44,plain,
% 27.69/4.07      ( ~ r2_hidden(X0,X1)
% 27.69/4.07      | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 27.69/4.07      inference(prop_impl,[status(thm)],[c_6]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_8,negated_conjecture,
% 27.69/4.07      ( r2_hidden(sK0,sK1)
% 27.69/4.07      | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
% 27.69/4.07      inference(cnf_transformation,[],[f50]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_48,plain,
% 27.69/4.07      ( r2_hidden(sK0,sK1)
% 27.69/4.07      | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
% 27.69/4.07      inference(prop_impl,[status(thm)],[c_8]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_96,plain,
% 27.69/4.07      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0
% 27.69/4.07      | k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
% 27.69/4.07      | sK1 != X0
% 27.69/4.07      | sK0 != X1 ),
% 27.69/4.07      inference(resolution_lifted,[status(thm)],[c_44,c_48]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_97,plain,
% 27.69/4.07      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0
% 27.69/4.07      | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 27.69/4.07      inference(unflattening,[status(thm)],[c_96]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_110,plain,
% 27.69/4.07      ( k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
% 27.69/4.07      | k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
% 27.69/4.07      inference(prop_impl,[status(thm)],[c_97]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_111,plain,
% 27.69/4.07      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0
% 27.69/4.07      | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 27.69/4.07      inference(renaming,[status(thm)],[c_110]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_1,plain,
% 27.69/4.07      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 27.69/4.07      inference(cnf_transformation,[],[f25]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_164,plain,
% 27.69/4.07      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 27.69/4.07      inference(superposition,[status(thm)],[c_3,c_1]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_609,plain,
% 27.69/4.07      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = k5_xboole_0(X0,k1_xboole_0)
% 27.69/4.07      | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 27.69/4.07      inference(superposition,[status(thm)],[c_111,c_164]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_9734,plain,
% 27.69/4.07      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0)
% 27.69/4.07      | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 27.69/4.07      inference(superposition,[status(thm)],[c_1035,c_609]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_132,plain,
% 27.69/4.07      ( X0 != X1
% 27.69/4.07      | X2 != X3
% 27.69/4.07      | X4 != X5
% 27.69/4.07      | X6 != X7
% 27.69/4.07      | X8 != X9
% 27.69/4.07      | X10 != X11
% 27.69/4.07      | X12 != X13
% 27.69/4.07      | X14 != X15
% 27.69/4.07      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 27.69/4.07      theory(equality) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_522,plain,
% 27.69/4.07      ( X0 != X1
% 27.69/4.07      | X2 != X3
% 27.69/4.07      | X4 != X5
% 27.69/4.07      | X6 != X7
% 27.69/4.07      | X8 != X9
% 27.69/4.07      | X10 != X11
% 27.69/4.07      | X12 != X13
% 27.69/4.07      | X14 != X15
% 27.69/4.07      | X16 != k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15)
% 27.69/4.07      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = X16 ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_132,c_129]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_221,plain,
% 27.69/4.07      ( X0 != k5_xboole_0(X1,k5_xboole_0(X2,X3))
% 27.69/4.07      | k5_xboole_0(k5_xboole_0(X1,X2),X3) = X0 ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_129,c_3]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_232,plain,
% 27.69/4.07      ( X0 = k5_xboole_0(X0,k1_xboole_0) ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_225,c_2]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_242,plain,
% 27.69/4.07      ( X0 = X1 | X1 != k5_xboole_0(X0,k1_xboole_0) ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_232,c_129]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_369,plain,
% 27.69/4.07      ( X0 = k5_xboole_0(k1_xboole_0,X0) ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_242,c_1]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_381,plain,
% 27.69/4.07      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_369,c_225]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_676,plain,
% 27.69/4.07      ( X0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_381,c_242]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_1612,plain,
% 27.69/4.07      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_xboole_0) = X0 ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_221,c_676]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_2120,plain,
% 27.69/4.07      ( X0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_1612,c_225]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_218,plain,
% 27.69/4.07      ( X0 != k5_xboole_0(X1,X2) | k5_xboole_0(X2,X1) = X0 ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_129,c_1]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_2137,plain,
% 27.69/4.07      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = X0 ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_2120,c_218]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_2387,plain,
% 27.69/4.07      ( X0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_2137,c_225]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_2405,plain,
% 27.69/4.07      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0) = X0 ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_2387,c_221]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_2410,plain,
% 27.69/4.07      ( X0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0) ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_2405,c_225]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_2597,plain,
% 27.69/4.07      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_2410,c_218]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_3320,plain,
% 27.69/4.07      ( X0 != X1
% 27.69/4.07      | X2 != X3
% 27.69/4.07      | X4 != X5
% 27.69/4.07      | X6 != X7
% 27.69/4.07      | X8 != X9
% 27.69/4.07      | X10 != X11
% 27.69/4.07      | X12 != X13
% 27.69/4.07      | X14 != X15
% 27.69/4.07      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k5_xboole_0(k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15),k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 27.69/4.07      inference(resolution,[status(thm)],[c_522,c_2597]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_3321,plain,
% 27.69/4.07      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,k1_xboole_0))
% 27.69/4.07      | sK0 != sK0 ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_3320]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_386,plain,
% 27.69/4.07      ( X0 != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
% 27.69/4.07      | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = X0
% 27.69/4.07      | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_253]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_437,plain,
% 27.69/4.07      ( k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
% 27.69/4.07      | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0)
% 27.69/4.07      | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_386]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_387,plain,
% 27.69/4.07      ( k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_128]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_265,plain,
% 27.69/4.07      ( k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k1_xboole_0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_2]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_194,plain,
% 27.69/4.07      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0
% 27.69/4.07      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 27.69/4.07      | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != X0 ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_129]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_258,plain,
% 27.69/4.07      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
% 27.69/4.07      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 27.69/4.07      | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_194]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_0,plain,
% 27.69/4.07      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 27.69/4.07      inference(cnf_transformation,[],[f24]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_251,plain,
% 27.69/4.07      ( k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_0]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_250,plain,
% 27.69/4.07      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
% 27.69/4.07      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 27.69/4.07      | k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_191]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_183,plain,
% 27.69/4.07      ( k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_0]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_174,plain,
% 27.69/4.07      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0
% 27.69/4.07      | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != X0
% 27.69/4.07      | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_129]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_182,plain,
% 27.69/4.07      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
% 27.69/4.07      | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
% 27.69/4.07      | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_174]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_134,plain,
% 27.69/4.07      ( sK0 = sK0 ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_128]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(c_133,plain,
% 27.69/4.07      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
% 27.69/4.07      | sK0 != sK0 ),
% 27.69/4.07      inference(instantiation,[status(thm)],[c_132]) ).
% 27.69/4.07  
% 27.69/4.07  cnf(contradiction,plain,
% 27.69/4.07      ( $false ),
% 27.69/4.07      inference(minisat,
% 27.69/4.07                [status(thm)],
% 27.69/4.07                [c_153158,c_111536,c_24017,c_9734,c_3321,c_437,c_387,
% 27.69/4.07                 c_265,c_258,c_251,c_250,c_183,c_182,c_134,c_133]) ).
% 27.69/4.07  
% 27.69/4.07  
% 27.69/4.07  % SZS output end CNFRefutation for theBenchmark.p
% 27.69/4.07  
% 27.69/4.07  ------                               Statistics
% 27.69/4.07  
% 27.69/4.07  ------ Selected
% 27.69/4.07  
% 27.69/4.07  total_time:                             3.25
% 27.69/4.07  
%------------------------------------------------------------------------------
