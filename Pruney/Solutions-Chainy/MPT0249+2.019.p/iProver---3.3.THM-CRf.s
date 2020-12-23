%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:34 EST 2020

% Result     : Theorem 6.90s
% Output     : CNFRefutation 6.90s
% Verified   : 
% Statistics : Number of formulae       :  131 (1418 expanded)
%              Number of clauses        :   55 ( 139 expanded)
%              Number of leaves         :   25 ( 446 expanded)
%              Depth                    :   20
%              Number of atoms          :  227 (1982 expanded)
%              Number of equality atoms :  169 (1807 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34])).

fof(f58,plain,(
    k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f66])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f62])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f66])).

fof(f80,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f58,f67,f69])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f41,f67])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f32])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f54,f69,f69])).

fof(f60,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f35])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f69])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f69])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f67])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f44,f67])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f68])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f39,f68])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f38,f67])).

fof(f61,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_16,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_5,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_379,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_13118,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_379])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_374,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_15330,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13118,c_374])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_212,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_224,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_212])).

cnf(c_218,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_463,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | X0 != X2
    | X1 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_675,plain,
    ( r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | X0 != sK1
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_463])).

cnf(c_677,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_789,plain,
    ( ~ r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = X0
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_791,plain,
    ( ~ r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_789])).

cnf(c_928,plain,
    ( r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_15496,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15330,c_16,c_14,c_224,c_677,c_791,c_928])).

cnf(c_15500,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_15496,c_16])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_377,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_15506,plain,
    ( r2_hidden(sK0,X0) = iProver_top
    | r1_xboole_0(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15496,c_377])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_378,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_15505,plain,
    ( r2_hidden(sK0,X0) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15496,c_378])).

cnf(c_15772,plain,
    ( r1_tarski(sK1,X0) = iProver_top
    | r1_xboole_0(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15506,c_15505])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_380,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_19137,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = X0
    | r1_xboole_0(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15772,c_380])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_210,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_1,c_6,c_0])).

cnf(c_381,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_19623,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)))) = k1_xboole_0
    | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_19137,c_381])).

cnf(c_21329,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k1_xboole_0
    | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_15500,c_19623])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_743,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_740,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_6])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_209,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_3,c_6,c_0])).

cnf(c_2,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_400,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_209,c_2,c_7])).

cnf(c_577,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_400,c_0])).

cnf(c_753,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_740,c_577])).

cnf(c_997,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_743,c_753])).

cnf(c_1012,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_997,c_400])).

cnf(c_21824,plain,
    ( sK1 = sK2
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_21329,c_1012,c_15500])).

cnf(c_496,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_212])).

cnf(c_213,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_452,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_495,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_452])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_15,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21824,c_496,c_495,c_13,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:49:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.90/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.90/1.49  
% 6.90/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.90/1.49  
% 6.90/1.49  ------  iProver source info
% 6.90/1.49  
% 6.90/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.90/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.90/1.49  git: non_committed_changes: false
% 6.90/1.49  git: last_make_outside_of_git: false
% 6.90/1.49  
% 6.90/1.49  ------ 
% 6.90/1.49  
% 6.90/1.49  ------ Input Options
% 6.90/1.49  
% 6.90/1.49  --out_options                           all
% 6.90/1.49  --tptp_safe_out                         true
% 6.90/1.49  --problem_path                          ""
% 6.90/1.49  --include_path                          ""
% 6.90/1.49  --clausifier                            res/vclausify_rel
% 6.90/1.49  --clausifier_options                    --mode clausify
% 6.90/1.49  --stdin                                 false
% 6.90/1.49  --stats_out                             all
% 6.90/1.49  
% 6.90/1.49  ------ General Options
% 6.90/1.49  
% 6.90/1.49  --fof                                   false
% 6.90/1.49  --time_out_real                         305.
% 6.90/1.49  --time_out_virtual                      -1.
% 6.90/1.49  --symbol_type_check                     false
% 6.90/1.49  --clausify_out                          false
% 6.90/1.49  --sig_cnt_out                           false
% 6.90/1.49  --trig_cnt_out                          false
% 6.90/1.49  --trig_cnt_out_tolerance                1.
% 6.90/1.49  --trig_cnt_out_sk_spl                   false
% 6.90/1.49  --abstr_cl_out                          false
% 6.90/1.49  
% 6.90/1.49  ------ Global Options
% 6.90/1.49  
% 6.90/1.49  --schedule                              default
% 6.90/1.49  --add_important_lit                     false
% 6.90/1.49  --prop_solver_per_cl                    1000
% 6.90/1.49  --min_unsat_core                        false
% 6.90/1.49  --soft_assumptions                      false
% 6.90/1.49  --soft_lemma_size                       3
% 6.90/1.49  --prop_impl_unit_size                   0
% 6.90/1.49  --prop_impl_unit                        []
% 6.90/1.49  --share_sel_clauses                     true
% 6.90/1.49  --reset_solvers                         false
% 6.90/1.49  --bc_imp_inh                            [conj_cone]
% 6.90/1.49  --conj_cone_tolerance                   3.
% 6.90/1.49  --extra_neg_conj                        none
% 6.90/1.49  --large_theory_mode                     true
% 6.90/1.49  --prolific_symb_bound                   200
% 6.90/1.49  --lt_threshold                          2000
% 6.90/1.49  --clause_weak_htbl                      true
% 6.90/1.49  --gc_record_bc_elim                     false
% 6.90/1.49  
% 6.90/1.49  ------ Preprocessing Options
% 6.90/1.49  
% 6.90/1.49  --preprocessing_flag                    true
% 6.90/1.49  --time_out_prep_mult                    0.1
% 6.90/1.49  --splitting_mode                        input
% 6.90/1.49  --splitting_grd                         true
% 6.90/1.49  --splitting_cvd                         false
% 6.90/1.49  --splitting_cvd_svl                     false
% 6.90/1.49  --splitting_nvd                         32
% 6.90/1.49  --sub_typing                            true
% 6.90/1.49  --prep_gs_sim                           true
% 6.90/1.49  --prep_unflatten                        true
% 6.90/1.49  --prep_res_sim                          true
% 6.90/1.49  --prep_upred                            true
% 6.90/1.49  --prep_sem_filter                       exhaustive
% 6.90/1.49  --prep_sem_filter_out                   false
% 6.90/1.49  --pred_elim                             true
% 6.90/1.49  --res_sim_input                         true
% 6.90/1.49  --eq_ax_congr_red                       true
% 6.90/1.49  --pure_diseq_elim                       true
% 6.90/1.49  --brand_transform                       false
% 6.90/1.49  --non_eq_to_eq                          false
% 6.90/1.49  --prep_def_merge                        true
% 6.90/1.49  --prep_def_merge_prop_impl              false
% 6.90/1.49  --prep_def_merge_mbd                    true
% 6.90/1.49  --prep_def_merge_tr_red                 false
% 6.90/1.49  --prep_def_merge_tr_cl                  false
% 6.90/1.49  --smt_preprocessing                     true
% 6.90/1.49  --smt_ac_axioms                         fast
% 6.90/1.49  --preprocessed_out                      false
% 6.90/1.49  --preprocessed_stats                    false
% 6.90/1.49  
% 6.90/1.49  ------ Abstraction refinement Options
% 6.90/1.49  
% 6.90/1.49  --abstr_ref                             []
% 6.90/1.49  --abstr_ref_prep                        false
% 6.90/1.49  --abstr_ref_until_sat                   false
% 6.90/1.49  --abstr_ref_sig_restrict                funpre
% 6.90/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.90/1.49  --abstr_ref_under                       []
% 6.90/1.49  
% 6.90/1.49  ------ SAT Options
% 6.90/1.49  
% 6.90/1.49  --sat_mode                              false
% 6.90/1.49  --sat_fm_restart_options                ""
% 6.90/1.49  --sat_gr_def                            false
% 6.90/1.49  --sat_epr_types                         true
% 6.90/1.49  --sat_non_cyclic_types                  false
% 6.90/1.49  --sat_finite_models                     false
% 6.90/1.49  --sat_fm_lemmas                         false
% 6.90/1.49  --sat_fm_prep                           false
% 6.90/1.49  --sat_fm_uc_incr                        true
% 6.90/1.49  --sat_out_model                         small
% 6.90/1.49  --sat_out_clauses                       false
% 6.90/1.49  
% 6.90/1.49  ------ QBF Options
% 6.90/1.49  
% 6.90/1.49  --qbf_mode                              false
% 6.90/1.49  --qbf_elim_univ                         false
% 6.90/1.49  --qbf_dom_inst                          none
% 6.90/1.49  --qbf_dom_pre_inst                      false
% 6.90/1.49  --qbf_sk_in                             false
% 6.90/1.49  --qbf_pred_elim                         true
% 6.90/1.49  --qbf_split                             512
% 6.90/1.49  
% 6.90/1.49  ------ BMC1 Options
% 6.90/1.49  
% 6.90/1.49  --bmc1_incremental                      false
% 6.90/1.49  --bmc1_axioms                           reachable_all
% 6.90/1.49  --bmc1_min_bound                        0
% 6.90/1.49  --bmc1_max_bound                        -1
% 6.90/1.49  --bmc1_max_bound_default                -1
% 6.90/1.49  --bmc1_symbol_reachability              true
% 6.90/1.49  --bmc1_property_lemmas                  false
% 6.90/1.49  --bmc1_k_induction                      false
% 6.90/1.49  --bmc1_non_equiv_states                 false
% 6.90/1.49  --bmc1_deadlock                         false
% 6.90/1.49  --bmc1_ucm                              false
% 6.90/1.49  --bmc1_add_unsat_core                   none
% 6.90/1.49  --bmc1_unsat_core_children              false
% 6.90/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.90/1.49  --bmc1_out_stat                         full
% 6.90/1.49  --bmc1_ground_init                      false
% 6.90/1.49  --bmc1_pre_inst_next_state              false
% 6.90/1.49  --bmc1_pre_inst_state                   false
% 6.90/1.49  --bmc1_pre_inst_reach_state             false
% 6.90/1.49  --bmc1_out_unsat_core                   false
% 6.90/1.49  --bmc1_aig_witness_out                  false
% 6.90/1.49  --bmc1_verbose                          false
% 6.90/1.49  --bmc1_dump_clauses_tptp                false
% 6.90/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.90/1.49  --bmc1_dump_file                        -
% 6.90/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.90/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.90/1.49  --bmc1_ucm_extend_mode                  1
% 6.90/1.49  --bmc1_ucm_init_mode                    2
% 6.90/1.49  --bmc1_ucm_cone_mode                    none
% 6.90/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.90/1.49  --bmc1_ucm_relax_model                  4
% 6.90/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.90/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.90/1.49  --bmc1_ucm_layered_model                none
% 6.90/1.49  --bmc1_ucm_max_lemma_size               10
% 6.90/1.49  
% 6.90/1.49  ------ AIG Options
% 6.90/1.49  
% 6.90/1.49  --aig_mode                              false
% 6.90/1.49  
% 6.90/1.49  ------ Instantiation Options
% 6.90/1.49  
% 6.90/1.49  --instantiation_flag                    true
% 6.90/1.49  --inst_sos_flag                         false
% 6.90/1.49  --inst_sos_phase                        true
% 6.90/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.90/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.90/1.49  --inst_lit_sel_side                     num_symb
% 6.90/1.49  --inst_solver_per_active                1400
% 6.90/1.49  --inst_solver_calls_frac                1.
% 6.90/1.49  --inst_passive_queue_type               priority_queues
% 6.90/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.90/1.49  --inst_passive_queues_freq              [25;2]
% 6.90/1.49  --inst_dismatching                      true
% 6.90/1.49  --inst_eager_unprocessed_to_passive     true
% 6.90/1.49  --inst_prop_sim_given                   true
% 6.90/1.49  --inst_prop_sim_new                     false
% 6.90/1.49  --inst_subs_new                         false
% 6.90/1.49  --inst_eq_res_simp                      false
% 6.90/1.49  --inst_subs_given                       false
% 6.90/1.49  --inst_orphan_elimination               true
% 6.90/1.49  --inst_learning_loop_flag               true
% 6.90/1.49  --inst_learning_start                   3000
% 6.90/1.49  --inst_learning_factor                  2
% 6.90/1.49  --inst_start_prop_sim_after_learn       3
% 6.90/1.49  --inst_sel_renew                        solver
% 6.90/1.49  --inst_lit_activity_flag                true
% 6.90/1.49  --inst_restr_to_given                   false
% 6.90/1.49  --inst_activity_threshold               500
% 6.90/1.49  --inst_out_proof                        true
% 6.90/1.49  
% 6.90/1.49  ------ Resolution Options
% 6.90/1.49  
% 6.90/1.49  --resolution_flag                       true
% 6.90/1.49  --res_lit_sel                           adaptive
% 6.90/1.49  --res_lit_sel_side                      none
% 6.90/1.49  --res_ordering                          kbo
% 6.90/1.49  --res_to_prop_solver                    active
% 6.90/1.49  --res_prop_simpl_new                    false
% 6.90/1.49  --res_prop_simpl_given                  true
% 6.90/1.49  --res_passive_queue_type                priority_queues
% 6.90/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.90/1.49  --res_passive_queues_freq               [15;5]
% 6.90/1.49  --res_forward_subs                      full
% 6.90/1.49  --res_backward_subs                     full
% 6.90/1.49  --res_forward_subs_resolution           true
% 6.90/1.49  --res_backward_subs_resolution          true
% 6.90/1.49  --res_orphan_elimination                true
% 6.90/1.49  --res_time_limit                        2.
% 6.90/1.49  --res_out_proof                         true
% 6.90/1.49  
% 6.90/1.49  ------ Superposition Options
% 6.90/1.49  
% 6.90/1.49  --superposition_flag                    true
% 6.90/1.49  --sup_passive_queue_type                priority_queues
% 6.90/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.90/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.90/1.49  --demod_completeness_check              fast
% 6.90/1.49  --demod_use_ground                      true
% 6.90/1.49  --sup_to_prop_solver                    passive
% 6.90/1.49  --sup_prop_simpl_new                    true
% 6.90/1.49  --sup_prop_simpl_given                  true
% 6.90/1.49  --sup_fun_splitting                     false
% 6.90/1.49  --sup_smt_interval                      50000
% 6.90/1.49  
% 6.90/1.49  ------ Superposition Simplification Setup
% 6.90/1.49  
% 6.90/1.49  --sup_indices_passive                   []
% 6.90/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.90/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.49  --sup_full_bw                           [BwDemod]
% 6.90/1.49  --sup_immed_triv                        [TrivRules]
% 6.90/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.90/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.49  --sup_immed_bw_main                     []
% 6.90/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.90/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.90/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.90/1.49  
% 6.90/1.49  ------ Combination Options
% 6.90/1.49  
% 6.90/1.49  --comb_res_mult                         3
% 6.90/1.49  --comb_sup_mult                         2
% 6.90/1.49  --comb_inst_mult                        10
% 6.90/1.49  
% 6.90/1.49  ------ Debug Options
% 6.90/1.49  
% 6.90/1.49  --dbg_backtrace                         false
% 6.90/1.49  --dbg_dump_prop_clauses                 false
% 6.90/1.49  --dbg_dump_prop_clauses_file            -
% 6.90/1.49  --dbg_out_stat                          false
% 6.90/1.49  ------ Parsing...
% 6.90/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.90/1.49  
% 6.90/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.90/1.49  
% 6.90/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.90/1.49  
% 6.90/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.90/1.49  ------ Proving...
% 6.90/1.49  ------ Problem Properties 
% 6.90/1.49  
% 6.90/1.49  
% 6.90/1.49  clauses                                 17
% 6.90/1.49  conjectures                             4
% 6.90/1.49  EPR                                     3
% 6.90/1.49  Horn                                    15
% 6.90/1.49  unary                                   12
% 6.90/1.49  binary                                  4
% 6.90/1.49  lits                                    23
% 6.90/1.49  lits eq                                 13
% 6.90/1.49  fd_pure                                 0
% 6.90/1.49  fd_pseudo                               0
% 6.90/1.49  fd_cond                                 0
% 6.90/1.49  fd_pseudo_cond                          1
% 6.90/1.49  AC symbols                              1
% 6.90/1.49  
% 6.90/1.49  ------ Schedule dynamic 5 is on 
% 6.90/1.49  
% 6.90/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.90/1.49  
% 6.90/1.49  
% 6.90/1.49  ------ 
% 6.90/1.49  Current options:
% 6.90/1.49  ------ 
% 6.90/1.49  
% 6.90/1.49  ------ Input Options
% 6.90/1.49  
% 6.90/1.49  --out_options                           all
% 6.90/1.49  --tptp_safe_out                         true
% 6.90/1.49  --problem_path                          ""
% 6.90/1.49  --include_path                          ""
% 6.90/1.49  --clausifier                            res/vclausify_rel
% 6.90/1.49  --clausifier_options                    --mode clausify
% 6.90/1.49  --stdin                                 false
% 6.90/1.49  --stats_out                             all
% 6.90/1.49  
% 6.90/1.49  ------ General Options
% 6.90/1.49  
% 6.90/1.49  --fof                                   false
% 6.90/1.49  --time_out_real                         305.
% 6.90/1.49  --time_out_virtual                      -1.
% 6.90/1.49  --symbol_type_check                     false
% 6.90/1.49  --clausify_out                          false
% 6.90/1.49  --sig_cnt_out                           false
% 6.90/1.49  --trig_cnt_out                          false
% 6.90/1.49  --trig_cnt_out_tolerance                1.
% 6.90/1.49  --trig_cnt_out_sk_spl                   false
% 6.90/1.49  --abstr_cl_out                          false
% 6.90/1.49  
% 6.90/1.49  ------ Global Options
% 6.90/1.49  
% 6.90/1.49  --schedule                              default
% 6.90/1.49  --add_important_lit                     false
% 6.90/1.49  --prop_solver_per_cl                    1000
% 6.90/1.49  --min_unsat_core                        false
% 6.90/1.49  --soft_assumptions                      false
% 6.90/1.49  --soft_lemma_size                       3
% 6.90/1.49  --prop_impl_unit_size                   0
% 6.90/1.49  --prop_impl_unit                        []
% 6.90/1.49  --share_sel_clauses                     true
% 6.90/1.49  --reset_solvers                         false
% 6.90/1.49  --bc_imp_inh                            [conj_cone]
% 6.90/1.49  --conj_cone_tolerance                   3.
% 6.90/1.49  --extra_neg_conj                        none
% 6.90/1.49  --large_theory_mode                     true
% 6.90/1.49  --prolific_symb_bound                   200
% 6.90/1.49  --lt_threshold                          2000
% 6.90/1.49  --clause_weak_htbl                      true
% 6.90/1.49  --gc_record_bc_elim                     false
% 6.90/1.49  
% 6.90/1.49  ------ Preprocessing Options
% 6.90/1.49  
% 6.90/1.49  --preprocessing_flag                    true
% 6.90/1.49  --time_out_prep_mult                    0.1
% 6.90/1.49  --splitting_mode                        input
% 6.90/1.49  --splitting_grd                         true
% 6.90/1.49  --splitting_cvd                         false
% 6.90/1.49  --splitting_cvd_svl                     false
% 6.90/1.49  --splitting_nvd                         32
% 6.90/1.49  --sub_typing                            true
% 6.90/1.49  --prep_gs_sim                           true
% 6.90/1.49  --prep_unflatten                        true
% 6.90/1.49  --prep_res_sim                          true
% 6.90/1.49  --prep_upred                            true
% 6.90/1.49  --prep_sem_filter                       exhaustive
% 6.90/1.49  --prep_sem_filter_out                   false
% 6.90/1.49  --pred_elim                             true
% 6.90/1.49  --res_sim_input                         true
% 6.90/1.49  --eq_ax_congr_red                       true
% 6.90/1.49  --pure_diseq_elim                       true
% 6.90/1.49  --brand_transform                       false
% 6.90/1.49  --non_eq_to_eq                          false
% 6.90/1.49  --prep_def_merge                        true
% 6.90/1.49  --prep_def_merge_prop_impl              false
% 6.90/1.49  --prep_def_merge_mbd                    true
% 6.90/1.49  --prep_def_merge_tr_red                 false
% 6.90/1.49  --prep_def_merge_tr_cl                  false
% 6.90/1.49  --smt_preprocessing                     true
% 6.90/1.49  --smt_ac_axioms                         fast
% 6.90/1.49  --preprocessed_out                      false
% 6.90/1.49  --preprocessed_stats                    false
% 6.90/1.49  
% 6.90/1.49  ------ Abstraction refinement Options
% 6.90/1.49  
% 6.90/1.49  --abstr_ref                             []
% 6.90/1.49  --abstr_ref_prep                        false
% 6.90/1.49  --abstr_ref_until_sat                   false
% 6.90/1.49  --abstr_ref_sig_restrict                funpre
% 6.90/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.90/1.49  --abstr_ref_under                       []
% 6.90/1.49  
% 6.90/1.49  ------ SAT Options
% 6.90/1.49  
% 6.90/1.49  --sat_mode                              false
% 6.90/1.49  --sat_fm_restart_options                ""
% 6.90/1.49  --sat_gr_def                            false
% 6.90/1.49  --sat_epr_types                         true
% 6.90/1.49  --sat_non_cyclic_types                  false
% 6.90/1.49  --sat_finite_models                     false
% 6.90/1.49  --sat_fm_lemmas                         false
% 6.90/1.49  --sat_fm_prep                           false
% 6.90/1.49  --sat_fm_uc_incr                        true
% 6.90/1.49  --sat_out_model                         small
% 6.90/1.49  --sat_out_clauses                       false
% 6.90/1.49  
% 6.90/1.49  ------ QBF Options
% 6.90/1.49  
% 6.90/1.49  --qbf_mode                              false
% 6.90/1.49  --qbf_elim_univ                         false
% 6.90/1.49  --qbf_dom_inst                          none
% 6.90/1.49  --qbf_dom_pre_inst                      false
% 6.90/1.49  --qbf_sk_in                             false
% 6.90/1.49  --qbf_pred_elim                         true
% 6.90/1.49  --qbf_split                             512
% 6.90/1.49  
% 6.90/1.49  ------ BMC1 Options
% 6.90/1.49  
% 6.90/1.49  --bmc1_incremental                      false
% 6.90/1.49  --bmc1_axioms                           reachable_all
% 6.90/1.49  --bmc1_min_bound                        0
% 6.90/1.49  --bmc1_max_bound                        -1
% 6.90/1.49  --bmc1_max_bound_default                -1
% 6.90/1.49  --bmc1_symbol_reachability              true
% 6.90/1.49  --bmc1_property_lemmas                  false
% 6.90/1.49  --bmc1_k_induction                      false
% 6.90/1.49  --bmc1_non_equiv_states                 false
% 6.90/1.49  --bmc1_deadlock                         false
% 6.90/1.49  --bmc1_ucm                              false
% 6.90/1.49  --bmc1_add_unsat_core                   none
% 6.90/1.49  --bmc1_unsat_core_children              false
% 6.90/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.90/1.49  --bmc1_out_stat                         full
% 6.90/1.49  --bmc1_ground_init                      false
% 6.90/1.49  --bmc1_pre_inst_next_state              false
% 6.90/1.49  --bmc1_pre_inst_state                   false
% 6.90/1.49  --bmc1_pre_inst_reach_state             false
% 6.90/1.49  --bmc1_out_unsat_core                   false
% 6.90/1.49  --bmc1_aig_witness_out                  false
% 6.90/1.49  --bmc1_verbose                          false
% 6.90/1.49  --bmc1_dump_clauses_tptp                false
% 6.90/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.90/1.49  --bmc1_dump_file                        -
% 6.90/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.90/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.90/1.49  --bmc1_ucm_extend_mode                  1
% 6.90/1.49  --bmc1_ucm_init_mode                    2
% 6.90/1.49  --bmc1_ucm_cone_mode                    none
% 6.90/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.90/1.49  --bmc1_ucm_relax_model                  4
% 6.90/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.90/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.90/1.49  --bmc1_ucm_layered_model                none
% 6.90/1.49  --bmc1_ucm_max_lemma_size               10
% 6.90/1.49  
% 6.90/1.49  ------ AIG Options
% 6.90/1.49  
% 6.90/1.49  --aig_mode                              false
% 6.90/1.49  
% 6.90/1.49  ------ Instantiation Options
% 6.90/1.49  
% 6.90/1.49  --instantiation_flag                    true
% 6.90/1.49  --inst_sos_flag                         false
% 6.90/1.49  --inst_sos_phase                        true
% 6.90/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.90/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.90/1.49  --inst_lit_sel_side                     none
% 6.90/1.49  --inst_solver_per_active                1400
% 6.90/1.49  --inst_solver_calls_frac                1.
% 6.90/1.49  --inst_passive_queue_type               priority_queues
% 6.90/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.90/1.49  --inst_passive_queues_freq              [25;2]
% 6.90/1.49  --inst_dismatching                      true
% 6.90/1.49  --inst_eager_unprocessed_to_passive     true
% 6.90/1.49  --inst_prop_sim_given                   true
% 6.90/1.49  --inst_prop_sim_new                     false
% 6.90/1.49  --inst_subs_new                         false
% 6.90/1.49  --inst_eq_res_simp                      false
% 6.90/1.49  --inst_subs_given                       false
% 6.90/1.49  --inst_orphan_elimination               true
% 6.90/1.49  --inst_learning_loop_flag               true
% 6.90/1.49  --inst_learning_start                   3000
% 6.90/1.49  --inst_learning_factor                  2
% 6.90/1.49  --inst_start_prop_sim_after_learn       3
% 6.90/1.49  --inst_sel_renew                        solver
% 6.90/1.49  --inst_lit_activity_flag                true
% 6.90/1.49  --inst_restr_to_given                   false
% 6.90/1.49  --inst_activity_threshold               500
% 6.90/1.49  --inst_out_proof                        true
% 6.90/1.49  
% 6.90/1.49  ------ Resolution Options
% 6.90/1.49  
% 6.90/1.49  --resolution_flag                       false
% 6.90/1.49  --res_lit_sel                           adaptive
% 6.90/1.49  --res_lit_sel_side                      none
% 6.90/1.49  --res_ordering                          kbo
% 6.90/1.49  --res_to_prop_solver                    active
% 6.90/1.49  --res_prop_simpl_new                    false
% 6.90/1.49  --res_prop_simpl_given                  true
% 6.90/1.49  --res_passive_queue_type                priority_queues
% 6.90/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.90/1.49  --res_passive_queues_freq               [15;5]
% 6.90/1.49  --res_forward_subs                      full
% 6.90/1.49  --res_backward_subs                     full
% 6.90/1.49  --res_forward_subs_resolution           true
% 6.90/1.49  --res_backward_subs_resolution          true
% 6.90/1.49  --res_orphan_elimination                true
% 6.90/1.49  --res_time_limit                        2.
% 6.90/1.49  --res_out_proof                         true
% 6.90/1.49  
% 6.90/1.49  ------ Superposition Options
% 6.90/1.49  
% 6.90/1.49  --superposition_flag                    true
% 6.90/1.49  --sup_passive_queue_type                priority_queues
% 6.90/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.90/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.90/1.49  --demod_completeness_check              fast
% 6.90/1.49  --demod_use_ground                      true
% 6.90/1.49  --sup_to_prop_solver                    passive
% 6.90/1.49  --sup_prop_simpl_new                    true
% 6.90/1.49  --sup_prop_simpl_given                  true
% 6.90/1.49  --sup_fun_splitting                     false
% 6.90/1.49  --sup_smt_interval                      50000
% 6.90/1.49  
% 6.90/1.49  ------ Superposition Simplification Setup
% 6.90/1.49  
% 6.90/1.49  --sup_indices_passive                   []
% 6.90/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.90/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.49  --sup_full_bw                           [BwDemod]
% 6.90/1.49  --sup_immed_triv                        [TrivRules]
% 6.90/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.90/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.49  --sup_immed_bw_main                     []
% 6.90/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.90/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.90/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.90/1.49  
% 6.90/1.49  ------ Combination Options
% 6.90/1.49  
% 6.90/1.49  --comb_res_mult                         3
% 6.90/1.49  --comb_sup_mult                         2
% 6.90/1.49  --comb_inst_mult                        10
% 6.90/1.49  
% 6.90/1.49  ------ Debug Options
% 6.90/1.49  
% 6.90/1.49  --dbg_backtrace                         false
% 6.90/1.49  --dbg_dump_prop_clauses                 false
% 6.90/1.49  --dbg_dump_prop_clauses_file            -
% 6.90/1.49  --dbg_out_stat                          false
% 6.90/1.49  
% 6.90/1.49  
% 6.90/1.49  
% 6.90/1.49  
% 6.90/1.49  ------ Proving...
% 6.90/1.49  
% 6.90/1.49  
% 6.90/1.49  % SZS status Theorem for theBenchmark.p
% 6.90/1.49  
% 6.90/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.90/1.49  
% 6.90/1.49  fof(f21,conjecture,(
% 6.90/1.49    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f22,negated_conjecture,(
% 6.90/1.49    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 6.90/1.49    inference(negated_conjecture,[],[f21])).
% 6.90/1.49  
% 6.90/1.49  fof(f31,plain,(
% 6.90/1.49    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 6.90/1.49    inference(ennf_transformation,[],[f22])).
% 6.90/1.49  
% 6.90/1.49  fof(f34,plain,(
% 6.90/1.49    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k2_xboole_0(sK1,sK2) = k1_tarski(sK0))),
% 6.90/1.49    introduced(choice_axiom,[])).
% 6.90/1.49  
% 6.90/1.49  fof(f35,plain,(
% 6.90/1.49    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 6.90/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34])).
% 6.90/1.49  
% 6.90/1.49  fof(f58,plain,(
% 6.90/1.49    k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 6.90/1.49    inference(cnf_transformation,[],[f35])).
% 6.90/1.49  
% 6.90/1.49  fof(f20,axiom,(
% 6.90/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f57,plain,(
% 6.90/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 6.90/1.49    inference(cnf_transformation,[],[f20])).
% 6.90/1.49  
% 6.90/1.49  fof(f67,plain,(
% 6.90/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 6.90/1.49    inference(definition_unfolding,[],[f57,f66])).
% 6.90/1.49  
% 6.90/1.49  fof(f10,axiom,(
% 6.90/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f45,plain,(
% 6.90/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f10])).
% 6.90/1.49  
% 6.90/1.49  fof(f11,axiom,(
% 6.90/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f46,plain,(
% 6.90/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f11])).
% 6.90/1.49  
% 6.90/1.49  fof(f12,axiom,(
% 6.90/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f47,plain,(
% 6.90/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f12])).
% 6.90/1.49  
% 6.90/1.49  fof(f13,axiom,(
% 6.90/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f48,plain,(
% 6.90/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f13])).
% 6.90/1.49  
% 6.90/1.49  fof(f14,axiom,(
% 6.90/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f49,plain,(
% 6.90/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f14])).
% 6.90/1.49  
% 6.90/1.49  fof(f15,axiom,(
% 6.90/1.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f50,plain,(
% 6.90/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f15])).
% 6.90/1.49  
% 6.90/1.49  fof(f16,axiom,(
% 6.90/1.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f51,plain,(
% 6.90/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f16])).
% 6.90/1.49  
% 6.90/1.49  fof(f62,plain,(
% 6.90/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 6.90/1.49    inference(definition_unfolding,[],[f50,f51])).
% 6.90/1.49  
% 6.90/1.49  fof(f63,plain,(
% 6.90/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 6.90/1.49    inference(definition_unfolding,[],[f49,f62])).
% 6.90/1.49  
% 6.90/1.49  fof(f64,plain,(
% 6.90/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 6.90/1.49    inference(definition_unfolding,[],[f48,f63])).
% 6.90/1.49  
% 6.90/1.49  fof(f65,plain,(
% 6.90/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 6.90/1.49    inference(definition_unfolding,[],[f47,f64])).
% 6.90/1.49  
% 6.90/1.49  fof(f66,plain,(
% 6.90/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 6.90/1.49    inference(definition_unfolding,[],[f46,f65])).
% 6.90/1.49  
% 6.90/1.49  fof(f69,plain,(
% 6.90/1.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 6.90/1.49    inference(definition_unfolding,[],[f45,f66])).
% 6.90/1.49  
% 6.90/1.49  fof(f80,plain,(
% 6.90/1.49    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 6.90/1.49    inference(definition_unfolding,[],[f58,f67,f69])).
% 6.90/1.49  
% 6.90/1.49  fof(f6,axiom,(
% 6.90/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f41,plain,(
% 6.90/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 6.90/1.49    inference(cnf_transformation,[],[f6])).
% 6.90/1.49  
% 6.90/1.49  fof(f74,plain,(
% 6.90/1.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 6.90/1.49    inference(definition_unfolding,[],[f41,f67])).
% 6.90/1.49  
% 6.90/1.49  fof(f19,axiom,(
% 6.90/1.49    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f32,plain,(
% 6.90/1.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 6.90/1.49    inference(nnf_transformation,[],[f19])).
% 6.90/1.49  
% 6.90/1.49  fof(f33,plain,(
% 6.90/1.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 6.90/1.49    inference(flattening,[],[f32])).
% 6.90/1.49  
% 6.90/1.49  fof(f54,plain,(
% 6.90/1.49    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 6.90/1.49    inference(cnf_transformation,[],[f33])).
% 6.90/1.49  
% 6.90/1.49  fof(f79,plain,(
% 6.90/1.49    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 6.90/1.49    inference(definition_unfolding,[],[f54,f69,f69])).
% 6.90/1.49  
% 6.90/1.49  fof(f60,plain,(
% 6.90/1.49    k1_xboole_0 != sK1),
% 6.90/1.49    inference(cnf_transformation,[],[f35])).
% 6.90/1.49  
% 6.90/1.49  fof(f18,axiom,(
% 6.90/1.49    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f30,plain,(
% 6.90/1.49    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 6.90/1.49    inference(ennf_transformation,[],[f18])).
% 6.90/1.49  
% 6.90/1.49  fof(f53,plain,(
% 6.90/1.49    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f30])).
% 6.90/1.49  
% 6.90/1.49  fof(f76,plain,(
% 6.90/1.49    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 6.90/1.49    inference(definition_unfolding,[],[f53,f69])).
% 6.90/1.49  
% 6.90/1.49  fof(f17,axiom,(
% 6.90/1.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f25,plain,(
% 6.90/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 6.90/1.49    inference(unused_predicate_definition_removal,[],[f17])).
% 6.90/1.49  
% 6.90/1.49  fof(f29,plain,(
% 6.90/1.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 6.90/1.49    inference(ennf_transformation,[],[f25])).
% 6.90/1.49  
% 6.90/1.49  fof(f52,plain,(
% 6.90/1.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f29])).
% 6.90/1.49  
% 6.90/1.49  fof(f75,plain,(
% 6.90/1.49    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 6.90/1.49    inference(definition_unfolding,[],[f52,f69])).
% 6.90/1.49  
% 6.90/1.49  fof(f5,axiom,(
% 6.90/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f28,plain,(
% 6.90/1.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 6.90/1.49    inference(ennf_transformation,[],[f5])).
% 6.90/1.49  
% 6.90/1.49  fof(f40,plain,(
% 6.90/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f28])).
% 6.90/1.49  
% 6.90/1.49  fof(f73,plain,(
% 6.90/1.49    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 6.90/1.49    inference(definition_unfolding,[],[f40,f67])).
% 6.90/1.49  
% 6.90/1.49  fof(f2,axiom,(
% 6.90/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f26,plain,(
% 6.90/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 6.90/1.49    inference(unused_predicate_definition_removal,[],[f2])).
% 6.90/1.49  
% 6.90/1.49  fof(f27,plain,(
% 6.90/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 6.90/1.49    inference(ennf_transformation,[],[f26])).
% 6.90/1.49  
% 6.90/1.49  fof(f37,plain,(
% 6.90/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f27])).
% 6.90/1.49  
% 6.90/1.49  fof(f9,axiom,(
% 6.90/1.49    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f44,plain,(
% 6.90/1.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f9])).
% 6.90/1.49  
% 6.90/1.49  fof(f68,plain,(
% 6.90/1.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 6.90/1.49    inference(definition_unfolding,[],[f44,f67])).
% 6.90/1.49  
% 6.90/1.49  fof(f70,plain,(
% 6.90/1.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 6.90/1.49    inference(definition_unfolding,[],[f37,f68])).
% 6.90/1.49  
% 6.90/1.49  fof(f7,axiom,(
% 6.90/1.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f42,plain,(
% 6.90/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f7])).
% 6.90/1.49  
% 6.90/1.49  fof(f1,axiom,(
% 6.90/1.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f36,plain,(
% 6.90/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 6.90/1.49    inference(cnf_transformation,[],[f1])).
% 6.90/1.49  
% 6.90/1.49  fof(f8,axiom,(
% 6.90/1.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f43,plain,(
% 6.90/1.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 6.90/1.49    inference(cnf_transformation,[],[f8])).
% 6.90/1.49  
% 6.90/1.49  fof(f4,axiom,(
% 6.90/1.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f24,plain,(
% 6.90/1.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 6.90/1.49    inference(rectify,[],[f4])).
% 6.90/1.49  
% 6.90/1.49  fof(f39,plain,(
% 6.90/1.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 6.90/1.49    inference(cnf_transformation,[],[f24])).
% 6.90/1.49  
% 6.90/1.49  fof(f72,plain,(
% 6.90/1.49    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 6.90/1.49    inference(definition_unfolding,[],[f39,f68])).
% 6.90/1.49  
% 6.90/1.49  fof(f3,axiom,(
% 6.90/1.49    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 6.90/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.49  
% 6.90/1.49  fof(f23,plain,(
% 6.90/1.49    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 6.90/1.49    inference(rectify,[],[f3])).
% 6.90/1.49  
% 6.90/1.49  fof(f38,plain,(
% 6.90/1.49    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 6.90/1.49    inference(cnf_transformation,[],[f23])).
% 6.90/1.49  
% 6.90/1.49  fof(f71,plain,(
% 6.90/1.49    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 6.90/1.49    inference(definition_unfolding,[],[f38,f67])).
% 6.90/1.49  
% 6.90/1.49  fof(f61,plain,(
% 6.90/1.49    k1_xboole_0 != sK2),
% 6.90/1.49    inference(cnf_transformation,[],[f35])).
% 6.90/1.49  
% 6.90/1.49  fof(f59,plain,(
% 6.90/1.49    sK1 != sK2),
% 6.90/1.49    inference(cnf_transformation,[],[f35])).
% 6.90/1.49  
% 6.90/1.49  cnf(c_16,negated_conjecture,
% 6.90/1.49      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 6.90/1.49      inference(cnf_transformation,[],[f80]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_5,plain,
% 6.90/1.49      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 6.90/1.49      inference(cnf_transformation,[],[f74]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_379,plain,
% 6.90/1.49      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 6.90/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_13118,plain,
% 6.90/1.49      ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 6.90/1.49      inference(superposition,[status(thm)],[c_16,c_379]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_12,plain,
% 6.90/1.49      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 6.90/1.49      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 6.90/1.49      | k1_xboole_0 = X0 ),
% 6.90/1.49      inference(cnf_transformation,[],[f79]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_374,plain,
% 6.90/1.49      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 6.90/1.49      | k1_xboole_0 = X1
% 6.90/1.49      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 6.90/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_15330,plain,
% 6.90/1.49      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
% 6.90/1.49      | sK1 = k1_xboole_0 ),
% 6.90/1.49      inference(superposition,[status(thm)],[c_13118,c_374]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_14,negated_conjecture,
% 6.90/1.49      ( k1_xboole_0 != sK1 ),
% 6.90/1.49      inference(cnf_transformation,[],[f60]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_212,plain,( X0 = X0 ),theory(equality) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_224,plain,
% 6.90/1.49      ( sK1 = sK1 ),
% 6.90/1.49      inference(instantiation,[status(thm)],[c_212]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_218,plain,
% 6.90/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.90/1.49      theory(equality) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_463,plain,
% 6.90/1.49      ( r1_tarski(X0,X1)
% 6.90/1.49      | ~ r1_tarski(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
% 6.90/1.49      | X0 != X2
% 6.90/1.49      | X1 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
% 6.90/1.49      inference(instantiation,[status(thm)],[c_218]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_675,plain,
% 6.90/1.49      ( r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 6.90/1.49      | ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
% 6.90/1.49      | X0 != sK1
% 6.90/1.49      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 6.90/1.49      inference(instantiation,[status(thm)],[c_463]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_677,plain,
% 6.90/1.49      ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 6.90/1.49      | ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
% 6.90/1.49      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 6.90/1.49      | sK1 != sK1 ),
% 6.90/1.49      inference(instantiation,[status(thm)],[c_675]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_789,plain,
% 6.90/1.49      ( ~ r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 6.90/1.49      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = X0
% 6.90/1.49      | k1_xboole_0 = X0 ),
% 6.90/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_791,plain,
% 6.90/1.49      ( ~ r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 6.90/1.49      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
% 6.90/1.49      | k1_xboole_0 = sK1 ),
% 6.90/1.49      inference(instantiation,[status(thm)],[c_789]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_928,plain,
% 6.90/1.49      ( r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
% 6.90/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_15496,plain,
% 6.90/1.49      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1 ),
% 6.90/1.49      inference(global_propositional_subsumption,
% 6.90/1.49                [status(thm)],
% 6.90/1.49                [c_15330,c_16,c_14,c_224,c_677,c_791,c_928]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_15500,plain,
% 6.90/1.49      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK1 ),
% 6.90/1.49      inference(demodulation,[status(thm)],[c_15496,c_16]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_9,plain,
% 6.90/1.49      ( r2_hidden(X0,X1)
% 6.90/1.49      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 6.90/1.49      inference(cnf_transformation,[],[f76]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_377,plain,
% 6.90/1.49      ( r2_hidden(X0,X1) = iProver_top
% 6.90/1.49      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 6.90/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_15506,plain,
% 6.90/1.49      ( r2_hidden(sK0,X0) = iProver_top
% 6.90/1.49      | r1_xboole_0(sK1,X0) = iProver_top ),
% 6.90/1.49      inference(superposition,[status(thm)],[c_15496,c_377]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_8,plain,
% 6.90/1.49      ( ~ r2_hidden(X0,X1)
% 6.90/1.49      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 6.90/1.49      inference(cnf_transformation,[],[f75]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_378,plain,
% 6.90/1.49      ( r2_hidden(X0,X1) != iProver_top
% 6.90/1.49      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 6.90/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_15505,plain,
% 6.90/1.49      ( r2_hidden(sK0,X0) != iProver_top
% 6.90/1.49      | r1_tarski(sK1,X0) = iProver_top ),
% 6.90/1.49      inference(superposition,[status(thm)],[c_15496,c_378]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_15772,plain,
% 6.90/1.49      ( r1_tarski(sK1,X0) = iProver_top
% 6.90/1.49      | r1_xboole_0(sK1,X0) = iProver_top ),
% 6.90/1.49      inference(superposition,[status(thm)],[c_15506,c_15505]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_4,plain,
% 6.90/1.49      ( ~ r1_tarski(X0,X1)
% 6.90/1.49      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 6.90/1.49      inference(cnf_transformation,[],[f73]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_380,plain,
% 6.90/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
% 6.90/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 6.90/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_19137,plain,
% 6.90/1.49      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = X0
% 6.90/1.49      | r1_xboole_0(sK1,X0) = iProver_top ),
% 6.90/1.49      inference(superposition,[status(thm)],[c_15772,c_380]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_1,plain,
% 6.90/1.49      ( ~ r1_xboole_0(X0,X1)
% 6.90/1.49      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
% 6.90/1.49      inference(cnf_transformation,[],[f70]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_6,plain,
% 6.90/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 6.90/1.49      inference(cnf_transformation,[],[f42]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_0,plain,
% 6.90/1.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 6.90/1.49      inference(cnf_transformation,[],[f36]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_210,plain,
% 6.90/1.49      ( ~ r1_xboole_0(X0,X1)
% 6.90/1.49      | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
% 6.90/1.49      inference(theory_normalisation,[status(thm)],[c_1,c_6,c_0]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_381,plain,
% 6.90/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0
% 6.90/1.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 6.90/1.49      inference(predicate_to_equality,[status(thm)],[c_210]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_19623,plain,
% 6.90/1.49      ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)))) = k1_xboole_0
% 6.90/1.49      | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = X0 ),
% 6.90/1.49      inference(superposition,[status(thm)],[c_19137,c_381]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_21329,plain,
% 6.90/1.49      ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k1_xboole_0
% 6.90/1.49      | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK2 ),
% 6.90/1.49      inference(superposition,[status(thm)],[c_15500,c_19623]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_7,plain,
% 6.90/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 6.90/1.49      inference(cnf_transformation,[],[f43]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_743,plain,
% 6.90/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 6.90/1.49      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_740,plain,
% 6.90/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 6.90/1.49      inference(superposition,[status(thm)],[c_7,c_6]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_3,plain,
% 6.90/1.49      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
% 6.90/1.49      inference(cnf_transformation,[],[f72]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_209,plain,
% 6.90/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
% 6.90/1.49      inference(theory_normalisation,[status(thm)],[c_3,c_6,c_0]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_2,plain,
% 6.90/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 6.90/1.49      inference(cnf_transformation,[],[f71]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_400,plain,
% 6.90/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 6.90/1.49      inference(light_normalisation,[status(thm)],[c_209,c_2,c_7]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_577,plain,
% 6.90/1.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 6.90/1.49      inference(superposition,[status(thm)],[c_400,c_0]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_753,plain,
% 6.90/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 6.90/1.49      inference(demodulation,[status(thm)],[c_740,c_577]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_997,plain,
% 6.90/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 6.90/1.49      inference(superposition,[status(thm)],[c_743,c_753]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_1012,plain,
% 6.90/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 6.90/1.49      inference(demodulation,[status(thm)],[c_997,c_400]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_21824,plain,
% 6.90/1.49      ( sK1 = sK2 | sK2 = k1_xboole_0 ),
% 6.90/1.49      inference(demodulation,[status(thm)],[c_21329,c_1012,c_15500]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_496,plain,
% 6.90/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 6.90/1.49      inference(instantiation,[status(thm)],[c_212]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_213,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_452,plain,
% 6.90/1.49      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 6.90/1.49      inference(instantiation,[status(thm)],[c_213]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_495,plain,
% 6.90/1.49      ( sK2 != k1_xboole_0
% 6.90/1.49      | k1_xboole_0 = sK2
% 6.90/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 6.90/1.49      inference(instantiation,[status(thm)],[c_452]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_13,negated_conjecture,
% 6.90/1.49      ( k1_xboole_0 != sK2 ),
% 6.90/1.49      inference(cnf_transformation,[],[f61]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(c_15,negated_conjecture,
% 6.90/1.49      ( sK1 != sK2 ),
% 6.90/1.49      inference(cnf_transformation,[],[f59]) ).
% 6.90/1.49  
% 6.90/1.49  cnf(contradiction,plain,
% 6.90/1.49      ( $false ),
% 6.90/1.49      inference(minisat,[status(thm)],[c_21824,c_496,c_495,c_13,c_15]) ).
% 6.90/1.49  
% 6.90/1.49  
% 6.90/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 6.90/1.49  
% 6.90/1.49  ------                               Statistics
% 6.90/1.49  
% 6.90/1.49  ------ General
% 6.90/1.49  
% 6.90/1.49  abstr_ref_over_cycles:                  0
% 6.90/1.49  abstr_ref_under_cycles:                 0
% 6.90/1.49  gc_basic_clause_elim:                   0
% 6.90/1.49  forced_gc_time:                         0
% 6.90/1.49  parsing_time:                           0.009
% 6.90/1.49  unif_index_cands_time:                  0.
% 6.90/1.49  unif_index_add_time:                    0.
% 6.90/1.49  orderings_time:                         0.
% 6.90/1.49  out_proof_time:                         0.008
% 6.90/1.49  total_time:                             0.621
% 6.90/1.49  num_of_symbols:                         41
% 6.90/1.49  num_of_terms:                           20523
% 6.90/1.49  
% 6.90/1.49  ------ Preprocessing
% 6.90/1.49  
% 6.90/1.49  num_of_splits:                          0
% 6.90/1.49  num_of_split_atoms:                     0
% 6.90/1.49  num_of_reused_defs:                     0
% 6.90/1.49  num_eq_ax_congr_red:                    6
% 6.90/1.49  num_of_sem_filtered_clauses:            1
% 6.90/1.49  num_of_subtypes:                        0
% 6.90/1.49  monotx_restored_types:                  0
% 6.90/1.49  sat_num_of_epr_types:                   0
% 6.90/1.49  sat_num_of_non_cyclic_types:            0
% 6.90/1.49  sat_guarded_non_collapsed_types:        0
% 6.90/1.49  num_pure_diseq_elim:                    0
% 6.90/1.49  simp_replaced_by:                       0
% 6.90/1.49  res_preprocessed:                       66
% 6.90/1.49  prep_upred:                             0
% 6.90/1.49  prep_unflattend:                        15
% 6.90/1.49  smt_new_axioms:                         0
% 6.90/1.49  pred_elim_cands:                        3
% 6.90/1.49  pred_elim:                              0
% 6.90/1.49  pred_elim_cl:                           0
% 6.90/1.49  pred_elim_cycles:                       3
% 6.90/1.49  merged_defs:                            0
% 6.90/1.49  merged_defs_ncl:                        0
% 6.90/1.49  bin_hyper_res:                          0
% 6.90/1.49  prep_cycles:                            3
% 6.90/1.49  pred_elim_time:                         0.001
% 6.90/1.49  splitting_time:                         0.
% 6.90/1.49  sem_filter_time:                        0.
% 6.90/1.49  monotx_time:                            0.
% 6.90/1.49  subtype_inf_time:                       0.
% 6.90/1.49  
% 6.90/1.49  ------ Problem properties
% 6.90/1.49  
% 6.90/1.49  clauses:                                17
% 6.90/1.49  conjectures:                            4
% 6.90/1.49  epr:                                    3
% 6.90/1.49  horn:                                   15
% 6.90/1.49  ground:                                 4
% 6.90/1.49  unary:                                  12
% 6.90/1.49  binary:                                 4
% 6.90/1.49  lits:                                   23
% 6.90/1.49  lits_eq:                                13
% 6.90/1.49  fd_pure:                                0
% 6.90/1.49  fd_pseudo:                              0
% 6.90/1.49  fd_cond:                                0
% 6.90/1.49  fd_pseudo_cond:                         1
% 6.90/1.49  ac_symbols:                             1
% 6.90/1.49  
% 6.90/1.49  ------ Propositional Solver
% 6.90/1.49  
% 6.90/1.49  prop_solver_calls:                      25
% 6.90/1.49  prop_fast_solver_calls:                 381
% 6.90/1.49  smt_solver_calls:                       0
% 6.90/1.49  smt_fast_solver_calls:                  0
% 6.90/1.49  prop_num_of_clauses:                    4080
% 6.90/1.49  prop_preprocess_simplified:             7741
% 6.90/1.49  prop_fo_subsumed:                       2
% 6.90/1.49  prop_solver_time:                       0.
% 6.90/1.49  smt_solver_time:                        0.
% 6.90/1.49  smt_fast_solver_time:                   0.
% 6.90/1.49  prop_fast_solver_time:                  0.
% 6.90/1.49  prop_unsat_core_time:                   0.
% 6.90/1.49  
% 6.90/1.49  ------ QBF
% 6.90/1.49  
% 6.90/1.49  qbf_q_res:                              0
% 6.90/1.49  qbf_num_tautologies:                    0
% 6.90/1.49  qbf_prep_cycles:                        0
% 6.90/1.49  
% 6.90/1.49  ------ BMC1
% 6.90/1.49  
% 6.90/1.49  bmc1_current_bound:                     -1
% 6.90/1.49  bmc1_last_solved_bound:                 -1
% 6.90/1.49  bmc1_unsat_core_size:                   -1
% 6.90/1.49  bmc1_unsat_core_parents_size:           -1
% 6.90/1.49  bmc1_merge_next_fun:                    0
% 6.90/1.49  bmc1_unsat_core_clauses_time:           0.
% 6.90/1.49  
% 6.90/1.49  ------ Instantiation
% 6.90/1.49  
% 6.90/1.49  inst_num_of_clauses:                    1029
% 6.90/1.49  inst_num_in_passive:                    467
% 6.90/1.49  inst_num_in_active:                     392
% 6.90/1.49  inst_num_in_unprocessed:                170
% 6.90/1.49  inst_num_of_loops:                      430
% 6.90/1.49  inst_num_of_learning_restarts:          0
% 6.90/1.49  inst_num_moves_active_passive:          35
% 6.90/1.49  inst_lit_activity:                      0
% 6.90/1.49  inst_lit_activity_moves:                0
% 6.90/1.49  inst_num_tautologies:                   0
% 6.90/1.49  inst_num_prop_implied:                  0
% 6.90/1.49  inst_num_existing_simplified:           0
% 6.90/1.49  inst_num_eq_res_simplified:             0
% 6.90/1.49  inst_num_child_elim:                    0
% 6.90/1.49  inst_num_of_dismatching_blockings:      606
% 6.90/1.49  inst_num_of_non_proper_insts:           1096
% 6.90/1.49  inst_num_of_duplicates:                 0
% 6.90/1.49  inst_inst_num_from_inst_to_res:         0
% 6.90/1.49  inst_dismatching_checking_time:         0.
% 6.90/1.49  
% 6.90/1.49  ------ Resolution
% 6.90/1.49  
% 6.90/1.49  res_num_of_clauses:                     0
% 6.90/1.49  res_num_in_passive:                     0
% 6.90/1.49  res_num_in_active:                      0
% 6.90/1.49  res_num_of_loops:                       69
% 6.90/1.49  res_forward_subset_subsumed:            126
% 6.90/1.49  res_backward_subset_subsumed:           2
% 6.90/1.49  res_forward_subsumed:                   1
% 6.90/1.49  res_backward_subsumed:                  0
% 6.90/1.49  res_forward_subsumption_resolution:     0
% 6.90/1.49  res_backward_subsumption_resolution:    0
% 6.90/1.49  res_clause_to_clause_subsumption:       44910
% 6.90/1.49  res_orphan_elimination:                 0
% 6.90/1.49  res_tautology_del:                      95
% 6.90/1.49  res_num_eq_res_simplified:              0
% 6.90/1.49  res_num_sel_changes:                    0
% 6.90/1.49  res_moves_from_active_to_pass:          0
% 6.90/1.49  
% 6.90/1.49  ------ Superposition
% 6.90/1.49  
% 6.90/1.49  sup_time_total:                         0.
% 6.90/1.49  sup_time_generating:                    0.
% 6.90/1.49  sup_time_sim_full:                      0.
% 6.90/1.49  sup_time_sim_immed:                     0.
% 6.90/1.49  
% 6.90/1.49  sup_num_of_clauses:                     1278
% 6.90/1.49  sup_num_in_active:                      80
% 6.90/1.49  sup_num_in_passive:                     1198
% 6.90/1.49  sup_num_of_loops:                       85
% 6.90/1.49  sup_fw_superposition:                   4832
% 6.90/1.49  sup_bw_superposition:                   3369
% 6.90/1.49  sup_immediate_simplified:               2371
% 6.90/1.49  sup_given_eliminated:                   0
% 6.90/1.49  comparisons_done:                       0
% 6.90/1.49  comparisons_avoided:                    3
% 6.90/1.49  
% 6.90/1.49  ------ Simplifications
% 6.90/1.49  
% 6.90/1.49  
% 6.90/1.49  sim_fw_subset_subsumed:                 2
% 6.90/1.49  sim_bw_subset_subsumed:                 0
% 6.90/1.49  sim_fw_subsumed:                        132
% 6.90/1.49  sim_bw_subsumed:                        1
% 6.90/1.49  sim_fw_subsumption_res:                 0
% 6.90/1.49  sim_bw_subsumption_res:                 0
% 6.90/1.49  sim_tautology_del:                      0
% 6.90/1.49  sim_eq_tautology_del:                   392
% 6.90/1.49  sim_eq_res_simp:                        0
% 6.90/1.49  sim_fw_demodulated:                     1272
% 6.90/1.49  sim_bw_demodulated:                     88
% 6.90/1.49  sim_light_normalised:                   931
% 6.90/1.49  sim_joinable_taut:                      193
% 6.90/1.49  sim_joinable_simp:                      0
% 6.90/1.49  sim_ac_normalised:                      0
% 6.90/1.49  sim_smt_subsumption:                    0
% 6.90/1.49  
%------------------------------------------------------------------------------
