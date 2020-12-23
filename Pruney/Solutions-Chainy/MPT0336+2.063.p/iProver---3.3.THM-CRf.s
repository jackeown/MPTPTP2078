%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:43 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 313 expanded)
%              Number of clauses        :   43 (  77 expanded)
%              Number of leaves         :   15 (  78 expanded)
%              Depth                    :   19
%              Number of atoms          :  211 ( 646 expanded)
%              Number of equality atoms :   90 ( 285 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f18])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
      & r1_xboole_0(sK3,sK2)
      & r2_hidden(sK4,sK3)
      & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    & r1_xboole_0(sK3,sK2)
    & r2_hidden(sK4,sK3)
    & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f27])).

fof(f50,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f48,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f52])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f53])).

fof(f64,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f41,f55,f55])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f25])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f46,f53])).

fof(f49,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f21])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f54])).

fof(f51,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ~ r1_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK3)),sK2) ),
    inference(definition_unfolding,[],[f51,f54])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_980,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_993,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1363,plain,
    ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_980,c_993])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_994,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1365,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_994])).

cnf(c_1995,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_1365])).

cnf(c_2004,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1995,c_993])).

cnf(c_6,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_989,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK1,sK2),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_978,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_985,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1872,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_xboole_0(sK1,sK2)
    | k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_978,c_985])).

cnf(c_12,plain,
    ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
    | r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_983,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4103,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0
    | r1_tarski(k3_xboole_0(sK1,sK2),X0) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1872,c_983])).

cnf(c_5708,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0
    | r2_hidden(sK4,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_989,c_4103])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_505,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_506,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_507,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_509,plain,
    ( r2_hidden(sK4,sK2) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = k3_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_988,plain,
    ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = k3_xboole_0(X0,X2)
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2003,plain,
    ( k3_xboole_0(sK2,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X0))) = k3_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1995,c_988])).

cnf(c_2798,plain,
    ( r1_tarski(k3_xboole_0(sK2,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2003,c_989])).

cnf(c_2908,plain,
    ( r1_tarski(k3_xboole_0(X0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2798])).

cnf(c_5712,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0
    | r2_hidden(sK4,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2908,c_4103])).

cnf(c_5984,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5708,c_19,c_509,c_5712])).

cnf(c_5986,plain,
    ( r1_xboole_0(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5984,c_1365])).

cnf(c_6140,plain,
    ( k3_xboole_0(sK2,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0))) = k3_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_5986,c_988])).

cnf(c_7382,plain,
    ( k3_xboole_0(sK2,X0) != k1_xboole_0
    | r1_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6140,c_1365])).

cnf(c_8615,plain,
    ( r1_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK3)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2004,c_7382])).

cnf(c_14,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK3)),sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,plain,
    ( r1_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK3)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8615,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.69/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.01  
% 3.69/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.69/1.01  
% 3.69/1.01  ------  iProver source info
% 3.69/1.01  
% 3.69/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.69/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.69/1.01  git: non_committed_changes: false
% 3.69/1.01  git: last_make_outside_of_git: false
% 3.69/1.01  
% 3.69/1.01  ------ 
% 3.69/1.01  ------ Parsing...
% 3.69/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.69/1.01  
% 3.69/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.69/1.01  
% 3.69/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.69/1.01  
% 3.69/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/1.01  ------ Proving...
% 3.69/1.01  ------ Problem Properties 
% 3.69/1.01  
% 3.69/1.01  
% 3.69/1.01  clauses                                 18
% 3.69/1.01  conjectures                             4
% 3.69/1.01  EPR                                     3
% 3.69/1.01  Horn                                    15
% 3.69/1.01  unary                                   8
% 3.69/1.01  binary                                  7
% 3.69/1.01  lits                                    31
% 3.69/1.01  lits eq                                 6
% 3.69/1.01  fd_pure                                 0
% 3.69/1.01  fd_pseudo                               0
% 3.69/1.01  fd_cond                                 0
% 3.69/1.01  fd_pseudo_cond                          1
% 3.69/1.01  AC symbols                              0
% 3.69/1.01  
% 3.69/1.01  ------ Input Options Time Limit: Unbounded
% 3.69/1.01  
% 3.69/1.01  
% 3.69/1.01  ------ 
% 3.69/1.01  Current options:
% 3.69/1.01  ------ 
% 3.69/1.01  
% 3.69/1.01  
% 3.69/1.01  
% 3.69/1.01  
% 3.69/1.01  ------ Proving...
% 3.69/1.01  
% 3.69/1.01  
% 3.69/1.01  % SZS status Theorem for theBenchmark.p
% 3.69/1.01  
% 3.69/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.69/1.01  
% 3.69/1.01  fof(f13,conjecture,(
% 3.69/1.01    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.69/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.01  
% 3.69/1.01  fof(f14,negated_conjecture,(
% 3.69/1.01    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.69/1.01    inference(negated_conjecture,[],[f13])).
% 3.69/1.01  
% 3.69/1.01  fof(f18,plain,(
% 3.69/1.01    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 3.69/1.01    inference(ennf_transformation,[],[f14])).
% 3.69/1.01  
% 3.69/1.01  fof(f19,plain,(
% 3.69/1.01    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 3.69/1.01    inference(flattening,[],[f18])).
% 3.69/1.01  
% 3.69/1.01  fof(f27,plain,(
% 3.69/1.01    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)))),
% 3.69/1.01    introduced(choice_axiom,[])).
% 3.69/1.01  
% 3.69/1.01  fof(f28,plain,(
% 3.69/1.01    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 3.69/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f27])).
% 3.69/1.01  
% 3.69/1.01  fof(f50,plain,(
% 3.69/1.01    r1_xboole_0(sK3,sK2)),
% 3.69/1.01    inference(cnf_transformation,[],[f28])).
% 3.69/1.01  
% 3.69/1.01  fof(f2,axiom,(
% 3.69/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.69/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.01  
% 3.69/1.01  fof(f20,plain,(
% 3.69/1.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.69/1.01    inference(nnf_transformation,[],[f2])).
% 3.69/1.01  
% 3.69/1.01  fof(f30,plain,(
% 3.69/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.69/1.01    inference(cnf_transformation,[],[f20])).
% 3.69/1.01  
% 3.69/1.01  fof(f1,axiom,(
% 3.69/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.69/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.01  
% 3.69/1.01  fof(f29,plain,(
% 3.69/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.69/1.01    inference(cnf_transformation,[],[f1])).
% 3.69/1.01  
% 3.69/1.01  fof(f31,plain,(
% 3.69/1.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.69/1.01    inference(cnf_transformation,[],[f20])).
% 3.69/1.01  
% 3.69/1.01  fof(f4,axiom,(
% 3.69/1.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.69/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.01  
% 3.69/1.01  fof(f35,plain,(
% 3.69/1.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.69/1.01    inference(cnf_transformation,[],[f4])).
% 3.69/1.01  
% 3.69/1.01  fof(f48,plain,(
% 3.69/1.01    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 3.69/1.01    inference(cnf_transformation,[],[f28])).
% 3.69/1.01  
% 3.69/1.01  fof(f6,axiom,(
% 3.69/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.69/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.01  
% 3.69/1.01  fof(f37,plain,(
% 3.69/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.69/1.01    inference(cnf_transformation,[],[f6])).
% 3.69/1.01  
% 3.69/1.01  fof(f7,axiom,(
% 3.69/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.69/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.01  
% 3.69/1.01  fof(f38,plain,(
% 3.69/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.69/1.01    inference(cnf_transformation,[],[f7])).
% 3.69/1.01  
% 3.69/1.01  fof(f8,axiom,(
% 3.69/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.69/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.01  
% 3.69/1.01  fof(f39,plain,(
% 3.69/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.69/1.01    inference(cnf_transformation,[],[f8])).
% 3.69/1.01  
% 3.69/1.01  fof(f9,axiom,(
% 3.69/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.69/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.01  
% 3.69/1.01  fof(f40,plain,(
% 3.69/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.69/1.01    inference(cnf_transformation,[],[f9])).
% 3.69/1.01  
% 3.69/1.01  fof(f52,plain,(
% 3.69/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.69/1.01    inference(definition_unfolding,[],[f39,f40])).
% 3.69/1.01  
% 3.69/1.01  fof(f53,plain,(
% 3.69/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.69/1.01    inference(definition_unfolding,[],[f38,f52])).
% 3.69/1.01  
% 3.69/1.01  fof(f55,plain,(
% 3.69/1.01    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.69/1.01    inference(definition_unfolding,[],[f37,f53])).
% 3.69/1.01  
% 3.69/1.01  fof(f64,plain,(
% 3.69/1.01    r1_tarski(k3_xboole_0(sK1,sK2),k3_enumset1(sK4,sK4,sK4,sK4,sK4))),
% 3.69/1.01    inference(definition_unfolding,[],[f48,f55])).
% 3.69/1.01  
% 3.69/1.01  fof(f10,axiom,(
% 3.69/1.01    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.69/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.01  
% 3.69/1.01  fof(f23,plain,(
% 3.69/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.69/1.01    inference(nnf_transformation,[],[f10])).
% 3.69/1.01  
% 3.69/1.01  fof(f24,plain,(
% 3.69/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.69/1.01    inference(flattening,[],[f23])).
% 3.69/1.01  
% 3.69/1.01  fof(f41,plain,(
% 3.69/1.01    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.69/1.01    inference(cnf_transformation,[],[f24])).
% 3.69/1.01  
% 3.69/1.01  fof(f59,plain,(
% 3.69/1.01    ( ! [X0,X1] : (k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))) )),
% 3.69/1.01    inference(definition_unfolding,[],[f41,f55,f55])).
% 3.69/1.01  
% 3.69/1.01  fof(f12,axiom,(
% 3.69/1.01    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.69/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.01  
% 3.69/1.01  fof(f25,plain,(
% 3.69/1.01    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.69/1.01    inference(nnf_transformation,[],[f12])).
% 3.69/1.01  
% 3.69/1.01  fof(f26,plain,(
% 3.69/1.01    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.69/1.01    inference(flattening,[],[f25])).
% 3.69/1.01  
% 3.69/1.01  fof(f46,plain,(
% 3.69/1.01    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.69/1.01    inference(cnf_transformation,[],[f26])).
% 3.69/1.01  
% 3.69/1.01  fof(f61,plain,(
% 3.69/1.01    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)) )),
% 3.69/1.01    inference(definition_unfolding,[],[f46,f53])).
% 3.69/1.01  
% 3.69/1.01  fof(f49,plain,(
% 3.69/1.01    r2_hidden(sK4,sK3)),
% 3.69/1.01    inference(cnf_transformation,[],[f28])).
% 3.69/1.01  
% 3.69/1.01  fof(f3,axiom,(
% 3.69/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.69/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.01  
% 3.69/1.01  fof(f15,plain,(
% 3.69/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.69/1.01    inference(rectify,[],[f3])).
% 3.69/1.01  
% 3.69/1.01  fof(f16,plain,(
% 3.69/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.69/1.01    inference(ennf_transformation,[],[f15])).
% 3.69/1.01  
% 3.69/1.01  fof(f21,plain,(
% 3.69/1.01    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.69/1.01    introduced(choice_axiom,[])).
% 3.69/1.01  
% 3.69/1.01  fof(f22,plain,(
% 3.69/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.69/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f21])).
% 3.69/1.01  
% 3.69/1.01  fof(f34,plain,(
% 3.69/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.69/1.01    inference(cnf_transformation,[],[f22])).
% 3.69/1.01  
% 3.69/1.01  fof(f5,axiom,(
% 3.69/1.01    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 3.69/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.01  
% 3.69/1.01  fof(f17,plain,(
% 3.69/1.01    ! [X0,X1,X2] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 3.69/1.01    inference(ennf_transformation,[],[f5])).
% 3.69/1.01  
% 3.69/1.01  fof(f36,plain,(
% 3.69/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 3.69/1.01    inference(cnf_transformation,[],[f17])).
% 3.69/1.01  
% 3.69/1.01  fof(f11,axiom,(
% 3.69/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.69/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.69/1.01  
% 3.69/1.01  fof(f44,plain,(
% 3.69/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.69/1.01    inference(cnf_transformation,[],[f11])).
% 3.69/1.01  
% 3.69/1.01  fof(f54,plain,(
% 3.69/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.69/1.01    inference(definition_unfolding,[],[f44,f53])).
% 3.69/1.01  
% 3.69/1.01  fof(f56,plain,(
% 3.69/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) | ~r1_xboole_0(X0,X1)) )),
% 3.69/1.01    inference(definition_unfolding,[],[f36,f54])).
% 3.69/1.01  
% 3.69/1.01  fof(f51,plain,(
% 3.69/1.01    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)),
% 3.69/1.01    inference(cnf_transformation,[],[f28])).
% 3.69/1.01  
% 3.69/1.01  fof(f63,plain,(
% 3.69/1.01    ~r1_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK3)),sK2)),
% 3.69/1.01    inference(definition_unfolding,[],[f51,f54])).
% 3.69/1.01  
% 3.69/1.01  cnf(c_15,negated_conjecture,
% 3.69/1.01      ( r1_xboole_0(sK3,sK2) ),
% 3.69/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_980,plain,
% 3.69/1.01      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 3.69/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_2,plain,
% 3.69/1.01      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.69/1.01      inference(cnf_transformation,[],[f30]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_993,plain,
% 3.69/1.01      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 3.69/1.01      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.69/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_1363,plain,
% 3.69/1.01      ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
% 3.69/1.01      inference(superposition,[status(thm)],[c_980,c_993]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_0,plain,
% 3.69/1.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.69/1.01      inference(cnf_transformation,[],[f29]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_1,plain,
% 3.69/1.01      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.69/1.01      inference(cnf_transformation,[],[f31]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_994,plain,
% 3.69/1.01      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 3.69/1.01      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.69/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_1365,plain,
% 3.69/1.01      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 3.69/1.01      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.69/1.01      inference(superposition,[status(thm)],[c_0,c_994]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_1995,plain,
% 3.69/1.01      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 3.69/1.01      inference(superposition,[status(thm)],[c_1363,c_1365]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_2004,plain,
% 3.69/1.01      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 3.69/1.01      inference(superposition,[status(thm)],[c_1995,c_993]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_6,plain,
% 3.69/1.01      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 3.69/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_989,plain,
% 3.69/1.01      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 3.69/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_17,negated_conjecture,
% 3.69/1.01      ( r1_tarski(k3_xboole_0(sK1,sK2),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 3.69/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_978,plain,
% 3.69/1.01      ( r1_tarski(k3_xboole_0(sK1,sK2),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 3.69/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_10,plain,
% 3.69/1.01      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
% 3.69/1.01      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 3.69/1.01      | k1_xboole_0 = X0 ),
% 3.69/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_985,plain,
% 3.69/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 3.69/1.01      | k1_xboole_0 = X1
% 3.69/1.01      | r1_tarski(X1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 3.69/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_1872,plain,
% 3.69/1.01      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_xboole_0(sK1,sK2)
% 3.69/1.01      | k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 3.69/1.01      inference(superposition,[status(thm)],[c_978,c_985]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_12,plain,
% 3.69/1.01      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2) ),
% 3.69/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_983,plain,
% 3.69/1.01      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) != iProver_top
% 3.69/1.01      | r2_hidden(X1,X2) = iProver_top ),
% 3.69/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_4103,plain,
% 3.69/1.01      ( k3_xboole_0(sK1,sK2) = k1_xboole_0
% 3.69/1.01      | r1_tarski(k3_xboole_0(sK1,sK2),X0) != iProver_top
% 3.69/1.01      | r2_hidden(sK4,X0) = iProver_top ),
% 3.69/1.01      inference(superposition,[status(thm)],[c_1872,c_983]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_5708,plain,
% 3.69/1.01      ( k3_xboole_0(sK1,sK2) = k1_xboole_0
% 3.69/1.01      | r2_hidden(sK4,sK1) = iProver_top ),
% 3.69/1.01      inference(superposition,[status(thm)],[c_989,c_4103]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_16,negated_conjecture,
% 3.69/1.01      ( r2_hidden(sK4,sK3) ),
% 3.69/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_19,plain,
% 3.69/1.01      ( r2_hidden(sK4,sK3) = iProver_top ),
% 3.69/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_3,plain,
% 3.69/1.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.69/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_505,plain,
% 3.69/1.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | sK2 != X1 | sK3 != X2 ),
% 3.69/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_15]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_506,plain,
% 3.69/1.01      ( ~ r2_hidden(X0,sK2) | ~ r2_hidden(X0,sK3) ),
% 3.69/1.01      inference(unflattening,[status(thm)],[c_505]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_507,plain,
% 3.69/1.01      ( r2_hidden(X0,sK2) != iProver_top
% 3.69/1.01      | r2_hidden(X0,sK3) != iProver_top ),
% 3.69/1.01      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_509,plain,
% 3.69/1.01      ( r2_hidden(sK4,sK2) != iProver_top
% 3.69/1.01      | r2_hidden(sK4,sK3) != iProver_top ),
% 3.69/1.01      inference(instantiation,[status(thm)],[c_507]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_7,plain,
% 3.69/1.01      ( ~ r1_xboole_0(X0,X1)
% 3.69/1.01      | k3_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = k3_xboole_0(X0,X2) ),
% 3.69/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_988,plain,
% 3.69/1.01      ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = k3_xboole_0(X0,X2)
% 3.69/1.01      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.69/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_2003,plain,
% 3.69/1.01      ( k3_xboole_0(sK2,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X0))) = k3_xboole_0(sK2,X0) ),
% 3.69/1.01      inference(superposition,[status(thm)],[c_1995,c_988]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_2798,plain,
% 3.69/1.01      ( r1_tarski(k3_xboole_0(sK2,X0),sK2) = iProver_top ),
% 3.69/1.01      inference(superposition,[status(thm)],[c_2003,c_989]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_2908,plain,
% 3.69/1.01      ( r1_tarski(k3_xboole_0(X0,sK2),sK2) = iProver_top ),
% 3.69/1.01      inference(superposition,[status(thm)],[c_0,c_2798]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_5712,plain,
% 3.69/1.01      ( k3_xboole_0(sK1,sK2) = k1_xboole_0
% 3.69/1.01      | r2_hidden(sK4,sK2) = iProver_top ),
% 3.69/1.01      inference(superposition,[status(thm)],[c_2908,c_4103]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_5984,plain,
% 3.69/1.01      ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 3.69/1.01      inference(global_propositional_subsumption,
% 3.69/1.01                [status(thm)],
% 3.69/1.01                [c_5708,c_19,c_509,c_5712]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_5986,plain,
% 3.69/1.01      ( r1_xboole_0(sK2,sK1) = iProver_top ),
% 3.69/1.01      inference(superposition,[status(thm)],[c_5984,c_1365]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_6140,plain,
% 3.69/1.01      ( k3_xboole_0(sK2,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0))) = k3_xboole_0(sK2,X0) ),
% 3.69/1.01      inference(superposition,[status(thm)],[c_5986,c_988]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_7382,plain,
% 3.69/1.01      ( k3_xboole_0(sK2,X0) != k1_xboole_0
% 3.69/1.01      | r1_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0)),sK2) = iProver_top ),
% 3.69/1.01      inference(superposition,[status(thm)],[c_6140,c_1365]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_8615,plain,
% 3.69/1.01      ( r1_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK3)),sK2) = iProver_top ),
% 3.69/1.01      inference(superposition,[status(thm)],[c_2004,c_7382]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_14,negated_conjecture,
% 3.69/1.01      ( ~ r1_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK3)),sK2) ),
% 3.69/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(c_21,plain,
% 3.69/1.01      ( r1_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK3)),sK2) != iProver_top ),
% 3.69/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.69/1.01  
% 3.69/1.01  cnf(contradiction,plain,
% 3.69/1.01      ( $false ),
% 3.69/1.01      inference(minisat,[status(thm)],[c_8615,c_21]) ).
% 3.69/1.01  
% 3.69/1.01  
% 3.69/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.69/1.01  
% 3.69/1.01  ------                               Statistics
% 3.69/1.01  
% 3.69/1.01  ------ Selected
% 3.69/1.01  
% 3.69/1.01  total_time:                             0.315
% 3.69/1.01  
%------------------------------------------------------------------------------
