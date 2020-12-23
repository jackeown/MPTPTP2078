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
% DateTime   : Thu Dec  3 11:38:44 EST 2020

% Result     : Theorem 7.32s
% Output     : CNFRefutation 7.32s
% Verified   : 
% Statistics : Number of formulae       :  172 (11655 expanded)
%              Number of clauses        :  112 (4165 expanded)
%              Number of leaves         :   18 (2590 expanded)
%              Depth                    :   30
%              Number of atoms          :  287 (25589 expanded)
%              Number of equality atoms :  149 (8303 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f26])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
      & r1_xboole_0(sK4,sK3)
      & r2_hidden(sK5,sK4)
      & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f35])).

fof(f61,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f65])).

fof(f76,plain,(
    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f61,f48,f66])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f73,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f47,f48,f48,f48,f48])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f60,f66])).

fof(f62,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f29])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f48,f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f63,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_297,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | k2_enumset1(sK5,sK5,sK5,sK5) != X2
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_298,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_956,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_16,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_962,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2042,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_956,c_962])).

cnf(c_10,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3165,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5)))))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_2042,c_10])).

cnf(c_14,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_964,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_961,plain,
    ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_957,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_972,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5423,plain,
    ( r2_hidden(sK5,X0) != iProver_top
    | r1_xboole_0(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_957,c_972])).

cnf(c_5966,plain,
    ( k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5)) = X0
    | r1_xboole_0(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_961,c_5423])).

cnf(c_6086,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK4),k2_enumset1(sK5,sK5,sK5,sK5)) = k4_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_964,c_5966])).

cnf(c_7488,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_6086,c_2042])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_9732,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_7488,c_1])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_973,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2239,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_956,c_973])).

cnf(c_7489,plain,
    ( r1_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6086,c_2239])).

cnf(c_7832,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = k4_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_7489,c_962])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_974,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7830,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7489,c_974])).

cnf(c_7833,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,sK4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7830,c_7832])).

cnf(c_9744,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_7488,c_10])).

cnf(c_21,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_958,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2238,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_958,c_973])).

cnf(c_2440,plain,
    ( k4_xboole_0(sK3,sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_2238,c_962])).

cnf(c_1665,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_964])).

cnf(c_2449,plain,
    ( r1_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2440,c_1665])).

cnf(c_2041,plain,
    ( k4_xboole_0(sK4,sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_958,c_962])).

cnf(c_2452,plain,
    ( r1_xboole_0(k4_xboole_0(sK4,sK4),sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2449,c_2041])).

cnf(c_2661,plain,
    ( r1_xboole_0(sK3,k4_xboole_0(sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2452,c_973])).

cnf(c_3987,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK4,sK4))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2661,c_974])).

cnf(c_2450,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_2440,c_1])).

cnf(c_2451,plain,
    ( k4_xboole_0(sK3,sK3) = k4_xboole_0(sK4,sK4) ),
    inference(light_normalisation,[status(thm)],[c_2450,c_2041])).

cnf(c_3426,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK4,sK4)) = sK3 ),
    inference(superposition,[status(thm)],[c_2661,c_962])).

cnf(c_3988,plain,
    ( k4_xboole_0(sK4,sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3987,c_2451,c_3426])).

cnf(c_4290,plain,
    ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3988,c_2451])).

cnf(c_9745,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_9744,c_2440,c_4290])).

cnf(c_9902,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)),k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9732,c_7832,c_7833,c_9745])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_10011,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0))) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_9745,c_0])).

cnf(c_10028,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_10011,c_0])).

cnf(c_16618,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5)))))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3165,c_3165,c_9902,c_10028])).

cnf(c_16660,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))))) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_16618,c_0])).

cnf(c_2252,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(k4_xboole_0(sK4,sK4),k4_xboole_0(k4_xboole_0(sK4,sK4),X0)) ),
    inference(superposition,[status(thm)],[c_2041,c_10])).

cnf(c_3349,plain,
    ( k5_xboole_0(k4_xboole_0(sK4,sK4),k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))))) = k4_xboole_0(k4_xboole_0(sK4,sK4),X0) ),
    inference(superposition,[status(thm)],[c_2252,c_0])).

cnf(c_2662,plain,
    ( k4_xboole_0(k4_xboole_0(sK4,sK4),sK3) = k4_xboole_0(sK4,sK4) ),
    inference(superposition,[status(thm)],[c_2452,c_962])).

cnf(c_3437,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)))) = k4_xboole_0(k4_xboole_0(sK4,sK4),k4_xboole_0(sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_2662,c_2252])).

cnf(c_3438,plain,
    ( k4_xboole_0(k4_xboole_0(sK4,sK4),k4_xboole_0(sK4,sK4)) = k4_xboole_0(sK4,sK4) ),
    inference(light_normalisation,[status(thm)],[c_3437,c_2041,c_2451,c_3426])).

cnf(c_3737,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK4,sK4))))) = k4_xboole_0(k4_xboole_0(sK4,sK4),k4_xboole_0(sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_3438,c_2252])).

cnf(c_3738,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK4,sK4))))) = k4_xboole_0(sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_3737,c_3438])).

cnf(c_3739,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK4,sK4))) = k4_xboole_0(sK4,sK4) ),
    inference(light_normalisation,[status(thm)],[c_3738,c_2451,c_3426])).

cnf(c_5071,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3739,c_3739,c_3988])).

cnf(c_5089,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_5071,c_10])).

cnf(c_4288,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_3988,c_2252])).

cnf(c_5259,plain,
    ( k5_xboole_0(sK4,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) ),
    inference(superposition,[status(thm)],[c_4288,c_0])).

cnf(c_5457,plain,
    ( k5_xboole_0(sK4,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(sK4,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_5089,c_0])).

cnf(c_5718,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) ),
    inference(light_normalisation,[status(thm)],[c_5259,c_5457])).

cnf(c_13647,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_3349,c_3349,c_3988,c_5089,c_5718])).

cnf(c_4284,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3988,c_3438])).

cnf(c_1666,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_4323,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4284,c_1666])).

cnf(c_4326,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4323,c_4284])).

cnf(c_1889,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_1,c_10])).

cnf(c_10750,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)),X0))))) = k4_xboole_0(k4_xboole_0(sK4,sK4),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,sK4)))) ),
    inference(superposition,[status(thm)],[c_2041,c_1889])).

cnf(c_10994,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,X0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
    inference(light_normalisation,[status(thm)],[c_10750,c_2041,c_3988])).

cnf(c_10995,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(demodulation,[status(thm)],[c_10994,c_5089,c_5718])).

cnf(c_10759,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)),X0))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))) ),
    inference(superposition,[status(thm)],[c_4284,c_1889])).

cnf(c_1664,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_10872,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))))))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_1889,c_1664])).

cnf(c_2040,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_964,c_962])).

cnf(c_3980,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_964,c_974])).

cnf(c_3995,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3980,c_2040])).

cnf(c_4722,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_10,c_1664])).

cnf(c_10893,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_10872,c_2040,c_3995,c_4722])).

cnf(c_10894,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10893,c_3995,c_4284])).

cnf(c_10985,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10759,c_10894])).

cnf(c_10986,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10985,c_4284])).

cnf(c_11816,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10995,c_10986])).

cnf(c_11863,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11816,c_0])).

cnf(c_11932,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11863,c_4326])).

cnf(c_13648,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13647,c_0,c_4326,c_11932])).

cnf(c_13839,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_13648,c_1666])).

cnf(c_16698,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))))) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_16660,c_13839])).

cnf(c_16708,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16698,c_16618])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_975,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4001,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_975])).

cnf(c_10005,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k1_xboole_0
    | r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_9745,c_4001])).

cnf(c_1294,plain,
    ( r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1295,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top
    | r1_xboole_0(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1294])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1076,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
    | ~ r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1077,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = iProver_top
    | r1_xboole_0(sK3,sK4) != iProver_top
    | r1_xboole_0(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1076])).

cnf(c_1016,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1017,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) = iProver_top
    | r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_20,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_26,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16708,c_10005,c_1295,c_1077,c_1017,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:05:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.32/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.32/1.49  
% 7.32/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.32/1.49  
% 7.32/1.49  ------  iProver source info
% 7.32/1.49  
% 7.32/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.32/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.32/1.49  git: non_committed_changes: false
% 7.32/1.49  git: last_make_outside_of_git: false
% 7.32/1.49  
% 7.32/1.49  ------ 
% 7.32/1.49  
% 7.32/1.49  ------ Input Options
% 7.32/1.49  
% 7.32/1.49  --out_options                           all
% 7.32/1.49  --tptp_safe_out                         true
% 7.32/1.49  --problem_path                          ""
% 7.32/1.49  --include_path                          ""
% 7.32/1.49  --clausifier                            res/vclausify_rel
% 7.32/1.49  --clausifier_options                    ""
% 7.32/1.49  --stdin                                 false
% 7.32/1.49  --stats_out                             all
% 7.32/1.49  
% 7.32/1.49  ------ General Options
% 7.32/1.49  
% 7.32/1.49  --fof                                   false
% 7.32/1.49  --time_out_real                         305.
% 7.32/1.49  --time_out_virtual                      -1.
% 7.32/1.49  --symbol_type_check                     false
% 7.32/1.49  --clausify_out                          false
% 7.32/1.49  --sig_cnt_out                           false
% 7.32/1.49  --trig_cnt_out                          false
% 7.32/1.49  --trig_cnt_out_tolerance                1.
% 7.32/1.49  --trig_cnt_out_sk_spl                   false
% 7.32/1.49  --abstr_cl_out                          false
% 7.32/1.49  
% 7.32/1.49  ------ Global Options
% 7.32/1.49  
% 7.32/1.49  --schedule                              default
% 7.32/1.49  --add_important_lit                     false
% 7.32/1.49  --prop_solver_per_cl                    1000
% 7.32/1.49  --min_unsat_core                        false
% 7.32/1.49  --soft_assumptions                      false
% 7.32/1.49  --soft_lemma_size                       3
% 7.32/1.49  --prop_impl_unit_size                   0
% 7.32/1.49  --prop_impl_unit                        []
% 7.32/1.49  --share_sel_clauses                     true
% 7.32/1.49  --reset_solvers                         false
% 7.32/1.49  --bc_imp_inh                            [conj_cone]
% 7.32/1.49  --conj_cone_tolerance                   3.
% 7.32/1.49  --extra_neg_conj                        none
% 7.32/1.49  --large_theory_mode                     true
% 7.32/1.49  --prolific_symb_bound                   200
% 7.32/1.49  --lt_threshold                          2000
% 7.32/1.49  --clause_weak_htbl                      true
% 7.32/1.49  --gc_record_bc_elim                     false
% 7.32/1.49  
% 7.32/1.49  ------ Preprocessing Options
% 7.32/1.49  
% 7.32/1.49  --preprocessing_flag                    true
% 7.32/1.49  --time_out_prep_mult                    0.1
% 7.32/1.49  --splitting_mode                        input
% 7.32/1.49  --splitting_grd                         true
% 7.32/1.49  --splitting_cvd                         false
% 7.32/1.49  --splitting_cvd_svl                     false
% 7.32/1.49  --splitting_nvd                         32
% 7.32/1.49  --sub_typing                            true
% 7.32/1.49  --prep_gs_sim                           true
% 7.32/1.49  --prep_unflatten                        true
% 7.32/1.49  --prep_res_sim                          true
% 7.32/1.49  --prep_upred                            true
% 7.32/1.49  --prep_sem_filter                       exhaustive
% 7.32/1.49  --prep_sem_filter_out                   false
% 7.32/1.49  --pred_elim                             true
% 7.32/1.49  --res_sim_input                         true
% 7.32/1.49  --eq_ax_congr_red                       true
% 7.32/1.49  --pure_diseq_elim                       true
% 7.32/1.49  --brand_transform                       false
% 7.32/1.49  --non_eq_to_eq                          false
% 7.32/1.49  --prep_def_merge                        true
% 7.32/1.49  --prep_def_merge_prop_impl              false
% 7.32/1.49  --prep_def_merge_mbd                    true
% 7.32/1.49  --prep_def_merge_tr_red                 false
% 7.32/1.49  --prep_def_merge_tr_cl                  false
% 7.32/1.49  --smt_preprocessing                     true
% 7.32/1.49  --smt_ac_axioms                         fast
% 7.32/1.49  --preprocessed_out                      false
% 7.32/1.49  --preprocessed_stats                    false
% 7.32/1.49  
% 7.32/1.49  ------ Abstraction refinement Options
% 7.32/1.49  
% 7.32/1.49  --abstr_ref                             []
% 7.32/1.49  --abstr_ref_prep                        false
% 7.32/1.49  --abstr_ref_until_sat                   false
% 7.32/1.49  --abstr_ref_sig_restrict                funpre
% 7.32/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.32/1.49  --abstr_ref_under                       []
% 7.32/1.49  
% 7.32/1.49  ------ SAT Options
% 7.32/1.49  
% 7.32/1.49  --sat_mode                              false
% 7.32/1.49  --sat_fm_restart_options                ""
% 7.32/1.49  --sat_gr_def                            false
% 7.32/1.49  --sat_epr_types                         true
% 7.32/1.49  --sat_non_cyclic_types                  false
% 7.32/1.49  --sat_finite_models                     false
% 7.32/1.49  --sat_fm_lemmas                         false
% 7.32/1.49  --sat_fm_prep                           false
% 7.32/1.49  --sat_fm_uc_incr                        true
% 7.32/1.49  --sat_out_model                         small
% 7.32/1.49  --sat_out_clauses                       false
% 7.32/1.49  
% 7.32/1.49  ------ QBF Options
% 7.32/1.49  
% 7.32/1.49  --qbf_mode                              false
% 7.32/1.49  --qbf_elim_univ                         false
% 7.32/1.49  --qbf_dom_inst                          none
% 7.32/1.49  --qbf_dom_pre_inst                      false
% 7.32/1.49  --qbf_sk_in                             false
% 7.32/1.49  --qbf_pred_elim                         true
% 7.32/1.49  --qbf_split                             512
% 7.32/1.49  
% 7.32/1.49  ------ BMC1 Options
% 7.32/1.49  
% 7.32/1.49  --bmc1_incremental                      false
% 7.32/1.49  --bmc1_axioms                           reachable_all
% 7.32/1.49  --bmc1_min_bound                        0
% 7.32/1.49  --bmc1_max_bound                        -1
% 7.32/1.49  --bmc1_max_bound_default                -1
% 7.32/1.49  --bmc1_symbol_reachability              true
% 7.32/1.49  --bmc1_property_lemmas                  false
% 7.32/1.49  --bmc1_k_induction                      false
% 7.32/1.49  --bmc1_non_equiv_states                 false
% 7.32/1.49  --bmc1_deadlock                         false
% 7.32/1.49  --bmc1_ucm                              false
% 7.32/1.49  --bmc1_add_unsat_core                   none
% 7.32/1.49  --bmc1_unsat_core_children              false
% 7.32/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.32/1.49  --bmc1_out_stat                         full
% 7.32/1.49  --bmc1_ground_init                      false
% 7.32/1.49  --bmc1_pre_inst_next_state              false
% 7.32/1.49  --bmc1_pre_inst_state                   false
% 7.32/1.49  --bmc1_pre_inst_reach_state             false
% 7.32/1.49  --bmc1_out_unsat_core                   false
% 7.32/1.49  --bmc1_aig_witness_out                  false
% 7.32/1.49  --bmc1_verbose                          false
% 7.32/1.49  --bmc1_dump_clauses_tptp                false
% 7.32/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.32/1.49  --bmc1_dump_file                        -
% 7.32/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.32/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.32/1.49  --bmc1_ucm_extend_mode                  1
% 7.32/1.49  --bmc1_ucm_init_mode                    2
% 7.32/1.49  --bmc1_ucm_cone_mode                    none
% 7.32/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.32/1.49  --bmc1_ucm_relax_model                  4
% 7.32/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.32/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.32/1.49  --bmc1_ucm_layered_model                none
% 7.32/1.49  --bmc1_ucm_max_lemma_size               10
% 7.32/1.49  
% 7.32/1.49  ------ AIG Options
% 7.32/1.49  
% 7.32/1.49  --aig_mode                              false
% 7.32/1.49  
% 7.32/1.49  ------ Instantiation Options
% 7.32/1.49  
% 7.32/1.49  --instantiation_flag                    true
% 7.32/1.49  --inst_sos_flag                         true
% 7.32/1.49  --inst_sos_phase                        true
% 7.32/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.32/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.32/1.49  --inst_lit_sel_side                     num_symb
% 7.32/1.49  --inst_solver_per_active                1400
% 7.32/1.49  --inst_solver_calls_frac                1.
% 7.32/1.49  --inst_passive_queue_type               priority_queues
% 7.32/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.32/1.49  --inst_passive_queues_freq              [25;2]
% 7.32/1.49  --inst_dismatching                      true
% 7.32/1.49  --inst_eager_unprocessed_to_passive     true
% 7.32/1.49  --inst_prop_sim_given                   true
% 7.32/1.49  --inst_prop_sim_new                     false
% 7.32/1.49  --inst_subs_new                         false
% 7.32/1.49  --inst_eq_res_simp                      false
% 7.32/1.49  --inst_subs_given                       false
% 7.32/1.49  --inst_orphan_elimination               true
% 7.32/1.49  --inst_learning_loop_flag               true
% 7.32/1.49  --inst_learning_start                   3000
% 7.32/1.49  --inst_learning_factor                  2
% 7.32/1.49  --inst_start_prop_sim_after_learn       3
% 7.32/1.49  --inst_sel_renew                        solver
% 7.32/1.49  --inst_lit_activity_flag                true
% 7.32/1.49  --inst_restr_to_given                   false
% 7.32/1.49  --inst_activity_threshold               500
% 7.32/1.49  --inst_out_proof                        true
% 7.32/1.49  
% 7.32/1.49  ------ Resolution Options
% 7.32/1.49  
% 7.32/1.49  --resolution_flag                       true
% 7.32/1.49  --res_lit_sel                           adaptive
% 7.32/1.49  --res_lit_sel_side                      none
% 7.32/1.49  --res_ordering                          kbo
% 7.32/1.49  --res_to_prop_solver                    active
% 7.32/1.49  --res_prop_simpl_new                    false
% 7.32/1.49  --res_prop_simpl_given                  true
% 7.32/1.49  --res_passive_queue_type                priority_queues
% 7.32/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.32/1.49  --res_passive_queues_freq               [15;5]
% 7.32/1.49  --res_forward_subs                      full
% 7.32/1.49  --res_backward_subs                     full
% 7.32/1.49  --res_forward_subs_resolution           true
% 7.32/1.49  --res_backward_subs_resolution          true
% 7.32/1.49  --res_orphan_elimination                true
% 7.32/1.49  --res_time_limit                        2.
% 7.32/1.49  --res_out_proof                         true
% 7.32/1.49  
% 7.32/1.49  ------ Superposition Options
% 7.32/1.49  
% 7.32/1.49  --superposition_flag                    true
% 7.32/1.49  --sup_passive_queue_type                priority_queues
% 7.32/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.32/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.32/1.49  --demod_completeness_check              fast
% 7.32/1.49  --demod_use_ground                      true
% 7.32/1.49  --sup_to_prop_solver                    passive
% 7.32/1.49  --sup_prop_simpl_new                    true
% 7.32/1.49  --sup_prop_simpl_given                  true
% 7.32/1.49  --sup_fun_splitting                     true
% 7.32/1.49  --sup_smt_interval                      50000
% 7.32/1.49  
% 7.32/1.49  ------ Superposition Simplification Setup
% 7.32/1.49  
% 7.32/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.32/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.32/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.32/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.32/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.32/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.32/1.49  --sup_immed_triv                        [TrivRules]
% 7.32/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.49  --sup_immed_bw_main                     []
% 7.32/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.32/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.32/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.49  --sup_input_bw                          []
% 7.32/1.49  
% 7.32/1.49  ------ Combination Options
% 7.32/1.49  
% 7.32/1.49  --comb_res_mult                         3
% 7.32/1.49  --comb_sup_mult                         2
% 7.32/1.49  --comb_inst_mult                        10
% 7.32/1.49  
% 7.32/1.49  ------ Debug Options
% 7.32/1.49  
% 7.32/1.49  --dbg_backtrace                         false
% 7.32/1.49  --dbg_dump_prop_clauses                 false
% 7.32/1.49  --dbg_dump_prop_clauses_file            -
% 7.32/1.49  --dbg_out_stat                          false
% 7.32/1.49  ------ Parsing...
% 7.32/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.32/1.49  
% 7.32/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.32/1.49  
% 7.32/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.32/1.49  
% 7.32/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.32/1.49  ------ Proving...
% 7.32/1.49  ------ Problem Properties 
% 7.32/1.49  
% 7.32/1.49  
% 7.32/1.49  clauses                                 23
% 7.32/1.49  conjectures                             3
% 7.32/1.49  EPR                                     4
% 7.32/1.49  Horn                                    19
% 7.32/1.49  unary                                   8
% 7.32/1.49  binary                                  13
% 7.32/1.49  lits                                    40
% 7.32/1.49  lits eq                                 9
% 7.32/1.49  fd_pure                                 0
% 7.32/1.49  fd_pseudo                               0
% 7.32/1.49  fd_cond                                 0
% 7.32/1.49  fd_pseudo_cond                          0
% 7.32/1.49  AC symbols                              0
% 7.32/1.49  
% 7.32/1.49  ------ Schedule dynamic 5 is on 
% 7.32/1.49  
% 7.32/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.32/1.49  
% 7.32/1.49  
% 7.32/1.49  ------ 
% 7.32/1.49  Current options:
% 7.32/1.49  ------ 
% 7.32/1.49  
% 7.32/1.49  ------ Input Options
% 7.32/1.49  
% 7.32/1.49  --out_options                           all
% 7.32/1.49  --tptp_safe_out                         true
% 7.32/1.49  --problem_path                          ""
% 7.32/1.49  --include_path                          ""
% 7.32/1.49  --clausifier                            res/vclausify_rel
% 7.32/1.49  --clausifier_options                    ""
% 7.32/1.49  --stdin                                 false
% 7.32/1.49  --stats_out                             all
% 7.32/1.49  
% 7.32/1.49  ------ General Options
% 7.32/1.49  
% 7.32/1.49  --fof                                   false
% 7.32/1.49  --time_out_real                         305.
% 7.32/1.49  --time_out_virtual                      -1.
% 7.32/1.49  --symbol_type_check                     false
% 7.32/1.49  --clausify_out                          false
% 7.32/1.49  --sig_cnt_out                           false
% 7.32/1.49  --trig_cnt_out                          false
% 7.32/1.49  --trig_cnt_out_tolerance                1.
% 7.32/1.49  --trig_cnt_out_sk_spl                   false
% 7.32/1.49  --abstr_cl_out                          false
% 7.32/1.49  
% 7.32/1.49  ------ Global Options
% 7.32/1.49  
% 7.32/1.49  --schedule                              default
% 7.32/1.49  --add_important_lit                     false
% 7.32/1.49  --prop_solver_per_cl                    1000
% 7.32/1.49  --min_unsat_core                        false
% 7.32/1.49  --soft_assumptions                      false
% 7.32/1.49  --soft_lemma_size                       3
% 7.32/1.49  --prop_impl_unit_size                   0
% 7.32/1.49  --prop_impl_unit                        []
% 7.32/1.49  --share_sel_clauses                     true
% 7.32/1.49  --reset_solvers                         false
% 7.32/1.49  --bc_imp_inh                            [conj_cone]
% 7.32/1.49  --conj_cone_tolerance                   3.
% 7.32/1.49  --extra_neg_conj                        none
% 7.32/1.49  --large_theory_mode                     true
% 7.32/1.49  --prolific_symb_bound                   200
% 7.32/1.49  --lt_threshold                          2000
% 7.32/1.49  --clause_weak_htbl                      true
% 7.32/1.49  --gc_record_bc_elim                     false
% 7.32/1.49  
% 7.32/1.49  ------ Preprocessing Options
% 7.32/1.49  
% 7.32/1.49  --preprocessing_flag                    true
% 7.32/1.49  --time_out_prep_mult                    0.1
% 7.32/1.49  --splitting_mode                        input
% 7.32/1.49  --splitting_grd                         true
% 7.32/1.49  --splitting_cvd                         false
% 7.32/1.49  --splitting_cvd_svl                     false
% 7.32/1.49  --splitting_nvd                         32
% 7.32/1.49  --sub_typing                            true
% 7.32/1.49  --prep_gs_sim                           true
% 7.32/1.49  --prep_unflatten                        true
% 7.32/1.49  --prep_res_sim                          true
% 7.32/1.49  --prep_upred                            true
% 7.32/1.49  --prep_sem_filter                       exhaustive
% 7.32/1.49  --prep_sem_filter_out                   false
% 7.32/1.49  --pred_elim                             true
% 7.32/1.49  --res_sim_input                         true
% 7.32/1.49  --eq_ax_congr_red                       true
% 7.32/1.49  --pure_diseq_elim                       true
% 7.32/1.49  --brand_transform                       false
% 7.32/1.49  --non_eq_to_eq                          false
% 7.32/1.49  --prep_def_merge                        true
% 7.32/1.49  --prep_def_merge_prop_impl              false
% 7.32/1.49  --prep_def_merge_mbd                    true
% 7.32/1.49  --prep_def_merge_tr_red                 false
% 7.32/1.49  --prep_def_merge_tr_cl                  false
% 7.32/1.49  --smt_preprocessing                     true
% 7.32/1.49  --smt_ac_axioms                         fast
% 7.32/1.49  --preprocessed_out                      false
% 7.32/1.49  --preprocessed_stats                    false
% 7.32/1.49  
% 7.32/1.49  ------ Abstraction refinement Options
% 7.32/1.49  
% 7.32/1.49  --abstr_ref                             []
% 7.32/1.49  --abstr_ref_prep                        false
% 7.32/1.49  --abstr_ref_until_sat                   false
% 7.32/1.49  --abstr_ref_sig_restrict                funpre
% 7.32/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.32/1.49  --abstr_ref_under                       []
% 7.32/1.49  
% 7.32/1.49  ------ SAT Options
% 7.32/1.49  
% 7.32/1.49  --sat_mode                              false
% 7.32/1.49  --sat_fm_restart_options                ""
% 7.32/1.49  --sat_gr_def                            false
% 7.32/1.49  --sat_epr_types                         true
% 7.32/1.49  --sat_non_cyclic_types                  false
% 7.32/1.49  --sat_finite_models                     false
% 7.32/1.49  --sat_fm_lemmas                         false
% 7.32/1.49  --sat_fm_prep                           false
% 7.32/1.49  --sat_fm_uc_incr                        true
% 7.32/1.49  --sat_out_model                         small
% 7.32/1.49  --sat_out_clauses                       false
% 7.32/1.49  
% 7.32/1.49  ------ QBF Options
% 7.32/1.49  
% 7.32/1.49  --qbf_mode                              false
% 7.32/1.49  --qbf_elim_univ                         false
% 7.32/1.49  --qbf_dom_inst                          none
% 7.32/1.49  --qbf_dom_pre_inst                      false
% 7.32/1.49  --qbf_sk_in                             false
% 7.32/1.49  --qbf_pred_elim                         true
% 7.32/1.49  --qbf_split                             512
% 7.32/1.49  
% 7.32/1.49  ------ BMC1 Options
% 7.32/1.49  
% 7.32/1.49  --bmc1_incremental                      false
% 7.32/1.49  --bmc1_axioms                           reachable_all
% 7.32/1.49  --bmc1_min_bound                        0
% 7.32/1.49  --bmc1_max_bound                        -1
% 7.32/1.49  --bmc1_max_bound_default                -1
% 7.32/1.49  --bmc1_symbol_reachability              true
% 7.32/1.49  --bmc1_property_lemmas                  false
% 7.32/1.49  --bmc1_k_induction                      false
% 7.32/1.49  --bmc1_non_equiv_states                 false
% 7.32/1.49  --bmc1_deadlock                         false
% 7.32/1.49  --bmc1_ucm                              false
% 7.32/1.49  --bmc1_add_unsat_core                   none
% 7.32/1.49  --bmc1_unsat_core_children              false
% 7.32/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.32/1.49  --bmc1_out_stat                         full
% 7.32/1.49  --bmc1_ground_init                      false
% 7.32/1.49  --bmc1_pre_inst_next_state              false
% 7.32/1.49  --bmc1_pre_inst_state                   false
% 7.32/1.49  --bmc1_pre_inst_reach_state             false
% 7.32/1.49  --bmc1_out_unsat_core                   false
% 7.32/1.49  --bmc1_aig_witness_out                  false
% 7.32/1.49  --bmc1_verbose                          false
% 7.32/1.49  --bmc1_dump_clauses_tptp                false
% 7.32/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.32/1.49  --bmc1_dump_file                        -
% 7.32/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.32/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.32/1.49  --bmc1_ucm_extend_mode                  1
% 7.32/1.49  --bmc1_ucm_init_mode                    2
% 7.32/1.49  --bmc1_ucm_cone_mode                    none
% 7.32/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.32/1.49  --bmc1_ucm_relax_model                  4
% 7.32/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.32/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.32/1.49  --bmc1_ucm_layered_model                none
% 7.32/1.49  --bmc1_ucm_max_lemma_size               10
% 7.32/1.49  
% 7.32/1.49  ------ AIG Options
% 7.32/1.49  
% 7.32/1.49  --aig_mode                              false
% 7.32/1.49  
% 7.32/1.49  ------ Instantiation Options
% 7.32/1.49  
% 7.32/1.49  --instantiation_flag                    true
% 7.32/1.49  --inst_sos_flag                         true
% 7.32/1.49  --inst_sos_phase                        true
% 7.32/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.32/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.32/1.49  --inst_lit_sel_side                     none
% 7.32/1.49  --inst_solver_per_active                1400
% 7.32/1.49  --inst_solver_calls_frac                1.
% 7.32/1.49  --inst_passive_queue_type               priority_queues
% 7.32/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.32/1.49  --inst_passive_queues_freq              [25;2]
% 7.32/1.49  --inst_dismatching                      true
% 7.32/1.49  --inst_eager_unprocessed_to_passive     true
% 7.32/1.49  --inst_prop_sim_given                   true
% 7.32/1.49  --inst_prop_sim_new                     false
% 7.32/1.49  --inst_subs_new                         false
% 7.32/1.49  --inst_eq_res_simp                      false
% 7.32/1.49  --inst_subs_given                       false
% 7.32/1.49  --inst_orphan_elimination               true
% 7.32/1.49  --inst_learning_loop_flag               true
% 7.32/1.49  --inst_learning_start                   3000
% 7.32/1.49  --inst_learning_factor                  2
% 7.32/1.49  --inst_start_prop_sim_after_learn       3
% 7.32/1.49  --inst_sel_renew                        solver
% 7.32/1.49  --inst_lit_activity_flag                true
% 7.32/1.49  --inst_restr_to_given                   false
% 7.32/1.49  --inst_activity_threshold               500
% 7.32/1.49  --inst_out_proof                        true
% 7.32/1.49  
% 7.32/1.49  ------ Resolution Options
% 7.32/1.49  
% 7.32/1.49  --resolution_flag                       false
% 7.32/1.49  --res_lit_sel                           adaptive
% 7.32/1.49  --res_lit_sel_side                      none
% 7.32/1.49  --res_ordering                          kbo
% 7.32/1.49  --res_to_prop_solver                    active
% 7.32/1.49  --res_prop_simpl_new                    false
% 7.32/1.49  --res_prop_simpl_given                  true
% 7.32/1.49  --res_passive_queue_type                priority_queues
% 7.32/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.32/1.49  --res_passive_queues_freq               [15;5]
% 7.32/1.49  --res_forward_subs                      full
% 7.32/1.49  --res_backward_subs                     full
% 7.32/1.49  --res_forward_subs_resolution           true
% 7.32/1.49  --res_backward_subs_resolution          true
% 7.32/1.49  --res_orphan_elimination                true
% 7.32/1.49  --res_time_limit                        2.
% 7.32/1.49  --res_out_proof                         true
% 7.32/1.49  
% 7.32/1.49  ------ Superposition Options
% 7.32/1.49  
% 7.32/1.49  --superposition_flag                    true
% 7.32/1.49  --sup_passive_queue_type                priority_queues
% 7.32/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.32/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.32/1.49  --demod_completeness_check              fast
% 7.32/1.49  --demod_use_ground                      true
% 7.32/1.49  --sup_to_prop_solver                    passive
% 7.32/1.49  --sup_prop_simpl_new                    true
% 7.32/1.49  --sup_prop_simpl_given                  true
% 7.32/1.49  --sup_fun_splitting                     true
% 7.32/1.49  --sup_smt_interval                      50000
% 7.32/1.49  
% 7.32/1.49  ------ Superposition Simplification Setup
% 7.32/1.49  
% 7.32/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.32/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.32/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.32/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.32/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.32/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.32/1.49  --sup_immed_triv                        [TrivRules]
% 7.32/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.49  --sup_immed_bw_main                     []
% 7.32/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.32/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.32/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.49  --sup_input_bw                          []
% 7.32/1.49  
% 7.32/1.49  ------ Combination Options
% 7.32/1.49  
% 7.32/1.49  --comb_res_mult                         3
% 7.32/1.49  --comb_sup_mult                         2
% 7.32/1.49  --comb_inst_mult                        10
% 7.32/1.49  
% 7.32/1.49  ------ Debug Options
% 7.32/1.49  
% 7.32/1.49  --dbg_backtrace                         false
% 7.32/1.49  --dbg_dump_prop_clauses                 false
% 7.32/1.49  --dbg_dump_prop_clauses_file            -
% 7.32/1.49  --dbg_out_stat                          false
% 7.32/1.49  
% 7.32/1.49  
% 7.32/1.49  
% 7.32/1.49  
% 7.32/1.49  ------ Proving...
% 7.32/1.49  
% 7.32/1.49  
% 7.32/1.49  % SZS status Theorem for theBenchmark.p
% 7.32/1.49  
% 7.32/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.32/1.49  
% 7.32/1.49  fof(f12,axiom,(
% 7.32/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 7.32/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f25,plain,(
% 7.32/1.49    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.32/1.49    inference(ennf_transformation,[],[f12])).
% 7.32/1.49  
% 7.32/1.49  fof(f55,plain,(
% 7.32/1.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.32/1.49    inference(cnf_transformation,[],[f25])).
% 7.32/1.49  
% 7.32/1.49  fof(f17,conjecture,(
% 7.32/1.49    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.32/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f18,negated_conjecture,(
% 7.32/1.49    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.32/1.49    inference(negated_conjecture,[],[f17])).
% 7.32/1.49  
% 7.32/1.49  fof(f26,plain,(
% 7.32/1.49    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 7.32/1.49    inference(ennf_transformation,[],[f18])).
% 7.32/1.49  
% 7.32/1.49  fof(f27,plain,(
% 7.32/1.49    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 7.32/1.49    inference(flattening,[],[f26])).
% 7.32/1.49  
% 7.32/1.49  fof(f35,plain,(
% 7.32/1.49    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 7.32/1.49    introduced(choice_axiom,[])).
% 7.32/1.49  
% 7.32/1.49  fof(f36,plain,(
% 7.32/1.49    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 7.32/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f35])).
% 7.32/1.49  
% 7.32/1.49  fof(f61,plain,(
% 7.32/1.49    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 7.32/1.49    inference(cnf_transformation,[],[f36])).
% 7.32/1.49  
% 7.32/1.49  fof(f8,axiom,(
% 7.32/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.32/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f48,plain,(
% 7.32/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.32/1.49    inference(cnf_transformation,[],[f8])).
% 7.32/1.49  
% 7.32/1.49  fof(f13,axiom,(
% 7.32/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.32/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f56,plain,(
% 7.32/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.32/1.49    inference(cnf_transformation,[],[f13])).
% 7.32/1.49  
% 7.32/1.49  fof(f14,axiom,(
% 7.32/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.32/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f57,plain,(
% 7.32/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.32/1.49    inference(cnf_transformation,[],[f14])).
% 7.32/1.49  
% 7.32/1.49  fof(f15,axiom,(
% 7.32/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.32/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f58,plain,(
% 7.32/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.32/1.49    inference(cnf_transformation,[],[f15])).
% 7.32/1.49  
% 7.32/1.49  fof(f65,plain,(
% 7.32/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.32/1.49    inference(definition_unfolding,[],[f57,f58])).
% 7.32/1.49  
% 7.32/1.49  fof(f66,plain,(
% 7.32/1.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.32/1.49    inference(definition_unfolding,[],[f56,f65])).
% 7.32/1.49  
% 7.32/1.49  fof(f76,plain,(
% 7.32/1.49    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5))),
% 7.32/1.49    inference(definition_unfolding,[],[f61,f48,f66])).
% 7.32/1.49  
% 7.32/1.49  fof(f11,axiom,(
% 7.32/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.32/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f33,plain,(
% 7.32/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 7.32/1.49    inference(nnf_transformation,[],[f11])).
% 7.32/1.49  
% 7.32/1.49  fof(f53,plain,(
% 7.32/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.32/1.49    inference(cnf_transformation,[],[f33])).
% 7.32/1.49  
% 7.32/1.49  fof(f7,axiom,(
% 7.32/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.32/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f47,plain,(
% 7.32/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.32/1.49    inference(cnf_transformation,[],[f7])).
% 7.32/1.49  
% 7.32/1.49  fof(f73,plain,(
% 7.32/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 7.32/1.49    inference(definition_unfolding,[],[f47,f48,f48,f48,f48])).
% 7.32/1.49  
% 7.32/1.49  fof(f10,axiom,(
% 7.32/1.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.32/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f52,plain,(
% 7.32/1.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.32/1.49    inference(cnf_transformation,[],[f10])).
% 7.32/1.49  
% 7.32/1.49  fof(f16,axiom,(
% 7.32/1.49    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 7.32/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f34,plain,(
% 7.32/1.49    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 7.32/1.49    inference(nnf_transformation,[],[f16])).
% 7.32/1.49  
% 7.32/1.49  fof(f60,plain,(
% 7.32/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 7.32/1.49    inference(cnf_transformation,[],[f34])).
% 7.32/1.49  
% 7.32/1.49  fof(f74,plain,(
% 7.32/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 7.32/1.49    inference(definition_unfolding,[],[f60,f66])).
% 7.32/1.49  
% 7.32/1.49  fof(f62,plain,(
% 7.32/1.49    r2_hidden(sK5,sK4)),
% 7.32/1.49    inference(cnf_transformation,[],[f36])).
% 7.32/1.49  
% 7.32/1.49  fof(f4,axiom,(
% 7.32/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.32/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f19,plain,(
% 7.32/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.32/1.49    inference(rectify,[],[f4])).
% 7.32/1.49  
% 7.32/1.49  fof(f22,plain,(
% 7.32/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.32/1.49    inference(ennf_transformation,[],[f19])).
% 7.32/1.49  
% 7.32/1.49  fof(f29,plain,(
% 7.32/1.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.32/1.49    introduced(choice_axiom,[])).
% 7.32/1.49  
% 7.32/1.49  fof(f30,plain,(
% 7.32/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.32/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f29])).
% 7.32/1.49  
% 7.32/1.49  fof(f43,plain,(
% 7.32/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.32/1.49    inference(cnf_transformation,[],[f30])).
% 7.32/1.49  
% 7.32/1.49  fof(f1,axiom,(
% 7.32/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.32/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f37,plain,(
% 7.32/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.32/1.49    inference(cnf_transformation,[],[f1])).
% 7.32/1.49  
% 7.32/1.49  fof(f68,plain,(
% 7.32/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.32/1.49    inference(definition_unfolding,[],[f37,f48,f48])).
% 7.32/1.49  
% 7.32/1.49  fof(f3,axiom,(
% 7.32/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.32/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f21,plain,(
% 7.32/1.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.32/1.49    inference(ennf_transformation,[],[f3])).
% 7.32/1.49  
% 7.32/1.49  fof(f40,plain,(
% 7.32/1.49    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.32/1.49    inference(cnf_transformation,[],[f21])).
% 7.32/1.49  
% 7.32/1.49  fof(f2,axiom,(
% 7.32/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.32/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f28,plain,(
% 7.32/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.32/1.49    inference(nnf_transformation,[],[f2])).
% 7.32/1.49  
% 7.32/1.49  fof(f38,plain,(
% 7.32/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.32/1.49    inference(cnf_transformation,[],[f28])).
% 7.32/1.49  
% 7.32/1.49  fof(f70,plain,(
% 7.32/1.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.32/1.49    inference(definition_unfolding,[],[f38,f48])).
% 7.32/1.49  
% 7.32/1.49  fof(f63,plain,(
% 7.32/1.49    r1_xboole_0(sK4,sK3)),
% 7.32/1.49    inference(cnf_transformation,[],[f36])).
% 7.32/1.49  
% 7.32/1.49  fof(f6,axiom,(
% 7.32/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.32/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f46,plain,(
% 7.32/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.32/1.49    inference(cnf_transformation,[],[f6])).
% 7.32/1.49  
% 7.32/1.49  fof(f67,plain,(
% 7.32/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.32/1.49    inference(definition_unfolding,[],[f46,f48])).
% 7.32/1.49  
% 7.32/1.49  fof(f39,plain,(
% 7.32/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.32/1.49    inference(cnf_transformation,[],[f28])).
% 7.32/1.49  
% 7.32/1.49  fof(f69,plain,(
% 7.32/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.32/1.49    inference(definition_unfolding,[],[f39,f48])).
% 7.32/1.49  
% 7.32/1.49  fof(f9,axiom,(
% 7.32/1.49    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.32/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f24,plain,(
% 7.32/1.49    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.32/1.49    inference(ennf_transformation,[],[f9])).
% 7.32/1.49  
% 7.32/1.49  fof(f49,plain,(
% 7.32/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 7.32/1.49    inference(cnf_transformation,[],[f24])).
% 7.32/1.49  
% 7.32/1.49  fof(f64,plain,(
% 7.32/1.49    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 7.32/1.49    inference(cnf_transformation,[],[f36])).
% 7.32/1.49  
% 7.32/1.49  cnf(c_17,plain,
% 7.32/1.49      ( ~ r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 7.32/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_23,negated_conjecture,
% 7.32/1.49      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 7.32/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_297,plain,
% 7.32/1.49      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
% 7.32/1.49      | k2_enumset1(sK5,sK5,sK5,sK5) != X2
% 7.32/1.49      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X0 ),
% 7.32/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_298,plain,
% 7.32/1.49      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 7.32/1.49      inference(unflattening,[status(thm)],[c_297]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_956,plain,
% 7.32/1.49      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16,plain,
% 7.32/1.49      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 7.32/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_962,plain,
% 7.32/1.49      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2042,plain,
% 7.32/1.49      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_956,c_962]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_10,plain,
% 7.32/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 7.32/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3165,plain,
% 7.32/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5)))))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2042,c_10]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_14,plain,
% 7.32/1.49      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 7.32/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_964,plain,
% 7.32/1.49      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_18,plain,
% 7.32/1.49      ( r2_hidden(X0,X1)
% 7.32/1.49      | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
% 7.32/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_961,plain,
% 7.32/1.49      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
% 7.32/1.49      | r2_hidden(X1,X0) = iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_22,negated_conjecture,
% 7.32/1.49      ( r2_hidden(sK5,sK4) ),
% 7.32/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_957,plain,
% 7.32/1.49      ( r2_hidden(sK5,sK4) = iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5,plain,
% 7.32/1.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 7.32/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_972,plain,
% 7.32/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.32/1.49      | r2_hidden(X0,X2) != iProver_top
% 7.32/1.49      | r1_xboole_0(X2,X1) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5423,plain,
% 7.32/1.49      ( r2_hidden(sK5,X0) != iProver_top
% 7.32/1.49      | r1_xboole_0(X0,sK4) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_957,c_972]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5966,plain,
% 7.32/1.49      ( k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5)) = X0
% 7.32/1.49      | r1_xboole_0(X0,sK4) != iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_961,c_5423]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_6086,plain,
% 7.32/1.49      ( k4_xboole_0(k4_xboole_0(X0,sK4),k2_enumset1(sK5,sK5,sK5,sK5)) = k4_xboole_0(X0,sK4) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_964,c_5966]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_7488,plain,
% 7.32/1.49      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_6086,c_2042]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1,plain,
% 7.32/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.32/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_9732,plain,
% 7.32/1.49      ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_7488,c_1]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4,plain,
% 7.32/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.32/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_973,plain,
% 7.32/1.49      ( r1_xboole_0(X0,X1) != iProver_top
% 7.32/1.49      | r1_xboole_0(X1,X0) = iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2239,plain,
% 7.32/1.49      ( r1_xboole_0(k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_956,c_973]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_7489,plain,
% 7.32/1.49      ( r1_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_6086,c_2239]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_7832,plain,
% 7.32/1.49      ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = k4_xboole_0(X0,sK4) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_7489,c_962]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3,plain,
% 7.32/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.32/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.32/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_974,plain,
% 7.32/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.32/1.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_7830,plain,
% 7.32/1.49      ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) = k1_xboole_0 ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_7489,c_974]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_7833,plain,
% 7.32/1.49      ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,sK4)) = k1_xboole_0 ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_7830,c_7832]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_9744,plain,
% 7.32/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_7488,c_10]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_21,negated_conjecture,
% 7.32/1.49      ( r1_xboole_0(sK4,sK3) ),
% 7.32/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_958,plain,
% 7.32/1.49      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2238,plain,
% 7.32/1.49      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_958,c_973]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2440,plain,
% 7.32/1.49      ( k4_xboole_0(sK3,sK4) = sK3 ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2238,c_962]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1665,plain,
% 7.32/1.49      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1,c_964]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2449,plain,
% 7.32/1.49      ( r1_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)),sK3) = iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2440,c_1665]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2041,plain,
% 7.32/1.49      ( k4_xboole_0(sK4,sK3) = sK4 ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_958,c_962]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2452,plain,
% 7.32/1.49      ( r1_xboole_0(k4_xboole_0(sK4,sK4),sK3) = iProver_top ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_2449,c_2041]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2661,plain,
% 7.32/1.49      ( r1_xboole_0(sK3,k4_xboole_0(sK4,sK4)) = iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2452,c_973]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3987,plain,
% 7.32/1.49      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK4,sK4))) = k1_xboole_0 ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2661,c_974]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2450,plain,
% 7.32/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) = k4_xboole_0(sK3,sK3) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2440,c_1]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2451,plain,
% 7.32/1.49      ( k4_xboole_0(sK3,sK3) = k4_xboole_0(sK4,sK4) ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_2450,c_2041]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3426,plain,
% 7.32/1.49      ( k4_xboole_0(sK3,k4_xboole_0(sK4,sK4)) = sK3 ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2661,c_962]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3988,plain,
% 7.32/1.49      ( k4_xboole_0(sK4,sK4) = k1_xboole_0 ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_3987,c_2451,c_3426]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4290,plain,
% 7.32/1.49      ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_3988,c_2451]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_9745,plain,
% 7.32/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_9744,c_2440,c_4290]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_9902,plain,
% 7.32/1.49      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)),k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0))) = k1_xboole_0 ),
% 7.32/1.49      inference(light_normalisation,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_9732,c_7832,c_7833,c_9745]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_0,plain,
% 7.32/1.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.32/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_10011,plain,
% 7.32/1.49      ( k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0))) = k4_xboole_0(sK2,sK3) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_9745,c_0]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_10028,plain,
% 7.32/1.49      ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK3) ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_10011,c_0]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16618,plain,
% 7.32/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5)))))) = k1_xboole_0 ),
% 7.32/1.49      inference(light_normalisation,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_3165,c_3165,c_9902,c_10028]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16660,plain,
% 7.32/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))))) = k5_xboole_0(sK2,k1_xboole_0) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_16618,c_0]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2252,plain,
% 7.32/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(k4_xboole_0(sK4,sK4),k4_xboole_0(k4_xboole_0(sK4,sK4),X0)) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2041,c_10]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3349,plain,
% 7.32/1.49      ( k5_xboole_0(k4_xboole_0(sK4,sK4),k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))))) = k4_xboole_0(k4_xboole_0(sK4,sK4),X0) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2252,c_0]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2662,plain,
% 7.32/1.49      ( k4_xboole_0(k4_xboole_0(sK4,sK4),sK3) = k4_xboole_0(sK4,sK4) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2452,c_962]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3437,plain,
% 7.32/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)))) = k4_xboole_0(k4_xboole_0(sK4,sK4),k4_xboole_0(sK4,sK4)) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2662,c_2252]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3438,plain,
% 7.32/1.49      ( k4_xboole_0(k4_xboole_0(sK4,sK4),k4_xboole_0(sK4,sK4)) = k4_xboole_0(sK4,sK4) ),
% 7.32/1.49      inference(light_normalisation,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_3437,c_2041,c_2451,c_3426]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3737,plain,
% 7.32/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK4,sK4))))) = k4_xboole_0(k4_xboole_0(sK4,sK4),k4_xboole_0(sK4,sK4)) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_3438,c_2252]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3738,plain,
% 7.32/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK4,sK4))))) = k4_xboole_0(sK4,sK4) ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_3737,c_3438]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3739,plain,
% 7.32/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK4,sK4))) = k4_xboole_0(sK4,sK4) ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_3738,c_2451,c_3426]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5071,plain,
% 7.32/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k1_xboole_0)) = k1_xboole_0 ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_3739,c_3739,c_3988]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5089,plain,
% 7.32/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_5071,c_10]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4288,plain,
% 7.32/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_3988,c_2252]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5259,plain,
% 7.32/1.49      ( k5_xboole_0(sK4,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_4288,c_0]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5457,plain,
% 7.32/1.49      ( k5_xboole_0(sK4,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(sK4,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_5089,c_0]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_5718,plain,
% 7.32/1.49      ( k4_xboole_0(sK4,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_5259,c_5457]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_13647,plain,
% 7.32/1.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.32/1.49      inference(light_normalisation,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_3349,c_3349,c_3988,c_5089,c_5718]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4284,plain,
% 7.32/1.49      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_3988,c_3438]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1666,plain,
% 7.32/1.49      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4323,plain,
% 7.32/1.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_4284,c_1666]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4326,plain,
% 7.32/1.49      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_4323,c_4284]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1889,plain,
% 7.32/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1,c_10]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_10750,plain,
% 7.32/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)),X0))))) = k4_xboole_0(k4_xboole_0(sK4,sK4),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,sK4)))) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_2041,c_1889]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_10994,plain,
% 7.32/1.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,X0))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
% 7.32/1.49      inference(light_normalisation,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_10750,c_2041,c_3988]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_10995,plain,
% 7.32/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_10994,c_5089,c_5718]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_10759,plain,
% 7.32/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)),X0))))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_4284,c_1889]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1664,plain,
% 7.32/1.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_10872,plain,
% 7.32/1.49      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))))))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1889,c_1664]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2040,plain,
% 7.32/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_964,c_962]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3980,plain,
% 7.32/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_964,c_974]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_3995,plain,
% 7.32/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_3980,c_2040]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4722,plain,
% 7.32/1.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_10,c_1664]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_10893,plain,
% 7.32/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 7.32/1.49      inference(demodulation,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_10872,c_2040,c_3995,c_4722]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_10894,plain,
% 7.32/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_10893,c_3995,c_4284]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_10985,plain,
% 7.32/1.49      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))) = k1_xboole_0 ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_10759,c_10894]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_10986,plain,
% 7.32/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_10985,c_4284]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_11816,plain,
% 7.32/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k1_xboole_0 ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_10995,c_10986]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_11863,plain,
% 7.32/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_11816,c_0]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_11932,plain,
% 7.32/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.32/1.49      inference(light_normalisation,[status(thm)],[c_11863,c_4326]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_13648,plain,
% 7.32/1.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_13647,c_0,c_4326,c_11932]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_13839,plain,
% 7.32/1.49      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_13648,c_1666]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16698,plain,
% 7.32/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))))) = k4_xboole_0(sK2,k1_xboole_0) ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_16660,c_13839]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_16708,plain,
% 7.32/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 7.32/1.49      inference(demodulation,[status(thm)],[c_16698,c_16618]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_2,plain,
% 7.32/1.49      ( r1_xboole_0(X0,X1)
% 7.32/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 7.32/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_975,plain,
% 7.32/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 7.32/1.49      | r1_xboole_0(X0,X1) = iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_4001,plain,
% 7.32/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 7.32/1.49      | r1_xboole_0(X1,X0) = iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_1,c_975]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_10005,plain,
% 7.32/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k1_xboole_0
% 7.32/1.49      | r1_xboole_0(sK3,sK2) = iProver_top ),
% 7.32/1.49      inference(superposition,[status(thm)],[c_9745,c_4001]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1294,plain,
% 7.32/1.49      ( r1_xboole_0(sK3,sK4) | ~ r1_xboole_0(sK4,sK3) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1295,plain,
% 7.32/1.49      ( r1_xboole_0(sK3,sK4) = iProver_top
% 7.32/1.49      | r1_xboole_0(sK4,sK3) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_1294]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_13,plain,
% 7.32/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.32/1.49      | ~ r1_xboole_0(X0,X2)
% 7.32/1.49      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.32/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1076,plain,
% 7.32/1.49      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
% 7.32/1.49      | ~ r1_xboole_0(sK3,sK4)
% 7.32/1.49      | ~ r1_xboole_0(sK3,sK2) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1077,plain,
% 7.32/1.49      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = iProver_top
% 7.32/1.49      | r1_xboole_0(sK3,sK4) != iProver_top
% 7.32/1.49      | r1_xboole_0(sK3,sK2) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_1076]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1016,plain,
% 7.32/1.49      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
% 7.32/1.49      | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
% 7.32/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_1017,plain,
% 7.32/1.49      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) = iProver_top
% 7.32/1.49      | r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_1016]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_20,negated_conjecture,
% 7.32/1.49      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
% 7.32/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_27,plain,
% 7.32/1.49      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) != iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(c_26,plain,
% 7.32/1.49      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 7.32/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.32/1.49  
% 7.32/1.49  cnf(contradiction,plain,
% 7.32/1.49      ( $false ),
% 7.32/1.49      inference(minisat,
% 7.32/1.49                [status(thm)],
% 7.32/1.49                [c_16708,c_10005,c_1295,c_1077,c_1017,c_27,c_26]) ).
% 7.32/1.49  
% 7.32/1.49  
% 7.32/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.32/1.49  
% 7.32/1.49  ------                               Statistics
% 7.32/1.49  
% 7.32/1.49  ------ General
% 7.32/1.49  
% 7.32/1.49  abstr_ref_over_cycles:                  0
% 7.32/1.49  abstr_ref_under_cycles:                 0
% 7.32/1.49  gc_basic_clause_elim:                   0
% 7.32/1.49  forced_gc_time:                         0
% 7.32/1.49  parsing_time:                           0.007
% 7.32/1.49  unif_index_cands_time:                  0.
% 7.32/1.49  unif_index_add_time:                    0.
% 7.32/1.49  orderings_time:                         0.
% 7.32/1.49  out_proof_time:                         0.01
% 7.32/1.49  total_time:                             0.588
% 7.32/1.49  num_of_symbols:                         45
% 7.32/1.49  num_of_terms:                           27073
% 7.32/1.49  
% 7.32/1.49  ------ Preprocessing
% 7.32/1.49  
% 7.32/1.49  num_of_splits:                          0
% 7.32/1.49  num_of_split_atoms:                     0
% 7.32/1.49  num_of_reused_defs:                     0
% 7.32/1.49  num_eq_ax_congr_red:                    15
% 7.32/1.49  num_of_sem_filtered_clauses:            1
% 7.32/1.49  num_of_subtypes:                        0
% 7.32/1.49  monotx_restored_types:                  0
% 7.32/1.49  sat_num_of_epr_types:                   0
% 7.32/1.49  sat_num_of_non_cyclic_types:            0
% 7.32/1.49  sat_guarded_non_collapsed_types:        0
% 7.32/1.49  num_pure_diseq_elim:                    0
% 7.32/1.49  simp_replaced_by:                       0
% 7.32/1.49  res_preprocessed:                       110
% 7.32/1.49  prep_upred:                             0
% 7.32/1.49  prep_unflattend:                        2
% 7.32/1.49  smt_new_axioms:                         0
% 7.32/1.49  pred_elim_cands:                        2
% 7.32/1.49  pred_elim:                              1
% 7.32/1.49  pred_elim_cl:                           1
% 7.32/1.49  pred_elim_cycles:                       3
% 7.32/1.49  merged_defs:                            24
% 7.32/1.49  merged_defs_ncl:                        0
% 7.32/1.49  bin_hyper_res:                          24
% 7.32/1.49  prep_cycles:                            4
% 7.32/1.49  pred_elim_time:                         0.
% 7.32/1.49  splitting_time:                         0.
% 7.32/1.49  sem_filter_time:                        0.
% 7.32/1.49  monotx_time:                            0.004
% 7.32/1.49  subtype_inf_time:                       0.
% 7.32/1.49  
% 7.32/1.49  ------ Problem properties
% 7.32/1.49  
% 7.32/1.49  clauses:                                23
% 7.32/1.49  conjectures:                            3
% 7.32/1.49  epr:                                    4
% 7.32/1.49  horn:                                   19
% 7.32/1.49  ground:                                 3
% 7.32/1.49  unary:                                  8
% 7.32/1.49  binary:                                 13
% 7.32/1.49  lits:                                   40
% 7.32/1.49  lits_eq:                                9
% 7.32/1.49  fd_pure:                                0
% 7.32/1.49  fd_pseudo:                              0
% 7.32/1.49  fd_cond:                                0
% 7.32/1.49  fd_pseudo_cond:                         0
% 7.32/1.49  ac_symbols:                             0
% 7.32/1.49  
% 7.32/1.49  ------ Propositional Solver
% 7.32/1.49  
% 7.32/1.49  prop_solver_calls:                      29
% 7.32/1.49  prop_fast_solver_calls:                 620
% 7.32/1.49  smt_solver_calls:                       0
% 7.32/1.49  smt_fast_solver_calls:                  0
% 7.32/1.49  prop_num_of_clauses:                    8093
% 7.32/1.49  prop_preprocess_simplified:             11381
% 7.32/1.49  prop_fo_subsumed:                       1
% 7.32/1.49  prop_solver_time:                       0.
% 7.32/1.49  smt_solver_time:                        0.
% 7.32/1.49  smt_fast_solver_time:                   0.
% 7.32/1.49  prop_fast_solver_time:                  0.
% 7.32/1.49  prop_unsat_core_time:                   0.
% 7.32/1.49  
% 7.32/1.49  ------ QBF
% 7.32/1.49  
% 7.32/1.49  qbf_q_res:                              0
% 7.32/1.49  qbf_num_tautologies:                    0
% 7.32/1.49  qbf_prep_cycles:                        0
% 7.32/1.49  
% 7.32/1.49  ------ BMC1
% 7.32/1.49  
% 7.32/1.49  bmc1_current_bound:                     -1
% 7.32/1.49  bmc1_last_solved_bound:                 -1
% 7.32/1.49  bmc1_unsat_core_size:                   -1
% 7.32/1.49  bmc1_unsat_core_parents_size:           -1
% 7.32/1.49  bmc1_merge_next_fun:                    0
% 7.32/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.32/1.49  
% 7.32/1.49  ------ Instantiation
% 7.32/1.49  
% 7.32/1.49  inst_num_of_clauses:                    1368
% 7.32/1.49  inst_num_in_passive:                    252
% 7.32/1.49  inst_num_in_active:                     573
% 7.32/1.49  inst_num_in_unprocessed:                543
% 7.32/1.49  inst_num_of_loops:                      590
% 7.32/1.49  inst_num_of_learning_restarts:          0
% 7.32/1.49  inst_num_moves_active_passive:          17
% 7.32/1.49  inst_lit_activity:                      0
% 7.32/1.49  inst_lit_activity_moves:                0
% 7.32/1.49  inst_num_tautologies:                   0
% 7.32/1.49  inst_num_prop_implied:                  0
% 7.32/1.49  inst_num_existing_simplified:           0
% 7.32/1.49  inst_num_eq_res_simplified:             0
% 7.32/1.49  inst_num_child_elim:                    0
% 7.32/1.49  inst_num_of_dismatching_blockings:      561
% 7.32/1.49  inst_num_of_non_proper_insts:           1654
% 7.32/1.49  inst_num_of_duplicates:                 0
% 7.32/1.49  inst_inst_num_from_inst_to_res:         0
% 7.32/1.49  inst_dismatching_checking_time:         0.
% 7.32/1.49  
% 7.32/1.49  ------ Resolution
% 7.32/1.49  
% 7.32/1.49  res_num_of_clauses:                     0
% 7.32/1.50  res_num_in_passive:                     0
% 7.32/1.50  res_num_in_active:                      0
% 7.32/1.50  res_num_of_loops:                       114
% 7.32/1.50  res_forward_subset_subsumed:            62
% 7.32/1.50  res_backward_subset_subsumed:           0
% 7.32/1.50  res_forward_subsumed:                   0
% 7.32/1.50  res_backward_subsumed:                  0
% 7.32/1.50  res_forward_subsumption_resolution:     0
% 7.32/1.50  res_backward_subsumption_resolution:    0
% 7.32/1.50  res_clause_to_clause_subsumption:       9630
% 7.32/1.50  res_orphan_elimination:                 0
% 7.32/1.50  res_tautology_del:                      109
% 7.32/1.50  res_num_eq_res_simplified:              0
% 7.32/1.50  res_num_sel_changes:                    0
% 7.32/1.50  res_moves_from_active_to_pass:          0
% 7.32/1.50  
% 7.32/1.50  ------ Superposition
% 7.32/1.50  
% 7.32/1.50  sup_time_total:                         0.
% 7.32/1.50  sup_time_generating:                    0.
% 7.32/1.50  sup_time_sim_full:                      0.
% 7.32/1.50  sup_time_sim_immed:                     0.
% 7.32/1.50  
% 7.32/1.50  sup_num_of_clauses:                     1148
% 7.32/1.50  sup_num_in_active:                      78
% 7.32/1.50  sup_num_in_passive:                     1070
% 7.32/1.50  sup_num_of_loops:                       117
% 7.32/1.50  sup_fw_superposition:                   1438
% 7.32/1.50  sup_bw_superposition:                   1657
% 7.32/1.50  sup_immediate_simplified:               1629
% 7.32/1.50  sup_given_eliminated:                   8
% 7.32/1.50  comparisons_done:                       0
% 7.32/1.50  comparisons_avoided:                    0
% 7.32/1.50  
% 7.32/1.50  ------ Simplifications
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  sim_fw_subset_subsumed:                 56
% 7.32/1.50  sim_bw_subset_subsumed:                 3
% 7.32/1.50  sim_fw_subsumed:                        219
% 7.32/1.50  sim_bw_subsumed:                        42
% 7.32/1.50  sim_fw_subsumption_res:                 0
% 7.32/1.50  sim_bw_subsumption_res:                 0
% 7.32/1.50  sim_tautology_del:                      4
% 7.32/1.50  sim_eq_tautology_del:                   293
% 7.32/1.50  sim_eq_res_simp:                        25
% 7.32/1.50  sim_fw_demodulated:                     900
% 7.32/1.50  sim_bw_demodulated:                     108
% 7.32/1.50  sim_light_normalised:                   963
% 7.32/1.50  sim_joinable_taut:                      0
% 7.32/1.50  sim_joinable_simp:                      0
% 7.32/1.50  sim_ac_normalised:                      0
% 7.32/1.50  sim_smt_subsumption:                    0
% 7.32/1.50  
%------------------------------------------------------------------------------
