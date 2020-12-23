%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:04 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 232 expanded)
%              Number of clauses        :   38 (  38 expanded)
%              Number of leaves         :   20 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  209 ( 372 expanded)
%              Number of equality atoms :   84 ( 218 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f25])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f46,f55])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f57])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f50,f59])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f41,f37])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f52,f59])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f60])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) )
        & ( ~ r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ) )
   => ( ( r2_hidden(sK1,sK2)
        | k4_xboole_0(k1_tarski(sK1),sK2) != k1_tarski(sK1) )
      & ( ~ r2_hidden(sK1,sK2)
        | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( r2_hidden(sK1,sK2)
      | k4_xboole_0(k1_tarski(sK1),sK2) != k1_tarski(sK1) )
    & ( ~ r2_hidden(sK1,sK2)
      | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f31])).

fof(f53,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f53,f37,f60,f60])).

fof(f54,plain,
    ( r2_hidden(sK1,sK2)
    | k4_xboole_0(k1_tarski(sK1),sK2) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,
    ( r2_hidden(sK1,sK2)
    | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f54,f37,f60,f60])).

cnf(c_316,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1579,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k3_xboole_0(X3,X4))
    | X2 != X0
    | k3_xboole_0(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_3098,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))
    | X2 != X0
    | k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_1579])).

cnf(c_7364,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(X1,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))
    | X1 != X0
    | k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_3098])).

cnf(c_7366,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK1,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))
    | k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_7364])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_960,plain,
    ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),X1)
    | k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),X1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2643,plain,
    ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),sK2)
    | k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0) ),
    inference(instantiation,[status(thm)],[c_960])).

cnf(c_2645,plain,
    ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)
    | k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2643])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2558,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))
    | ~ r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2560,plain,
    ( ~ r2_hidden(sK1,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))
    | ~ r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_2558])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_4,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_655,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_769,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_655])).

cnf(c_11,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
    | r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_648,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != iProver_top
    | r2_hidden(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2046,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_769,c_648])).

cnf(c_2047,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2046])).

cnf(c_2049,plain,
    ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_2047])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1449,plain,
    ( r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)
    | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_795,plain,
    ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),sK2)
    | ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_797,plain,
    ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_312,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_326,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_106,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_221,plain,
    ( r2_hidden(X0,X1)
    | X1 != X2
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X3
    | k5_xboole_0(X3,k3_xboole_0(X3,X2)) = X3 ),
    inference(resolution_lifted,[status(thm)],[c_106,c_8])).

cnf(c_222,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(sK1,sK2)
    | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_110,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_252,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_222,c_110])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK1,sK2)
    | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7366,c_2645,c_2560,c_2049,c_1449,c_797,c_326,c_252,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:49:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 3.01/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/1.00  
% 3.01/1.00  ------  iProver source info
% 3.01/1.00  
% 3.01/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.01/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/1.00  git: non_committed_changes: false
% 3.01/1.00  git: last_make_outside_of_git: false
% 3.01/1.00  
% 3.01/1.00  ------ 
% 3.01/1.00  ------ Parsing...
% 3.01/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.00  ------ Proving...
% 3.01/1.00  ------ Problem Properties 
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  clauses                                 14
% 3.01/1.00  conjectures                             0
% 3.01/1.00  EPR                                     1
% 3.01/1.00  Horn                                    12
% 3.01/1.00  unary                                   5
% 3.01/1.00  binary                                  8
% 3.01/1.00  lits                                    24
% 3.01/1.00  lits eq                                 6
% 3.01/1.00  fd_pure                                 0
% 3.01/1.00  fd_pseudo                               0
% 3.01/1.00  fd_cond                                 0
% 3.01/1.00  fd_pseudo_cond                          0
% 3.01/1.00  AC symbols                              0
% 3.01/1.00  
% 3.01/1.00  ------ Input Options Time Limit: Unbounded
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  ------ 
% 3.01/1.00  Current options:
% 3.01/1.00  ------ 
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  ------ Proving...
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  % SZS status Theorem for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  fof(f6,axiom,(
% 3.01/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f22,plain,(
% 3.01/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.01/1.00    inference(ennf_transformation,[],[f6])).
% 3.01/1.00  
% 3.01/1.00  fof(f39,plain,(
% 3.01/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f22])).
% 3.01/1.00  
% 3.01/1.00  fof(f3,axiom,(
% 3.01/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f20,plain,(
% 3.01/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.01/1.00    inference(rectify,[],[f3])).
% 3.01/1.00  
% 3.01/1.00  fof(f21,plain,(
% 3.01/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.01/1.00    inference(ennf_transformation,[],[f20])).
% 3.01/1.00  
% 3.01/1.00  fof(f25,plain,(
% 3.01/1.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f26,plain,(
% 3.01/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f25])).
% 3.01/1.00  
% 3.01/1.00  fof(f36,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.01/1.00    inference(cnf_transformation,[],[f26])).
% 3.01/1.00  
% 3.01/1.00  fof(f2,axiom,(
% 3.01/1.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f19,plain,(
% 3.01/1.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.01/1.00    inference(rectify,[],[f2])).
% 3.01/1.00  
% 3.01/1.00  fof(f34,plain,(
% 3.01/1.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.01/1.00    inference(cnf_transformation,[],[f19])).
% 3.01/1.00  
% 3.01/1.00  fof(f5,axiom,(
% 3.01/1.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f38,plain,(
% 3.01/1.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f5])).
% 3.01/1.00  
% 3.01/1.00  fof(f16,axiom,(
% 3.01/1.00    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f28,plain,(
% 3.01/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.01/1.00    inference(nnf_transformation,[],[f16])).
% 3.01/1.00  
% 3.01/1.00  fof(f29,plain,(
% 3.01/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.01/1.00    inference(flattening,[],[f28])).
% 3.01/1.00  
% 3.01/1.00  fof(f50,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f29])).
% 3.01/1.00  
% 3.01/1.00  fof(f9,axiom,(
% 3.01/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f43,plain,(
% 3.01/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f9])).
% 3.01/1.00  
% 3.01/1.00  fof(f10,axiom,(
% 3.01/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f44,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f10])).
% 3.01/1.00  
% 3.01/1.00  fof(f11,axiom,(
% 3.01/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f45,plain,(
% 3.01/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f11])).
% 3.01/1.00  
% 3.01/1.00  fof(f12,axiom,(
% 3.01/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f46,plain,(
% 3.01/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f12])).
% 3.01/1.00  
% 3.01/1.00  fof(f13,axiom,(
% 3.01/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f47,plain,(
% 3.01/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f13])).
% 3.01/1.00  
% 3.01/1.00  fof(f14,axiom,(
% 3.01/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f48,plain,(
% 3.01/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f14])).
% 3.01/1.00  
% 3.01/1.00  fof(f55,plain,(
% 3.01/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.01/1.00    inference(definition_unfolding,[],[f47,f48])).
% 3.01/1.00  
% 3.01/1.00  fof(f56,plain,(
% 3.01/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.01/1.00    inference(definition_unfolding,[],[f46,f55])).
% 3.01/1.00  
% 3.01/1.00  fof(f57,plain,(
% 3.01/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.01/1.00    inference(definition_unfolding,[],[f45,f56])).
% 3.01/1.00  
% 3.01/1.00  fof(f58,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.01/1.00    inference(definition_unfolding,[],[f44,f57])).
% 3.01/1.00  
% 3.01/1.00  fof(f59,plain,(
% 3.01/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.01/1.00    inference(definition_unfolding,[],[f43,f58])).
% 3.01/1.00  
% 3.01/1.00  fof(f66,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 3.01/1.00    inference(definition_unfolding,[],[f50,f59])).
% 3.01/1.00  
% 3.01/1.00  fof(f7,axiom,(
% 3.01/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f27,plain,(
% 3.01/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.01/1.00    inference(nnf_transformation,[],[f7])).
% 3.01/1.00  
% 3.01/1.00  fof(f41,plain,(
% 3.01/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.01/1.00    inference(cnf_transformation,[],[f27])).
% 3.01/1.00  
% 3.01/1.00  fof(f4,axiom,(
% 3.01/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f37,plain,(
% 3.01/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.01/1.00    inference(cnf_transformation,[],[f4])).
% 3.01/1.00  
% 3.01/1.00  fof(f61,plain,(
% 3.01/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0) )),
% 3.01/1.00    inference(definition_unfolding,[],[f41,f37])).
% 3.01/1.00  
% 3.01/1.00  fof(f52,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f29])).
% 3.01/1.00  
% 3.01/1.00  fof(f64,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.01/1.00    inference(definition_unfolding,[],[f52,f59])).
% 3.01/1.00  
% 3.01/1.00  fof(f40,plain,(
% 3.01/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f27])).
% 3.01/1.00  
% 3.01/1.00  fof(f62,plain,(
% 3.01/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.01/1.00    inference(definition_unfolding,[],[f40,f37])).
% 3.01/1.00  
% 3.01/1.00  fof(f15,axiom,(
% 3.01/1.00    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f23,plain,(
% 3.01/1.00    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 3.01/1.00    inference(ennf_transformation,[],[f15])).
% 3.01/1.00  
% 3.01/1.00  fof(f49,plain,(
% 3.01/1.00    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f23])).
% 3.01/1.00  
% 3.01/1.00  fof(f8,axiom,(
% 3.01/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f42,plain,(
% 3.01/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f8])).
% 3.01/1.00  
% 3.01/1.00  fof(f60,plain,(
% 3.01/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.01/1.00    inference(definition_unfolding,[],[f42,f59])).
% 3.01/1.00  
% 3.01/1.00  fof(f63,plain,(
% 3.01/1.00    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 3.01/1.00    inference(definition_unfolding,[],[f49,f60])).
% 3.01/1.00  
% 3.01/1.00  fof(f17,conjecture,(
% 3.01/1.00    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f18,negated_conjecture,(
% 3.01/1.00    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 3.01/1.00    inference(negated_conjecture,[],[f17])).
% 3.01/1.00  
% 3.01/1.00  fof(f24,plain,(
% 3.01/1.00    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <~> ~r2_hidden(X0,X1))),
% 3.01/1.00    inference(ennf_transformation,[],[f18])).
% 3.01/1.00  
% 3.01/1.00  fof(f30,plain,(
% 3.01/1.00    ? [X0,X1] : ((r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)))),
% 3.01/1.00    inference(nnf_transformation,[],[f24])).
% 3.01/1.00  
% 3.01/1.00  fof(f31,plain,(
% 3.01/1.00    ? [X0,X1] : ((r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0))) => ((r2_hidden(sK1,sK2) | k4_xboole_0(k1_tarski(sK1),sK2) != k1_tarski(sK1)) & (~r2_hidden(sK1,sK2) | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)))),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f32,plain,(
% 3.01/1.00    (r2_hidden(sK1,sK2) | k4_xboole_0(k1_tarski(sK1),sK2) != k1_tarski(sK1)) & (~r2_hidden(sK1,sK2) | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1))),
% 3.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f31])).
% 3.01/1.00  
% 3.01/1.00  fof(f53,plain,(
% 3.01/1.00    ~r2_hidden(sK1,sK2) | k4_xboole_0(k1_tarski(sK1),sK2) = k1_tarski(sK1)),
% 3.01/1.00    inference(cnf_transformation,[],[f32])).
% 3.01/1.00  
% 3.01/1.00  fof(f68,plain,(
% 3.01/1.00    ~r2_hidden(sK1,sK2) | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 3.01/1.00    inference(definition_unfolding,[],[f53,f37,f60,f60])).
% 3.01/1.00  
% 3.01/1.00  fof(f54,plain,(
% 3.01/1.00    r2_hidden(sK1,sK2) | k4_xboole_0(k1_tarski(sK1),sK2) != k1_tarski(sK1)),
% 3.01/1.00    inference(cnf_transformation,[],[f32])).
% 3.01/1.00  
% 3.01/1.00  fof(f67,plain,(
% 3.01/1.00    r2_hidden(sK1,sK2) | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 3.01/1.00    inference(definition_unfolding,[],[f54,f37,f60,f60])).
% 3.01/1.00  
% 3.01/1.00  cnf(c_316,plain,
% 3.01/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.01/1.00      theory(equality) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1579,plain,
% 3.01/1.00      ( ~ r2_hidden(X0,X1)
% 3.01/1.00      | r2_hidden(X2,k3_xboole_0(X3,X4))
% 3.01/1.00      | X2 != X0
% 3.01/1.00      | k3_xboole_0(X3,X4) != X1 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_316]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3098,plain,
% 3.01/1.00      ( ~ r2_hidden(X0,X1)
% 3.01/1.00      | r2_hidden(X2,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))
% 3.01/1.00      | X2 != X0
% 3.01/1.00      | k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) != X1 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_1579]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7364,plain,
% 3.01/1.00      ( ~ r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 3.01/1.00      | r2_hidden(X1,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))
% 3.01/1.00      | X1 != X0
% 3.01/1.00      | k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_3098]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7366,plain,
% 3.01/1.00      ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 3.01/1.00      | r2_hidden(sK1,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))
% 3.01/1.00      | k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 3.01/1.00      | sK1 != sK1 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_7364]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5,plain,
% 3.01/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.01/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_960,plain,
% 3.01/1.00      ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),X1)
% 3.01/1.00      | k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),X1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2643,plain,
% 3.01/1.00      ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),sK2)
% 3.01/1.00      | k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_960]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2645,plain,
% 3.01/1.00      ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)
% 3.01/1.00      | k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_2643]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2,plain,
% 3.01/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.01/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2558,plain,
% 3.01/1.00      ( ~ r2_hidden(X0,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))
% 3.01/1.00      | ~ r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2560,plain,
% 3.01/1.00      ( ~ r2_hidden(sK1,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))
% 3.01/1.00      | ~ r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_2558]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1,plain,
% 3.01/1.00      ( k3_xboole_0(X0,X0) = X0 ),
% 3.01/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4,plain,
% 3.01/1.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_655,plain,
% 3.01/1.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_769,plain,
% 3.01/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1,c_655]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_11,plain,
% 3.01/1.00      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
% 3.01/1.00      | r2_hidden(X0,X2) ),
% 3.01/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_648,plain,
% 3.01/1.00      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != iProver_top
% 3.01/1.00      | r2_hidden(X0,X2) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2046,plain,
% 3.01/1.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_769,c_648]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2047,plain,
% 3.01/1.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.01/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2046]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2049,plain,
% 3.01/1.00      ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_2047]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6,plain,
% 3.01/1.00      ( r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
% 3.01/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1449,plain,
% 3.01/1.00      ( r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)
% 3.01/1.00      | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_9,plain,
% 3.01/1.00      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
% 3.01/1.00      | ~ r2_hidden(X1,X2)
% 3.01/1.00      | ~ r2_hidden(X0,X2) ),
% 3.01/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_795,plain,
% 3.01/1.00      ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),sK2)
% 3.01/1.00      | ~ r2_hidden(X0,sK2)
% 3.01/1.00      | ~ r2_hidden(sK1,sK2) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_797,plain,
% 3.01/1.00      ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)
% 3.01/1.00      | ~ r2_hidden(sK1,sK2) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_795]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_312,plain,( X0 = X0 ),theory(equality) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_326,plain,
% 3.01/1.00      ( sK1 = sK1 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_312]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7,plain,
% 3.01/1.00      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 3.01/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_106,plain,
% 3.01/1.00      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 3.01/1.00      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_8,plain,
% 3.01/1.00      ( r2_hidden(X0,X1)
% 3.01/1.00      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_221,plain,
% 3.01/1.00      ( r2_hidden(X0,X1)
% 3.01/1.00      | X1 != X2
% 3.01/1.00      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X3
% 3.01/1.00      | k5_xboole_0(X3,k3_xboole_0(X3,X2)) = X3 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_106,c_8]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_222,plain,
% 3.01/1.00      ( r2_hidden(X0,X1)
% 3.01/1.00      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_221]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_13,negated_conjecture,
% 3.01/1.00      ( ~ r2_hidden(sK1,sK2)
% 3.01/1.00      | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_110,plain,
% 3.01/1.00      ( ~ r2_hidden(sK1,sK2)
% 3.01/1.00      | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 3.01/1.00      inference(prop_impl,[status(thm)],[c_13]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_252,plain,
% 3.01/1.00      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 3.01/1.00      inference(backward_subsumption_resolution,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_222,c_110]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_12,negated_conjecture,
% 3.01/1.00      ( r2_hidden(sK1,sK2)
% 3.01/1.00      | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(contradiction,plain,
% 3.01/1.00      ( $false ),
% 3.01/1.00      inference(minisat,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_7366,c_2645,c_2560,c_2049,c_1449,c_797,c_326,c_252,
% 3.01/1.00                 c_12]) ).
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  ------                               Statistics
% 3.01/1.00  
% 3.01/1.00  ------ Selected
% 3.01/1.00  
% 3.01/1.00  total_time:                             0.235
% 3.01/1.00  
%------------------------------------------------------------------------------
