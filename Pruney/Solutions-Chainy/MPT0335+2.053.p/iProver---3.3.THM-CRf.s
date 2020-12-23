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
% DateTime   : Thu Dec  3 11:38:33 EST 2020

% Result     : Theorem 15.69s
% Output     : CNFRefutation 15.69s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 216 expanded)
%              Number of clauses        :   57 (  68 expanded)
%              Number of leaves         :   14 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  332 ( 939 expanded)
%              Number of equality atoms :  145 ( 297 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f23,f30])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f25,f30])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK1,sK3) != k1_tarski(sK4)
      & r2_hidden(sK4,sK1)
      & k3_xboole_0(sK2,sK3) = k1_tarski(sK4)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( k3_xboole_0(sK1,sK3) != k1_tarski(sK4)
    & r2_hidden(sK4,sK1)
    & k3_xboole_0(sK2,sK3) = k1_tarski(sK4)
    & r1_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f20])).

fof(f36,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    k3_xboole_0(sK1,sK3) != k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f39,f30,f41])).

fof(f38,plain,(
    r2_hidden(sK4,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    k3_xboole_0(sK2,sK3) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f37,f30,f41])).

cnf(c_196,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6104,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | X0 != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | X1 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_13352,plain,
    ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0)
    | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_6104])).

cnf(c_38416,plain,
    ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | k2_enumset1(sK4,sK4,sK4,sK4) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_13352])).

cnf(c_38417,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38416])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_890,plain,
    ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0)
    | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_15445,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1)))
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1) ),
    inference(instantiation,[status(thm)],[c_890])).

cnf(c_15446,plain,
    ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1))) != iProver_top
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15445])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_612,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0)
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(X0,k4_xboole_0(X0,sK3)))
    | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_12615,plain,
    ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK2)
    | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_12616,plain,
    ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = iProver_top
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK2) != iProver_top
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12615])).

cnf(c_194,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2639,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X1 ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_9856,plain,
    ( X0 != k2_enumset1(sK4,sK4,sK4,sK4)
    | X0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2639])).

cnf(c_11819,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4)
    | k2_enumset1(sK4,sK4,sK4,sK4) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_9856])).

cnf(c_6706,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK2) ),
    inference(instantiation,[status(thm)],[c_890])).

cnf(c_6709,plain,
    ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6706])).

cnf(c_637,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | X1 != k2_enumset1(sK4,sK4,sK4,sK4)
    | X0 != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_804,plain,
    ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0)
    | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | X0 != k2_enumset1(sK4,sK4,sK4,sK4)
    | sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_6256,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1)))
    | sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_6260,plain,
    ( sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1)) != k2_enumset1(sK4,sK4,sK4,sK4)
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6256])).

cnf(c_6133,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_890])).

cnf(c_6134,plain,
    ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6133])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1754,plain,
    ( ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),X0)
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5560,plain,
    ( ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK1)
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1754])).

cnf(c_3624,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_3625,plain,
    ( sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k2_enumset1(sK4,sK4,sK4,sK4)
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3624])).

cnf(c_624,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1)
    | X0 != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_2297,plain,
    ( r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1)
    | X0 != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK1 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_2537,plain,
    ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1)
    | sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK1 ),
    inference(instantiation,[status(thm)],[c_2297])).

cnf(c_2541,plain,
    ( sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK1
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2537])).

cnf(c_193,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1772,plain,
    ( sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_599,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3)
    | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_600,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4)
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3) != iProver_top
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_596,plain,
    ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_597,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4)
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_593,plain,
    ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_594,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4)
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_8,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_572,plain,
    ( r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK1)
    | ~ r2_hidden(sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_204,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_198,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_202,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = k2_enumset1(sK4,sK4,sK4,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_198])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_170,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_171,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK1 ),
    inference(unflattening,[status(thm)],[c_170])).

cnf(c_10,negated_conjecture,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_11,negated_conjecture,
    ( r2_hidden(sK4,sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_12,negated_conjecture,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38417,c_15446,c_12616,c_11819,c_6709,c_6260,c_6134,c_5560,c_3625,c_2541,c_1772,c_600,c_597,c_594,c_572,c_204,c_202,c_171,c_10,c_11,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:01:03 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 15.69/2.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.69/2.50  
% 15.69/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.69/2.50  
% 15.69/2.50  ------  iProver source info
% 15.69/2.50  
% 15.69/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.69/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.69/2.50  git: non_committed_changes: false
% 15.69/2.50  git: last_make_outside_of_git: false
% 15.69/2.50  
% 15.69/2.50  ------ 
% 15.69/2.50  
% 15.69/2.50  ------ Input Options
% 15.69/2.50  
% 15.69/2.50  --out_options                           all
% 15.69/2.50  --tptp_safe_out                         true
% 15.69/2.50  --problem_path                          ""
% 15.69/2.50  --include_path                          ""
% 15.69/2.50  --clausifier                            res/vclausify_rel
% 15.69/2.50  --clausifier_options                    --mode clausify
% 15.69/2.50  --stdin                                 false
% 15.69/2.50  --stats_out                             all
% 15.69/2.50  
% 15.69/2.50  ------ General Options
% 15.69/2.50  
% 15.69/2.50  --fof                                   false
% 15.69/2.50  --time_out_real                         305.
% 15.69/2.50  --time_out_virtual                      -1.
% 15.69/2.50  --symbol_type_check                     false
% 15.69/2.50  --clausify_out                          false
% 15.69/2.50  --sig_cnt_out                           false
% 15.69/2.50  --trig_cnt_out                          false
% 15.69/2.50  --trig_cnt_out_tolerance                1.
% 15.69/2.50  --trig_cnt_out_sk_spl                   false
% 15.69/2.50  --abstr_cl_out                          false
% 15.69/2.50  
% 15.69/2.50  ------ Global Options
% 15.69/2.50  
% 15.69/2.50  --schedule                              default
% 15.69/2.50  --add_important_lit                     false
% 15.69/2.50  --prop_solver_per_cl                    1000
% 15.69/2.50  --min_unsat_core                        false
% 15.69/2.50  --soft_assumptions                      false
% 15.69/2.50  --soft_lemma_size                       3
% 15.69/2.50  --prop_impl_unit_size                   0
% 15.69/2.50  --prop_impl_unit                        []
% 15.69/2.50  --share_sel_clauses                     true
% 15.69/2.50  --reset_solvers                         false
% 15.69/2.50  --bc_imp_inh                            [conj_cone]
% 15.69/2.50  --conj_cone_tolerance                   3.
% 15.69/2.50  --extra_neg_conj                        none
% 15.69/2.50  --large_theory_mode                     true
% 15.69/2.50  --prolific_symb_bound                   200
% 15.69/2.50  --lt_threshold                          2000
% 15.69/2.50  --clause_weak_htbl                      true
% 15.69/2.50  --gc_record_bc_elim                     false
% 15.69/2.50  
% 15.69/2.50  ------ Preprocessing Options
% 15.69/2.50  
% 15.69/2.50  --preprocessing_flag                    true
% 15.69/2.50  --time_out_prep_mult                    0.1
% 15.69/2.50  --splitting_mode                        input
% 15.69/2.50  --splitting_grd                         true
% 15.69/2.50  --splitting_cvd                         false
% 15.69/2.50  --splitting_cvd_svl                     false
% 15.69/2.50  --splitting_nvd                         32
% 15.69/2.50  --sub_typing                            true
% 15.69/2.50  --prep_gs_sim                           true
% 15.69/2.50  --prep_unflatten                        true
% 15.69/2.50  --prep_res_sim                          true
% 15.69/2.50  --prep_upred                            true
% 15.69/2.50  --prep_sem_filter                       exhaustive
% 15.69/2.50  --prep_sem_filter_out                   false
% 15.69/2.50  --pred_elim                             true
% 15.69/2.50  --res_sim_input                         true
% 15.69/2.50  --eq_ax_congr_red                       true
% 15.69/2.50  --pure_diseq_elim                       true
% 15.69/2.50  --brand_transform                       false
% 15.69/2.50  --non_eq_to_eq                          false
% 15.69/2.50  --prep_def_merge                        true
% 15.69/2.50  --prep_def_merge_prop_impl              false
% 15.69/2.50  --prep_def_merge_mbd                    true
% 15.69/2.50  --prep_def_merge_tr_red                 false
% 15.69/2.50  --prep_def_merge_tr_cl                  false
% 15.69/2.50  --smt_preprocessing                     true
% 15.69/2.50  --smt_ac_axioms                         fast
% 15.69/2.50  --preprocessed_out                      false
% 15.69/2.50  --preprocessed_stats                    false
% 15.69/2.50  
% 15.69/2.50  ------ Abstraction refinement Options
% 15.69/2.50  
% 15.69/2.50  --abstr_ref                             []
% 15.69/2.50  --abstr_ref_prep                        false
% 15.69/2.50  --abstr_ref_until_sat                   false
% 15.69/2.50  --abstr_ref_sig_restrict                funpre
% 15.69/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.69/2.50  --abstr_ref_under                       []
% 15.69/2.50  
% 15.69/2.50  ------ SAT Options
% 15.69/2.50  
% 15.69/2.50  --sat_mode                              false
% 15.69/2.50  --sat_fm_restart_options                ""
% 15.69/2.50  --sat_gr_def                            false
% 15.69/2.50  --sat_epr_types                         true
% 15.69/2.50  --sat_non_cyclic_types                  false
% 15.69/2.50  --sat_finite_models                     false
% 15.69/2.50  --sat_fm_lemmas                         false
% 15.69/2.50  --sat_fm_prep                           false
% 15.69/2.50  --sat_fm_uc_incr                        true
% 15.69/2.50  --sat_out_model                         small
% 15.69/2.50  --sat_out_clauses                       false
% 15.69/2.50  
% 15.69/2.50  ------ QBF Options
% 15.69/2.50  
% 15.69/2.50  --qbf_mode                              false
% 15.69/2.50  --qbf_elim_univ                         false
% 15.69/2.50  --qbf_dom_inst                          none
% 15.69/2.50  --qbf_dom_pre_inst                      false
% 15.69/2.50  --qbf_sk_in                             false
% 15.69/2.50  --qbf_pred_elim                         true
% 15.69/2.50  --qbf_split                             512
% 15.69/2.50  
% 15.69/2.50  ------ BMC1 Options
% 15.69/2.50  
% 15.69/2.50  --bmc1_incremental                      false
% 15.69/2.50  --bmc1_axioms                           reachable_all
% 15.69/2.50  --bmc1_min_bound                        0
% 15.69/2.50  --bmc1_max_bound                        -1
% 15.69/2.50  --bmc1_max_bound_default                -1
% 15.69/2.50  --bmc1_symbol_reachability              true
% 15.69/2.50  --bmc1_property_lemmas                  false
% 15.69/2.50  --bmc1_k_induction                      false
% 15.69/2.50  --bmc1_non_equiv_states                 false
% 15.69/2.50  --bmc1_deadlock                         false
% 15.69/2.50  --bmc1_ucm                              false
% 15.69/2.50  --bmc1_add_unsat_core                   none
% 15.69/2.50  --bmc1_unsat_core_children              false
% 15.69/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.69/2.50  --bmc1_out_stat                         full
% 15.69/2.50  --bmc1_ground_init                      false
% 15.69/2.50  --bmc1_pre_inst_next_state              false
% 15.69/2.50  --bmc1_pre_inst_state                   false
% 15.69/2.50  --bmc1_pre_inst_reach_state             false
% 15.69/2.50  --bmc1_out_unsat_core                   false
% 15.69/2.50  --bmc1_aig_witness_out                  false
% 15.69/2.50  --bmc1_verbose                          false
% 15.69/2.50  --bmc1_dump_clauses_tptp                false
% 15.69/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.69/2.50  --bmc1_dump_file                        -
% 15.69/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.69/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.69/2.50  --bmc1_ucm_extend_mode                  1
% 15.69/2.50  --bmc1_ucm_init_mode                    2
% 15.69/2.50  --bmc1_ucm_cone_mode                    none
% 15.69/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.69/2.50  --bmc1_ucm_relax_model                  4
% 15.69/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.69/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.69/2.50  --bmc1_ucm_layered_model                none
% 15.69/2.50  --bmc1_ucm_max_lemma_size               10
% 15.69/2.50  
% 15.69/2.50  ------ AIG Options
% 15.69/2.50  
% 15.69/2.50  --aig_mode                              false
% 15.69/2.50  
% 15.69/2.50  ------ Instantiation Options
% 15.69/2.50  
% 15.69/2.50  --instantiation_flag                    true
% 15.69/2.50  --inst_sos_flag                         false
% 15.69/2.50  --inst_sos_phase                        true
% 15.69/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.69/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.69/2.50  --inst_lit_sel_side                     num_symb
% 15.69/2.50  --inst_solver_per_active                1400
% 15.69/2.50  --inst_solver_calls_frac                1.
% 15.69/2.50  --inst_passive_queue_type               priority_queues
% 15.69/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.69/2.50  --inst_passive_queues_freq              [25;2]
% 15.69/2.50  --inst_dismatching                      true
% 15.69/2.50  --inst_eager_unprocessed_to_passive     true
% 15.69/2.50  --inst_prop_sim_given                   true
% 15.69/2.50  --inst_prop_sim_new                     false
% 15.69/2.50  --inst_subs_new                         false
% 15.69/2.50  --inst_eq_res_simp                      false
% 15.69/2.50  --inst_subs_given                       false
% 15.69/2.50  --inst_orphan_elimination               true
% 15.69/2.50  --inst_learning_loop_flag               true
% 15.69/2.50  --inst_learning_start                   3000
% 15.69/2.50  --inst_learning_factor                  2
% 15.69/2.50  --inst_start_prop_sim_after_learn       3
% 15.69/2.50  --inst_sel_renew                        solver
% 15.69/2.50  --inst_lit_activity_flag                true
% 15.69/2.50  --inst_restr_to_given                   false
% 15.69/2.50  --inst_activity_threshold               500
% 15.69/2.50  --inst_out_proof                        true
% 15.69/2.50  
% 15.69/2.50  ------ Resolution Options
% 15.69/2.50  
% 15.69/2.50  --resolution_flag                       true
% 15.69/2.50  --res_lit_sel                           adaptive
% 15.69/2.50  --res_lit_sel_side                      none
% 15.69/2.50  --res_ordering                          kbo
% 15.69/2.50  --res_to_prop_solver                    active
% 15.69/2.50  --res_prop_simpl_new                    false
% 15.69/2.50  --res_prop_simpl_given                  true
% 15.69/2.50  --res_passive_queue_type                priority_queues
% 15.69/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.69/2.50  --res_passive_queues_freq               [15;5]
% 15.69/2.50  --res_forward_subs                      full
% 15.69/2.50  --res_backward_subs                     full
% 15.69/2.50  --res_forward_subs_resolution           true
% 15.69/2.50  --res_backward_subs_resolution          true
% 15.69/2.50  --res_orphan_elimination                true
% 15.69/2.50  --res_time_limit                        2.
% 15.69/2.50  --res_out_proof                         true
% 15.69/2.50  
% 15.69/2.50  ------ Superposition Options
% 15.69/2.50  
% 15.69/2.50  --superposition_flag                    true
% 15.69/2.50  --sup_passive_queue_type                priority_queues
% 15.69/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.69/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.69/2.50  --demod_completeness_check              fast
% 15.69/2.50  --demod_use_ground                      true
% 15.69/2.50  --sup_to_prop_solver                    passive
% 15.69/2.50  --sup_prop_simpl_new                    true
% 15.69/2.50  --sup_prop_simpl_given                  true
% 15.69/2.50  --sup_fun_splitting                     false
% 15.69/2.50  --sup_smt_interval                      50000
% 15.69/2.50  
% 15.69/2.50  ------ Superposition Simplification Setup
% 15.69/2.50  
% 15.69/2.50  --sup_indices_passive                   []
% 15.69/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.69/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.69/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.69/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.69/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.69/2.50  --sup_full_bw                           [BwDemod]
% 15.69/2.50  --sup_immed_triv                        [TrivRules]
% 15.69/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.69/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.69/2.50  --sup_immed_bw_main                     []
% 15.69/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.69/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.69/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.69/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.69/2.50  
% 15.69/2.50  ------ Combination Options
% 15.69/2.50  
% 15.69/2.50  --comb_res_mult                         3
% 15.69/2.50  --comb_sup_mult                         2
% 15.69/2.50  --comb_inst_mult                        10
% 15.69/2.50  
% 15.69/2.50  ------ Debug Options
% 15.69/2.50  
% 15.69/2.50  --dbg_backtrace                         false
% 15.69/2.50  --dbg_dump_prop_clauses                 false
% 15.69/2.50  --dbg_dump_prop_clauses_file            -
% 15.69/2.50  --dbg_out_stat                          false
% 15.69/2.50  ------ Parsing...
% 15.69/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.69/2.50  
% 15.69/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.69/2.50  
% 15.69/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.69/2.50  
% 15.69/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.69/2.50  ------ Proving...
% 15.69/2.50  ------ Problem Properties 
% 15.69/2.50  
% 15.69/2.50  
% 15.69/2.50  clauses                                 14
% 15.69/2.50  conjectures                             4
% 15.69/2.50  EPR                                     2
% 15.69/2.50  Horn                                    12
% 15.69/2.50  unary                                   5
% 15.69/2.50  binary                                  5
% 15.69/2.50  lits                                    28
% 15.69/2.50  lits eq                                 7
% 15.69/2.50  fd_pure                                 0
% 15.69/2.50  fd_pseudo                               0
% 15.69/2.50  fd_cond                                 0
% 15.69/2.50  fd_pseudo_cond                          3
% 15.69/2.50  AC symbols                              0
% 15.69/2.50  
% 15.69/2.50  ------ Schedule dynamic 5 is on 
% 15.69/2.50  
% 15.69/2.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.69/2.50  
% 15.69/2.50  
% 15.69/2.50  ------ 
% 15.69/2.50  Current options:
% 15.69/2.50  ------ 
% 15.69/2.50  
% 15.69/2.50  ------ Input Options
% 15.69/2.50  
% 15.69/2.50  --out_options                           all
% 15.69/2.50  --tptp_safe_out                         true
% 15.69/2.50  --problem_path                          ""
% 15.69/2.50  --include_path                          ""
% 15.69/2.50  --clausifier                            res/vclausify_rel
% 15.69/2.50  --clausifier_options                    --mode clausify
% 15.69/2.50  --stdin                                 false
% 15.69/2.50  --stats_out                             all
% 15.69/2.50  
% 15.69/2.50  ------ General Options
% 15.69/2.50  
% 15.69/2.50  --fof                                   false
% 15.69/2.50  --time_out_real                         305.
% 15.69/2.50  --time_out_virtual                      -1.
% 15.69/2.50  --symbol_type_check                     false
% 15.69/2.50  --clausify_out                          false
% 15.69/2.50  --sig_cnt_out                           false
% 15.69/2.50  --trig_cnt_out                          false
% 15.69/2.50  --trig_cnt_out_tolerance                1.
% 15.69/2.50  --trig_cnt_out_sk_spl                   false
% 15.69/2.50  --abstr_cl_out                          false
% 15.69/2.50  
% 15.69/2.50  ------ Global Options
% 15.69/2.50  
% 15.69/2.50  --schedule                              default
% 15.69/2.50  --add_important_lit                     false
% 15.69/2.50  --prop_solver_per_cl                    1000
% 15.69/2.50  --min_unsat_core                        false
% 15.69/2.50  --soft_assumptions                      false
% 15.69/2.50  --soft_lemma_size                       3
% 15.69/2.50  --prop_impl_unit_size                   0
% 15.69/2.50  --prop_impl_unit                        []
% 15.69/2.50  --share_sel_clauses                     true
% 15.69/2.50  --reset_solvers                         false
% 15.69/2.50  --bc_imp_inh                            [conj_cone]
% 15.69/2.50  --conj_cone_tolerance                   3.
% 15.69/2.50  --extra_neg_conj                        none
% 15.69/2.50  --large_theory_mode                     true
% 15.69/2.50  --prolific_symb_bound                   200
% 15.69/2.50  --lt_threshold                          2000
% 15.69/2.50  --clause_weak_htbl                      true
% 15.69/2.50  --gc_record_bc_elim                     false
% 15.69/2.50  
% 15.69/2.50  ------ Preprocessing Options
% 15.69/2.50  
% 15.69/2.50  --preprocessing_flag                    true
% 15.69/2.50  --time_out_prep_mult                    0.1
% 15.69/2.50  --splitting_mode                        input
% 15.69/2.50  --splitting_grd                         true
% 15.69/2.50  --splitting_cvd                         false
% 15.69/2.50  --splitting_cvd_svl                     false
% 15.69/2.50  --splitting_nvd                         32
% 15.69/2.50  --sub_typing                            true
% 15.69/2.50  --prep_gs_sim                           true
% 15.69/2.50  --prep_unflatten                        true
% 15.69/2.50  --prep_res_sim                          true
% 15.69/2.50  --prep_upred                            true
% 15.69/2.50  --prep_sem_filter                       exhaustive
% 15.69/2.50  --prep_sem_filter_out                   false
% 15.69/2.50  --pred_elim                             true
% 15.69/2.50  --res_sim_input                         true
% 15.69/2.50  --eq_ax_congr_red                       true
% 15.69/2.50  --pure_diseq_elim                       true
% 15.69/2.50  --brand_transform                       false
% 15.69/2.50  --non_eq_to_eq                          false
% 15.69/2.50  --prep_def_merge                        true
% 15.69/2.50  --prep_def_merge_prop_impl              false
% 15.69/2.50  --prep_def_merge_mbd                    true
% 15.69/2.50  --prep_def_merge_tr_red                 false
% 15.69/2.50  --prep_def_merge_tr_cl                  false
% 15.69/2.50  --smt_preprocessing                     true
% 15.69/2.50  --smt_ac_axioms                         fast
% 15.69/2.50  --preprocessed_out                      false
% 15.69/2.50  --preprocessed_stats                    false
% 15.69/2.50  
% 15.69/2.50  ------ Abstraction refinement Options
% 15.69/2.50  
% 15.69/2.50  --abstr_ref                             []
% 15.69/2.50  --abstr_ref_prep                        false
% 15.69/2.50  --abstr_ref_until_sat                   false
% 15.69/2.50  --abstr_ref_sig_restrict                funpre
% 15.69/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.69/2.50  --abstr_ref_under                       []
% 15.69/2.50  
% 15.69/2.50  ------ SAT Options
% 15.69/2.50  
% 15.69/2.50  --sat_mode                              false
% 15.69/2.50  --sat_fm_restart_options                ""
% 15.69/2.50  --sat_gr_def                            false
% 15.69/2.50  --sat_epr_types                         true
% 15.69/2.50  --sat_non_cyclic_types                  false
% 15.69/2.50  --sat_finite_models                     false
% 15.69/2.50  --sat_fm_lemmas                         false
% 15.69/2.50  --sat_fm_prep                           false
% 15.69/2.50  --sat_fm_uc_incr                        true
% 15.69/2.50  --sat_out_model                         small
% 15.69/2.50  --sat_out_clauses                       false
% 15.69/2.50  
% 15.69/2.50  ------ QBF Options
% 15.69/2.50  
% 15.69/2.50  --qbf_mode                              false
% 15.69/2.50  --qbf_elim_univ                         false
% 15.69/2.50  --qbf_dom_inst                          none
% 15.69/2.50  --qbf_dom_pre_inst                      false
% 15.69/2.50  --qbf_sk_in                             false
% 15.69/2.50  --qbf_pred_elim                         true
% 15.69/2.50  --qbf_split                             512
% 15.69/2.50  
% 15.69/2.50  ------ BMC1 Options
% 15.69/2.50  
% 15.69/2.50  --bmc1_incremental                      false
% 15.69/2.50  --bmc1_axioms                           reachable_all
% 15.69/2.50  --bmc1_min_bound                        0
% 15.69/2.50  --bmc1_max_bound                        -1
% 15.69/2.50  --bmc1_max_bound_default                -1
% 15.69/2.50  --bmc1_symbol_reachability              true
% 15.69/2.50  --bmc1_property_lemmas                  false
% 15.69/2.50  --bmc1_k_induction                      false
% 15.69/2.50  --bmc1_non_equiv_states                 false
% 15.69/2.50  --bmc1_deadlock                         false
% 15.69/2.50  --bmc1_ucm                              false
% 15.69/2.50  --bmc1_add_unsat_core                   none
% 15.69/2.50  --bmc1_unsat_core_children              false
% 15.69/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.69/2.50  --bmc1_out_stat                         full
% 15.69/2.50  --bmc1_ground_init                      false
% 15.69/2.50  --bmc1_pre_inst_next_state              false
% 15.69/2.50  --bmc1_pre_inst_state                   false
% 15.69/2.50  --bmc1_pre_inst_reach_state             false
% 15.69/2.50  --bmc1_out_unsat_core                   false
% 15.69/2.50  --bmc1_aig_witness_out                  false
% 15.69/2.50  --bmc1_verbose                          false
% 15.69/2.50  --bmc1_dump_clauses_tptp                false
% 15.69/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.69/2.50  --bmc1_dump_file                        -
% 15.69/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.69/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.69/2.50  --bmc1_ucm_extend_mode                  1
% 15.69/2.50  --bmc1_ucm_init_mode                    2
% 15.69/2.50  --bmc1_ucm_cone_mode                    none
% 15.69/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.69/2.50  --bmc1_ucm_relax_model                  4
% 15.69/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.69/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.69/2.50  --bmc1_ucm_layered_model                none
% 15.69/2.50  --bmc1_ucm_max_lemma_size               10
% 15.69/2.50  
% 15.69/2.50  ------ AIG Options
% 15.69/2.50  
% 15.69/2.50  --aig_mode                              false
% 15.69/2.50  
% 15.69/2.50  ------ Instantiation Options
% 15.69/2.50  
% 15.69/2.50  --instantiation_flag                    true
% 15.69/2.50  --inst_sos_flag                         false
% 15.69/2.50  --inst_sos_phase                        true
% 15.69/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.69/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.69/2.50  --inst_lit_sel_side                     none
% 15.69/2.50  --inst_solver_per_active                1400
% 15.69/2.50  --inst_solver_calls_frac                1.
% 15.69/2.50  --inst_passive_queue_type               priority_queues
% 15.69/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.69/2.50  --inst_passive_queues_freq              [25;2]
% 15.69/2.50  --inst_dismatching                      true
% 15.69/2.50  --inst_eager_unprocessed_to_passive     true
% 15.69/2.50  --inst_prop_sim_given                   true
% 15.69/2.50  --inst_prop_sim_new                     false
% 15.69/2.50  --inst_subs_new                         false
% 15.69/2.50  --inst_eq_res_simp                      false
% 15.69/2.50  --inst_subs_given                       false
% 15.69/2.50  --inst_orphan_elimination               true
% 15.69/2.50  --inst_learning_loop_flag               true
% 15.69/2.50  --inst_learning_start                   3000
% 15.69/2.50  --inst_learning_factor                  2
% 15.69/2.50  --inst_start_prop_sim_after_learn       3
% 15.69/2.50  --inst_sel_renew                        solver
% 15.69/2.50  --inst_lit_activity_flag                true
% 15.69/2.50  --inst_restr_to_given                   false
% 15.69/2.50  --inst_activity_threshold               500
% 15.69/2.50  --inst_out_proof                        true
% 15.69/2.50  
% 15.69/2.50  ------ Resolution Options
% 15.69/2.50  
% 15.69/2.50  --resolution_flag                       false
% 15.69/2.50  --res_lit_sel                           adaptive
% 15.69/2.50  --res_lit_sel_side                      none
% 15.69/2.50  --res_ordering                          kbo
% 15.69/2.50  --res_to_prop_solver                    active
% 15.69/2.50  --res_prop_simpl_new                    false
% 15.69/2.50  --res_prop_simpl_given                  true
% 15.69/2.50  --res_passive_queue_type                priority_queues
% 15.69/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.69/2.50  --res_passive_queues_freq               [15;5]
% 15.69/2.50  --res_forward_subs                      full
% 15.69/2.50  --res_backward_subs                     full
% 15.69/2.50  --res_forward_subs_resolution           true
% 15.69/2.50  --res_backward_subs_resolution          true
% 15.69/2.50  --res_orphan_elimination                true
% 15.69/2.50  --res_time_limit                        2.
% 15.69/2.50  --res_out_proof                         true
% 15.69/2.50  
% 15.69/2.50  ------ Superposition Options
% 15.69/2.50  
% 15.69/2.50  --superposition_flag                    true
% 15.69/2.50  --sup_passive_queue_type                priority_queues
% 15.69/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.69/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.69/2.50  --demod_completeness_check              fast
% 15.69/2.50  --demod_use_ground                      true
% 15.69/2.50  --sup_to_prop_solver                    passive
% 15.69/2.50  --sup_prop_simpl_new                    true
% 15.69/2.50  --sup_prop_simpl_given                  true
% 15.69/2.50  --sup_fun_splitting                     false
% 15.69/2.50  --sup_smt_interval                      50000
% 15.69/2.50  
% 15.69/2.50  ------ Superposition Simplification Setup
% 15.69/2.50  
% 15.69/2.50  --sup_indices_passive                   []
% 15.69/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.69/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.69/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.69/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.69/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.69/2.50  --sup_full_bw                           [BwDemod]
% 15.69/2.50  --sup_immed_triv                        [TrivRules]
% 15.69/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.69/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.69/2.50  --sup_immed_bw_main                     []
% 15.69/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.69/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.69/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.69/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.69/2.50  
% 15.69/2.50  ------ Combination Options
% 15.69/2.50  
% 15.69/2.50  --comb_res_mult                         3
% 15.69/2.50  --comb_sup_mult                         2
% 15.69/2.50  --comb_inst_mult                        10
% 15.69/2.50  
% 15.69/2.50  ------ Debug Options
% 15.69/2.50  
% 15.69/2.50  --dbg_backtrace                         false
% 15.69/2.50  --dbg_dump_prop_clauses                 false
% 15.69/2.50  --dbg_dump_prop_clauses_file            -
% 15.69/2.50  --dbg_out_stat                          false
% 15.69/2.50  
% 15.69/2.50  
% 15.69/2.50  
% 15.69/2.50  
% 15.69/2.50  ------ Proving...
% 15.69/2.50  
% 15.69/2.50  
% 15.69/2.50  % SZS status Theorem for theBenchmark.p
% 15.69/2.50  
% 15.69/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.69/2.50  
% 15.69/2.50  fof(f1,axiom,(
% 15.69/2.50    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.69/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.69/2.50  
% 15.69/2.50  fof(f14,plain,(
% 15.69/2.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.69/2.50    inference(nnf_transformation,[],[f1])).
% 15.69/2.50  
% 15.69/2.50  fof(f15,plain,(
% 15.69/2.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.69/2.50    inference(flattening,[],[f14])).
% 15.69/2.50  
% 15.69/2.50  fof(f16,plain,(
% 15.69/2.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.69/2.50    inference(rectify,[],[f15])).
% 15.69/2.50  
% 15.69/2.50  fof(f17,plain,(
% 15.69/2.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 15.69/2.50    introduced(choice_axiom,[])).
% 15.69/2.50  
% 15.69/2.50  fof(f18,plain,(
% 15.69/2.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.69/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 15.69/2.50  
% 15.69/2.50  fof(f23,plain,(
% 15.69/2.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 15.69/2.50    inference(cnf_transformation,[],[f18])).
% 15.69/2.50  
% 15.69/2.50  fof(f4,axiom,(
% 15.69/2.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.69/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.69/2.50  
% 15.69/2.50  fof(f30,plain,(
% 15.69/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.69/2.50    inference(cnf_transformation,[],[f4])).
% 15.69/2.50  
% 15.69/2.50  fof(f46,plain,(
% 15.69/2.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 15.69/2.50    inference(definition_unfolding,[],[f23,f30])).
% 15.69/2.50  
% 15.69/2.50  fof(f55,plain,(
% 15.69/2.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 15.69/2.50    inference(equality_resolution,[],[f46])).
% 15.69/2.50  
% 15.69/2.50  fof(f24,plain,(
% 15.69/2.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 15.69/2.50    inference(cnf_transformation,[],[f18])).
% 15.69/2.50  
% 15.69/2.50  fof(f45,plain,(
% 15.69/2.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 15.69/2.50    inference(definition_unfolding,[],[f24,f30])).
% 15.69/2.50  
% 15.69/2.50  fof(f54,plain,(
% 15.69/2.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 15.69/2.50    inference(equality_resolution,[],[f45])).
% 15.69/2.50  
% 15.69/2.50  fof(f3,axiom,(
% 15.69/2.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.69/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.69/2.50  
% 15.69/2.50  fof(f11,plain,(
% 15.69/2.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.69/2.50    inference(ennf_transformation,[],[f3])).
% 15.69/2.50  
% 15.69/2.50  fof(f29,plain,(
% 15.69/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.69/2.50    inference(cnf_transformation,[],[f11])).
% 15.69/2.50  
% 15.69/2.50  fof(f49,plain,(
% 15.69/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 15.69/2.50    inference(definition_unfolding,[],[f29,f30])).
% 15.69/2.50  
% 15.69/2.50  fof(f27,plain,(
% 15.69/2.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.69/2.50    inference(cnf_transformation,[],[f18])).
% 15.69/2.50  
% 15.69/2.50  fof(f42,plain,(
% 15.69/2.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.69/2.50    inference(definition_unfolding,[],[f27,f30])).
% 15.69/2.50  
% 15.69/2.50  fof(f25,plain,(
% 15.69/2.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.69/2.50    inference(cnf_transformation,[],[f18])).
% 15.69/2.50  
% 15.69/2.50  fof(f44,plain,(
% 15.69/2.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.69/2.50    inference(definition_unfolding,[],[f25,f30])).
% 15.69/2.50  
% 15.69/2.50  fof(f26,plain,(
% 15.69/2.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.69/2.50    inference(cnf_transformation,[],[f18])).
% 15.69/2.50  
% 15.69/2.50  fof(f43,plain,(
% 15.69/2.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.69/2.50    inference(definition_unfolding,[],[f26,f30])).
% 15.69/2.50  
% 15.69/2.50  fof(f8,axiom,(
% 15.69/2.50    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 15.69/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.69/2.50  
% 15.69/2.50  fof(f19,plain,(
% 15.69/2.50    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 15.69/2.50    inference(nnf_transformation,[],[f8])).
% 15.69/2.50  
% 15.69/2.50  fof(f35,plain,(
% 15.69/2.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 15.69/2.50    inference(cnf_transformation,[],[f19])).
% 15.69/2.50  
% 15.69/2.50  fof(f5,axiom,(
% 15.69/2.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.69/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.69/2.50  
% 15.69/2.50  fof(f31,plain,(
% 15.69/2.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.69/2.50    inference(cnf_transformation,[],[f5])).
% 15.69/2.50  
% 15.69/2.50  fof(f6,axiom,(
% 15.69/2.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.69/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.69/2.50  
% 15.69/2.50  fof(f32,plain,(
% 15.69/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.69/2.50    inference(cnf_transformation,[],[f6])).
% 15.69/2.50  
% 15.69/2.50  fof(f7,axiom,(
% 15.69/2.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.69/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.69/2.50  
% 15.69/2.50  fof(f33,plain,(
% 15.69/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.69/2.50    inference(cnf_transformation,[],[f7])).
% 15.69/2.50  
% 15.69/2.50  fof(f40,plain,(
% 15.69/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 15.69/2.50    inference(definition_unfolding,[],[f32,f33])).
% 15.69/2.50  
% 15.69/2.50  fof(f41,plain,(
% 15.69/2.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 15.69/2.50    inference(definition_unfolding,[],[f31,f40])).
% 15.69/2.50  
% 15.69/2.50  fof(f50,plain,(
% 15.69/2.50    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 15.69/2.50    inference(definition_unfolding,[],[f35,f41])).
% 15.69/2.50  
% 15.69/2.50  fof(f9,conjecture,(
% 15.69/2.50    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 15.69/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.69/2.50  
% 15.69/2.50  fof(f10,negated_conjecture,(
% 15.69/2.50    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 15.69/2.50    inference(negated_conjecture,[],[f9])).
% 15.69/2.50  
% 15.69/2.50  fof(f12,plain,(
% 15.69/2.50    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 15.69/2.50    inference(ennf_transformation,[],[f10])).
% 15.69/2.50  
% 15.69/2.50  fof(f13,plain,(
% 15.69/2.50    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 15.69/2.50    inference(flattening,[],[f12])).
% 15.69/2.50  
% 15.69/2.50  fof(f20,plain,(
% 15.69/2.50    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK1,sK3) != k1_tarski(sK4) & r2_hidden(sK4,sK1) & k3_xboole_0(sK2,sK3) = k1_tarski(sK4) & r1_tarski(sK1,sK2))),
% 15.69/2.50    introduced(choice_axiom,[])).
% 15.69/2.50  
% 15.69/2.50  fof(f21,plain,(
% 15.69/2.50    k3_xboole_0(sK1,sK3) != k1_tarski(sK4) & r2_hidden(sK4,sK1) & k3_xboole_0(sK2,sK3) = k1_tarski(sK4) & r1_tarski(sK1,sK2)),
% 15.69/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f20])).
% 15.69/2.50  
% 15.69/2.50  fof(f36,plain,(
% 15.69/2.50    r1_tarski(sK1,sK2)),
% 15.69/2.50    inference(cnf_transformation,[],[f21])).
% 15.69/2.50  
% 15.69/2.50  fof(f39,plain,(
% 15.69/2.50    k3_xboole_0(sK1,sK3) != k1_tarski(sK4)),
% 15.69/2.50    inference(cnf_transformation,[],[f21])).
% 15.69/2.50  
% 15.69/2.50  fof(f52,plain,(
% 15.69/2.50    k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k2_enumset1(sK4,sK4,sK4,sK4)),
% 15.69/2.50    inference(definition_unfolding,[],[f39,f30,f41])).
% 15.69/2.50  
% 15.69/2.50  fof(f38,plain,(
% 15.69/2.50    r2_hidden(sK4,sK1)),
% 15.69/2.50    inference(cnf_transformation,[],[f21])).
% 15.69/2.50  
% 15.69/2.50  fof(f37,plain,(
% 15.69/2.50    k3_xboole_0(sK2,sK3) = k1_tarski(sK4)),
% 15.69/2.50    inference(cnf_transformation,[],[f21])).
% 15.69/2.50  
% 15.69/2.50  fof(f53,plain,(
% 15.69/2.50    k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4)),
% 15.69/2.50    inference(definition_unfolding,[],[f37,f30,f41])).
% 15.69/2.50  
% 15.69/2.50  cnf(c_196,plain,
% 15.69/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.69/2.50      theory(equality) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_6104,plain,
% 15.69/2.50      ( r2_hidden(X0,X1)
% 15.69/2.50      | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 15.69/2.50      | X0 != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | X1 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_196]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_13352,plain,
% 15.69/2.50      ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0)
% 15.69/2.50      | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 15.69/2.50      | X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 15.69/2.50      | sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_6104]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_38416,plain,
% 15.69/2.50      ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 15.69/2.50      | k2_enumset1(sK4,sK4,sK4,sK4) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 15.69/2.50      | sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_13352]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_38417,plain,
% 15.69/2.50      ( k2_enumset1(sK4,sK4,sK4,sK4) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 15.69/2.50      | sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
% 15.69/2.50      inference(predicate_to_equality,[status(thm)],[c_38416]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_4,plain,
% 15.69/2.50      ( r2_hidden(X0,X1)
% 15.69/2.50      | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 15.69/2.50      inference(cnf_transformation,[],[f55]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_890,plain,
% 15.69/2.50      ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0)
% 15.69/2.50      | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_4]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_15445,plain,
% 15.69/2.50      ( ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1)))
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_890]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_15446,plain,
% 15.69/2.50      ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1))) != iProver_top
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1) = iProver_top ),
% 15.69/2.50      inference(predicate_to_equality,[status(thm)],[c_15445]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_3,plain,
% 15.69/2.50      ( ~ r2_hidden(X0,X1)
% 15.69/2.50      | ~ r2_hidden(X0,X2)
% 15.69/2.50      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 15.69/2.50      inference(cnf_transformation,[],[f54]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_612,plain,
% 15.69/2.50      ( ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0)
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(X0,k4_xboole_0(X0,sK3)))
% 15.69/2.50      | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_3]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_12615,plain,
% 15.69/2.50      ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 15.69/2.50      | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK2)
% 15.69/2.50      | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_612]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_12616,plain,
% 15.69/2.50      ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = iProver_top
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK2) != iProver_top
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3) != iProver_top ),
% 15.69/2.50      inference(predicate_to_equality,[status(thm)],[c_12615]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_194,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_2639,plain,
% 15.69/2.50      ( X0 != X1
% 15.69/2.50      | X0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 15.69/2.50      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X1 ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_194]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_9856,plain,
% 15.69/2.50      ( X0 != k2_enumset1(sK4,sK4,sK4,sK4)
% 15.69/2.50      | X0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 15.69/2.50      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_2639]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_11819,plain,
% 15.69/2.50      ( k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4)
% 15.69/2.50      | k2_enumset1(sK4,sK4,sK4,sK4) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 15.69/2.50      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_9856]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_6706,plain,
% 15.69/2.50      ( ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK2) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_890]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_6709,plain,
% 15.69/2.50      ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK2) = iProver_top ),
% 15.69/2.50      inference(predicate_to_equality,[status(thm)],[c_6706]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_637,plain,
% 15.69/2.50      ( r2_hidden(X0,X1)
% 15.69/2.50      | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | X1 != k2_enumset1(sK4,sK4,sK4,sK4)
% 15.69/2.50      | X0 != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_196]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_804,plain,
% 15.69/2.50      ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),X0)
% 15.69/2.50      | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | X0 != k2_enumset1(sK4,sK4,sK4,sK4)
% 15.69/2.50      | sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_637]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_6256,plain,
% 15.69/2.50      ( ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1)))
% 15.69/2.50      | sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_804]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_6260,plain,
% 15.69/2.50      ( sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1)) != k2_enumset1(sK4,sK4,sK4,sK4)
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1))) = iProver_top ),
% 15.69/2.50      inference(predicate_to_equality,[status(thm)],[c_6256]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_6133,plain,
% 15.69/2.50      ( ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_890]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_6134,plain,
% 15.69/2.50      ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3) = iProver_top ),
% 15.69/2.50      inference(predicate_to_equality,[status(thm)],[c_6133]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_7,plain,
% 15.69/2.50      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 15.69/2.50      inference(cnf_transformation,[],[f49]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_1754,plain,
% 15.69/2.50      ( ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),X0)
% 15.69/2.50      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_7]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_5560,plain,
% 15.69/2.50      ( ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK1)
% 15.69/2.50      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_1754]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_3624,plain,
% 15.69/2.50      ( ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 15.69/2.50      | sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_804]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_3625,plain,
% 15.69/2.50      ( sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k2_enumset1(sK4,sK4,sK4,sK4)
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = iProver_top ),
% 15.69/2.50      inference(predicate_to_equality,[status(thm)],[c_3624]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_624,plain,
% 15.69/2.50      ( r2_hidden(X0,X1)
% 15.69/2.50      | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1)
% 15.69/2.50      | X0 != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | X1 != sK1 ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_196]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_2297,plain,
% 15.69/2.50      ( r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 15.69/2.50      | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1)
% 15.69/2.50      | X0 != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK1 ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_624]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_2537,plain,
% 15.69/2.50      ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 15.69/2.50      | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1)
% 15.69/2.50      | sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK1 ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_2297]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_2541,plain,
% 15.69/2.50      ( sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK1
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1) != iProver_top ),
% 15.69/2.50      inference(predicate_to_equality,[status(thm)],[c_2537]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_193,plain,( X0 = X0 ),theory(equality) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_1772,plain,
% 15.69/2.50      ( sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_193]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_0,plain,
% 15.69/2.50      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 15.69/2.50      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 15.69/2.50      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 15.69/2.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 15.69/2.50      inference(cnf_transformation,[],[f42]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_599,plain,
% 15.69/2.50      ( ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3)
% 15.69/2.50      | ~ r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1)
% 15.69/2.50      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_0]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_600,plain,
% 15.69/2.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4)
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3) != iProver_top
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1) != iProver_top ),
% 15.69/2.50      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_2,plain,
% 15.69/2.50      ( r2_hidden(sK0(X0,X1,X2),X0)
% 15.69/2.50      | r2_hidden(sK0(X0,X1,X2),X2)
% 15.69/2.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 15.69/2.50      inference(cnf_transformation,[],[f44]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_596,plain,
% 15.69/2.50      ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1)
% 15.69/2.50      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_2]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_597,plain,
% 15.69/2.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4)
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK1) = iProver_top ),
% 15.69/2.50      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_1,plain,
% 15.69/2.50      ( r2_hidden(sK0(X0,X1,X2),X1)
% 15.69/2.50      | r2_hidden(sK0(X0,X1,X2),X2)
% 15.69/2.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 15.69/2.50      inference(cnf_transformation,[],[f43]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_593,plain,
% 15.69/2.50      ( r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3)
% 15.69/2.50      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_1]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_594,plain,
% 15.69/2.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4)
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
% 15.69/2.50      | r2_hidden(sK0(sK1,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK3) = iProver_top ),
% 15.69/2.50      inference(predicate_to_equality,[status(thm)],[c_593]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_8,plain,
% 15.69/2.50      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~ r2_hidden(X0,X1) ),
% 15.69/2.50      inference(cnf_transformation,[],[f50]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_572,plain,
% 15.69/2.50      ( r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK1)
% 15.69/2.50      | ~ r2_hidden(sK4,sK1) ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_8]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_204,plain,
% 15.69/2.50      ( sK4 = sK4 ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_193]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_198,plain,
% 15.69/2.50      ( X0 != X1
% 15.69/2.50      | X2 != X3
% 15.69/2.50      | X4 != X5
% 15.69/2.50      | X6 != X7
% 15.69/2.50      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 15.69/2.50      theory(equality) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_202,plain,
% 15.69/2.50      ( k2_enumset1(sK4,sK4,sK4,sK4) = k2_enumset1(sK4,sK4,sK4,sK4)
% 15.69/2.50      | sK4 != sK4 ),
% 15.69/2.50      inference(instantiation,[status(thm)],[c_198]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_13,negated_conjecture,
% 15.69/2.50      ( r1_tarski(sK1,sK2) ),
% 15.69/2.50      inference(cnf_transformation,[],[f36]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_170,plain,
% 15.69/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | sK2 != X1 | sK1 != X0 ),
% 15.69/2.50      inference(resolution_lifted,[status(thm)],[c_7,c_13]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_171,plain,
% 15.69/2.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK1 ),
% 15.69/2.50      inference(unflattening,[status(thm)],[c_170]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_10,negated_conjecture,
% 15.69/2.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 15.69/2.50      inference(cnf_transformation,[],[f52]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_11,negated_conjecture,
% 15.69/2.50      ( r2_hidden(sK4,sK1) ),
% 15.69/2.50      inference(cnf_transformation,[],[f38]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(c_12,negated_conjecture,
% 15.69/2.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 15.69/2.50      inference(cnf_transformation,[],[f53]) ).
% 15.69/2.50  
% 15.69/2.50  cnf(contradiction,plain,
% 15.69/2.50      ( $false ),
% 15.69/2.50      inference(minisat,
% 15.69/2.50                [status(thm)],
% 15.69/2.50                [c_38417,c_15446,c_12616,c_11819,c_6709,c_6260,c_6134,
% 15.69/2.50                 c_5560,c_3625,c_2541,c_1772,c_600,c_597,c_594,c_572,
% 15.69/2.50                 c_204,c_202,c_171,c_10,c_11,c_12]) ).
% 15.69/2.50  
% 15.69/2.50  
% 15.69/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.69/2.50  
% 15.69/2.50  ------                               Statistics
% 15.69/2.50  
% 15.69/2.50  ------ General
% 15.69/2.50  
% 15.69/2.50  abstr_ref_over_cycles:                  0
% 15.69/2.50  abstr_ref_under_cycles:                 0
% 15.69/2.50  gc_basic_clause_elim:                   0
% 15.69/2.50  forced_gc_time:                         0
% 15.69/2.50  parsing_time:                           0.007
% 15.69/2.50  unif_index_cands_time:                  0.
% 15.69/2.50  unif_index_add_time:                    0.
% 15.69/2.50  orderings_time:                         0.
% 15.69/2.50  out_proof_time:                         0.012
% 15.69/2.50  total_time:                             1.837
% 15.69/2.50  num_of_symbols:                         40
% 15.69/2.50  num_of_terms:                           81298
% 15.69/2.50  
% 15.69/2.50  ------ Preprocessing
% 15.69/2.50  
% 15.69/2.50  num_of_splits:                          0
% 15.69/2.50  num_of_split_atoms:                     0
% 15.69/2.50  num_of_reused_defs:                     0
% 15.69/2.50  num_eq_ax_congr_red:                    6
% 15.69/2.50  num_of_sem_filtered_clauses:            1
% 15.69/2.50  num_of_subtypes:                        0
% 15.69/2.50  monotx_restored_types:                  0
% 15.69/2.50  sat_num_of_epr_types:                   0
% 15.69/2.50  sat_num_of_non_cyclic_types:            0
% 15.69/2.50  sat_guarded_non_collapsed_types:        0
% 15.69/2.50  num_pure_diseq_elim:                    0
% 15.69/2.50  simp_replaced_by:                       0
% 15.69/2.50  res_preprocessed:                       55
% 15.69/2.50  prep_upred:                             0
% 15.69/2.50  prep_unflattend:                        5
% 15.69/2.50  smt_new_axioms:                         0
% 15.69/2.50  pred_elim_cands:                        2
% 15.69/2.50  pred_elim:                              0
% 15.69/2.50  pred_elim_cl:                           0
% 15.69/2.50  pred_elim_cycles:                       1
% 15.69/2.50  merged_defs:                            6
% 15.69/2.50  merged_defs_ncl:                        0
% 15.69/2.50  bin_hyper_res:                          6
% 15.69/2.50  prep_cycles:                            3
% 15.69/2.50  pred_elim_time:                         0.
% 15.69/2.50  splitting_time:                         0.
% 15.69/2.50  sem_filter_time:                        0.
% 15.69/2.50  monotx_time:                            0.
% 15.69/2.50  subtype_inf_time:                       0.
% 15.69/2.50  
% 15.69/2.50  ------ Problem properties
% 15.69/2.50  
% 15.69/2.50  clauses:                                14
% 15.69/2.50  conjectures:                            4
% 15.69/2.50  epr:                                    2
% 15.69/2.50  horn:                                   12
% 15.69/2.50  ground:                                 4
% 15.69/2.50  unary:                                  5
% 15.69/2.50  binary:                                 5
% 15.69/2.50  lits:                                   28
% 15.69/2.50  lits_eq:                                7
% 15.69/2.50  fd_pure:                                0
% 15.69/2.50  fd_pseudo:                              0
% 15.69/2.50  fd_cond:                                0
% 15.69/2.50  fd_pseudo_cond:                         3
% 15.69/2.50  ac_symbols:                             0
% 15.69/2.50  
% 15.69/2.50  ------ Propositional Solver
% 15.69/2.50  
% 15.69/2.50  prop_solver_calls:                      27
% 15.69/2.50  prop_fast_solver_calls:                 830
% 15.69/2.50  smt_solver_calls:                       0
% 15.69/2.50  smt_fast_solver_calls:                  0
% 15.69/2.50  prop_num_of_clauses:                    19648
% 15.69/2.50  prop_preprocess_simplified:             16923
% 15.69/2.50  prop_fo_subsumed:                       1
% 15.69/2.50  prop_solver_time:                       0.
% 15.69/2.50  smt_solver_time:                        0.
% 15.69/2.50  smt_fast_solver_time:                   0.
% 15.69/2.50  prop_fast_solver_time:                  0.
% 15.69/2.50  prop_unsat_core_time:                   0.003
% 15.69/2.50  
% 15.69/2.50  ------ QBF
% 15.69/2.50  
% 15.69/2.50  qbf_q_res:                              0
% 15.69/2.50  qbf_num_tautologies:                    0
% 15.69/2.50  qbf_prep_cycles:                        0
% 15.69/2.50  
% 15.69/2.50  ------ BMC1
% 15.69/2.50  
% 15.69/2.50  bmc1_current_bound:                     -1
% 15.69/2.50  bmc1_last_solved_bound:                 -1
% 15.69/2.50  bmc1_unsat_core_size:                   -1
% 15.69/2.50  bmc1_unsat_core_parents_size:           -1
% 15.69/2.50  bmc1_merge_next_fun:                    0
% 15.69/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.69/2.50  
% 15.69/2.50  ------ Instantiation
% 15.69/2.50  
% 15.69/2.50  inst_num_of_clauses:                    2808
% 15.69/2.50  inst_num_in_passive:                    679
% 15.69/2.50  inst_num_in_active:                     947
% 15.69/2.50  inst_num_in_unprocessed:                1182
% 15.69/2.50  inst_num_of_loops:                      1320
% 15.69/2.50  inst_num_of_learning_restarts:          0
% 15.69/2.50  inst_num_moves_active_passive:          369
% 15.69/2.50  inst_lit_activity:                      0
% 15.69/2.50  inst_lit_activity_moves:                0
% 15.69/2.50  inst_num_tautologies:                   0
% 15.69/2.50  inst_num_prop_implied:                  0
% 15.69/2.50  inst_num_existing_simplified:           0
% 15.69/2.50  inst_num_eq_res_simplified:             0
% 15.69/2.50  inst_num_child_elim:                    0
% 15.69/2.50  inst_num_of_dismatching_blockings:      5413
% 15.69/2.50  inst_num_of_non_proper_insts:           3303
% 15.69/2.50  inst_num_of_duplicates:                 0
% 15.69/2.50  inst_inst_num_from_inst_to_res:         0
% 15.69/2.50  inst_dismatching_checking_time:         0.
% 15.69/2.50  
% 15.69/2.50  ------ Resolution
% 15.69/2.50  
% 15.69/2.50  res_num_of_clauses:                     0
% 15.69/2.50  res_num_in_passive:                     0
% 15.69/2.50  res_num_in_active:                      0
% 15.69/2.50  res_num_of_loops:                       58
% 15.69/2.50  res_forward_subset_subsumed:            144
% 15.69/2.50  res_backward_subset_subsumed:           0
% 15.69/2.50  res_forward_subsumed:                   0
% 15.69/2.50  res_backward_subsumed:                  0
% 15.69/2.50  res_forward_subsumption_resolution:     0
% 15.69/2.50  res_backward_subsumption_resolution:    0
% 15.69/2.50  res_clause_to_clause_subsumption:       30735
% 15.69/2.50  res_orphan_elimination:                 0
% 15.69/2.50  res_tautology_del:                      104
% 15.69/2.50  res_num_eq_res_simplified:              0
% 15.69/2.50  res_num_sel_changes:                    0
% 15.69/2.50  res_moves_from_active_to_pass:          0
% 15.69/2.50  
% 15.69/2.50  ------ Superposition
% 15.69/2.50  
% 15.69/2.50  sup_time_total:                         0.
% 15.69/2.50  sup_time_generating:                    0.
% 15.69/2.50  sup_time_sim_full:                      0.
% 15.69/2.50  sup_time_sim_immed:                     0.
% 15.69/2.50  
% 15.69/2.50  sup_num_of_clauses:                     3545
% 15.69/2.50  sup_num_in_active:                      257
% 15.69/2.50  sup_num_in_passive:                     3288
% 15.69/2.50  sup_num_of_loops:                       262
% 15.69/2.50  sup_fw_superposition:                   3755
% 15.69/2.50  sup_bw_superposition:                   3059
% 15.69/2.50  sup_immediate_simplified:               3320
% 15.69/2.50  sup_given_eliminated:                   0
% 15.69/2.50  comparisons_done:                       0
% 15.69/2.50  comparisons_avoided:                    0
% 15.69/2.50  
% 15.69/2.50  ------ Simplifications
% 15.69/2.50  
% 15.69/2.50  
% 15.69/2.50  sim_fw_subset_subsumed:                 98
% 15.69/2.50  sim_bw_subset_subsumed:                 3
% 15.69/2.50  sim_fw_subsumed:                        1335
% 15.69/2.50  sim_bw_subsumed:                        42
% 15.69/2.50  sim_fw_subsumption_res:                 3
% 15.69/2.50  sim_bw_subsumption_res:                 0
% 15.69/2.50  sim_tautology_del:                      64
% 15.69/2.50  sim_eq_tautology_del:                   119
% 15.69/2.50  sim_eq_res_simp:                        3
% 15.69/2.50  sim_fw_demodulated:                     2251
% 15.69/2.50  sim_bw_demodulated:                     62
% 15.69/2.50  sim_light_normalised:                   416
% 15.69/2.50  sim_joinable_taut:                      0
% 15.69/2.50  sim_joinable_simp:                      0
% 15.69/2.50  sim_ac_normalised:                      0
% 15.69/2.50  sim_smt_subsumption:                    0
% 15.69/2.50  
%------------------------------------------------------------------------------
