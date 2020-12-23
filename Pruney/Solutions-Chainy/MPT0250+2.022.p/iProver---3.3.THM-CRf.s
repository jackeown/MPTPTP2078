%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:46 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 142 expanded)
%              Number of clauses        :   29 (  29 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   16
%              Number of atoms          :  268 ( 421 expanded)
%              Number of equality atoms :  138 ( 257 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f57])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f59])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f41,f57,f57])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK2,sK3)
      & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r2_hidden(sK2,sK3)
    & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f29])).

fof(f55,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f74,plain,(
    r1_tarski(k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),sK3)),sK3) ),
    inference(definition_unfolding,[],[f55,f58,f59])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f40,f58])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f39,f58])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f45,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f45,f52])).

fof(f77,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f69])).

fof(f78,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f77])).

fof(f1,axiom,(
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

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f20])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f43,f52])).

fof(f81,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f71])).

fof(f82,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f81])).

fof(f56,plain,(
    ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_702,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),sK3)),sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_700,plain,
    ( r1_tarski(k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),sK3)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1008,plain,
    ( r1_tarski(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10,c_700])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_716,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1723,plain,
    ( k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2))) = sK3
    | r1_tarski(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1008,c_716])).

cnf(c_9,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_711,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1862,plain,
    ( k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2))) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1723,c_711])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_714,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1865,plain,
    ( r1_xboole_0(X0,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1862,c_714])).

cnf(c_15,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_706,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_719,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2294,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(X1,k2_enumset1(X2,X2,X3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_706,c_719])).

cnf(c_2980,plain,
    ( r2_hidden(sK2,X0) != iProver_top
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1865,c_2294])).

cnf(c_3003,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(sK2,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_702,c_2980])).

cnf(c_3005,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3003])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_30,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_32,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_23,plain,
    ( r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3005,c_32,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:17:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.95/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/0.98  
% 1.95/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.95/0.98  
% 1.95/0.98  ------  iProver source info
% 1.95/0.98  
% 1.95/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.95/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.95/0.98  git: non_committed_changes: false
% 1.95/0.98  git: last_make_outside_of_git: false
% 1.95/0.98  
% 1.95/0.98  ------ 
% 1.95/0.98  
% 1.95/0.98  ------ Input Options
% 1.95/0.98  
% 1.95/0.98  --out_options                           all
% 1.95/0.98  --tptp_safe_out                         true
% 1.95/0.98  --problem_path                          ""
% 1.95/0.98  --include_path                          ""
% 1.95/0.98  --clausifier                            res/vclausify_rel
% 1.95/0.98  --clausifier_options                    --mode clausify
% 1.95/0.98  --stdin                                 false
% 1.95/0.98  --stats_out                             all
% 1.95/0.98  
% 1.95/0.98  ------ General Options
% 1.95/0.98  
% 1.95/0.98  --fof                                   false
% 1.95/0.98  --time_out_real                         305.
% 1.95/0.98  --time_out_virtual                      -1.
% 1.95/0.98  --symbol_type_check                     false
% 1.95/0.98  --clausify_out                          false
% 1.95/0.98  --sig_cnt_out                           false
% 1.95/0.98  --trig_cnt_out                          false
% 1.95/0.98  --trig_cnt_out_tolerance                1.
% 1.95/0.98  --trig_cnt_out_sk_spl                   false
% 1.95/0.98  --abstr_cl_out                          false
% 1.95/0.98  
% 1.95/0.98  ------ Global Options
% 1.95/0.98  
% 1.95/0.98  --schedule                              default
% 1.95/0.98  --add_important_lit                     false
% 1.95/0.98  --prop_solver_per_cl                    1000
% 1.95/0.98  --min_unsat_core                        false
% 1.95/0.98  --soft_assumptions                      false
% 1.95/0.98  --soft_lemma_size                       3
% 1.95/0.98  --prop_impl_unit_size                   0
% 1.95/0.98  --prop_impl_unit                        []
% 1.95/0.98  --share_sel_clauses                     true
% 1.95/0.98  --reset_solvers                         false
% 1.95/0.98  --bc_imp_inh                            [conj_cone]
% 1.95/0.98  --conj_cone_tolerance                   3.
% 1.95/0.98  --extra_neg_conj                        none
% 1.95/0.98  --large_theory_mode                     true
% 1.95/0.98  --prolific_symb_bound                   200
% 1.95/0.98  --lt_threshold                          2000
% 1.95/0.98  --clause_weak_htbl                      true
% 1.95/0.98  --gc_record_bc_elim                     false
% 1.95/0.98  
% 1.95/0.98  ------ Preprocessing Options
% 1.95/0.98  
% 1.95/0.98  --preprocessing_flag                    true
% 1.95/0.98  --time_out_prep_mult                    0.1
% 1.95/0.98  --splitting_mode                        input
% 1.95/0.98  --splitting_grd                         true
% 1.95/0.98  --splitting_cvd                         false
% 1.95/0.98  --splitting_cvd_svl                     false
% 1.95/0.98  --splitting_nvd                         32
% 1.95/0.98  --sub_typing                            true
% 1.95/0.98  --prep_gs_sim                           true
% 1.95/0.98  --prep_unflatten                        true
% 1.95/0.98  --prep_res_sim                          true
% 1.95/0.98  --prep_upred                            true
% 1.95/0.98  --prep_sem_filter                       exhaustive
% 1.95/0.98  --prep_sem_filter_out                   false
% 1.95/0.98  --pred_elim                             true
% 1.95/0.98  --res_sim_input                         true
% 1.95/0.98  --eq_ax_congr_red                       true
% 1.95/0.98  --pure_diseq_elim                       true
% 1.95/0.98  --brand_transform                       false
% 1.95/0.98  --non_eq_to_eq                          false
% 1.95/0.98  --prep_def_merge                        true
% 1.95/0.98  --prep_def_merge_prop_impl              false
% 1.95/0.98  --prep_def_merge_mbd                    true
% 1.95/0.98  --prep_def_merge_tr_red                 false
% 1.95/0.98  --prep_def_merge_tr_cl                  false
% 1.95/0.98  --smt_preprocessing                     true
% 1.95/0.98  --smt_ac_axioms                         fast
% 1.95/0.98  --preprocessed_out                      false
% 1.95/0.98  --preprocessed_stats                    false
% 1.95/0.98  
% 1.95/0.98  ------ Abstraction refinement Options
% 1.95/0.98  
% 1.95/0.98  --abstr_ref                             []
% 1.95/0.98  --abstr_ref_prep                        false
% 1.95/0.98  --abstr_ref_until_sat                   false
% 1.95/0.98  --abstr_ref_sig_restrict                funpre
% 1.95/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.95/0.98  --abstr_ref_under                       []
% 1.95/0.98  
% 1.95/0.98  ------ SAT Options
% 1.95/0.98  
% 1.95/0.98  --sat_mode                              false
% 1.95/0.98  --sat_fm_restart_options                ""
% 1.95/0.98  --sat_gr_def                            false
% 1.95/0.98  --sat_epr_types                         true
% 1.95/0.98  --sat_non_cyclic_types                  false
% 1.95/0.98  --sat_finite_models                     false
% 1.95/0.98  --sat_fm_lemmas                         false
% 1.95/0.98  --sat_fm_prep                           false
% 1.95/0.98  --sat_fm_uc_incr                        true
% 1.95/0.98  --sat_out_model                         small
% 1.95/0.98  --sat_out_clauses                       false
% 1.95/0.98  
% 1.95/0.98  ------ QBF Options
% 1.95/0.98  
% 1.95/0.98  --qbf_mode                              false
% 1.95/0.98  --qbf_elim_univ                         false
% 1.95/0.98  --qbf_dom_inst                          none
% 1.95/0.98  --qbf_dom_pre_inst                      false
% 1.95/0.98  --qbf_sk_in                             false
% 1.95/0.98  --qbf_pred_elim                         true
% 1.95/0.98  --qbf_split                             512
% 1.95/0.98  
% 1.95/0.98  ------ BMC1 Options
% 1.95/0.98  
% 1.95/0.98  --bmc1_incremental                      false
% 1.95/0.98  --bmc1_axioms                           reachable_all
% 1.95/0.98  --bmc1_min_bound                        0
% 1.95/0.98  --bmc1_max_bound                        -1
% 1.95/0.98  --bmc1_max_bound_default                -1
% 1.95/0.98  --bmc1_symbol_reachability              true
% 1.95/0.98  --bmc1_property_lemmas                  false
% 1.95/0.98  --bmc1_k_induction                      false
% 1.95/0.98  --bmc1_non_equiv_states                 false
% 1.95/0.98  --bmc1_deadlock                         false
% 1.95/0.98  --bmc1_ucm                              false
% 1.95/0.98  --bmc1_add_unsat_core                   none
% 1.95/0.98  --bmc1_unsat_core_children              false
% 1.95/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.95/0.98  --bmc1_out_stat                         full
% 1.95/0.98  --bmc1_ground_init                      false
% 1.95/0.98  --bmc1_pre_inst_next_state              false
% 1.95/0.98  --bmc1_pre_inst_state                   false
% 1.95/0.98  --bmc1_pre_inst_reach_state             false
% 1.95/0.98  --bmc1_out_unsat_core                   false
% 1.95/0.98  --bmc1_aig_witness_out                  false
% 1.95/0.98  --bmc1_verbose                          false
% 1.95/0.98  --bmc1_dump_clauses_tptp                false
% 1.95/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.95/0.98  --bmc1_dump_file                        -
% 1.95/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.95/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.95/0.98  --bmc1_ucm_extend_mode                  1
% 1.95/0.98  --bmc1_ucm_init_mode                    2
% 1.95/0.98  --bmc1_ucm_cone_mode                    none
% 1.95/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.95/0.98  --bmc1_ucm_relax_model                  4
% 1.95/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.95/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.95/0.98  --bmc1_ucm_layered_model                none
% 1.95/0.98  --bmc1_ucm_max_lemma_size               10
% 1.95/0.98  
% 1.95/0.98  ------ AIG Options
% 1.95/0.98  
% 1.95/0.98  --aig_mode                              false
% 1.95/0.98  
% 1.95/0.98  ------ Instantiation Options
% 1.95/0.98  
% 1.95/0.98  --instantiation_flag                    true
% 1.95/0.98  --inst_sos_flag                         false
% 1.95/0.98  --inst_sos_phase                        true
% 1.95/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.95/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.95/0.98  --inst_lit_sel_side                     num_symb
% 1.95/0.98  --inst_solver_per_active                1400
% 1.95/0.98  --inst_solver_calls_frac                1.
% 1.95/0.98  --inst_passive_queue_type               priority_queues
% 1.95/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.95/0.98  --inst_passive_queues_freq              [25;2]
% 1.95/0.98  --inst_dismatching                      true
% 1.95/0.98  --inst_eager_unprocessed_to_passive     true
% 1.95/0.98  --inst_prop_sim_given                   true
% 1.95/0.98  --inst_prop_sim_new                     false
% 1.95/0.98  --inst_subs_new                         false
% 1.95/0.98  --inst_eq_res_simp                      false
% 1.95/0.98  --inst_subs_given                       false
% 1.95/0.98  --inst_orphan_elimination               true
% 1.95/0.98  --inst_learning_loop_flag               true
% 1.95/0.98  --inst_learning_start                   3000
% 1.95/0.98  --inst_learning_factor                  2
% 1.95/0.98  --inst_start_prop_sim_after_learn       3
% 1.95/0.98  --inst_sel_renew                        solver
% 1.95/0.98  --inst_lit_activity_flag                true
% 1.95/0.98  --inst_restr_to_given                   false
% 1.95/0.98  --inst_activity_threshold               500
% 1.95/0.98  --inst_out_proof                        true
% 1.95/0.98  
% 1.95/0.98  ------ Resolution Options
% 1.95/0.98  
% 1.95/0.98  --resolution_flag                       true
% 1.95/0.98  --res_lit_sel                           adaptive
% 1.95/0.98  --res_lit_sel_side                      none
% 1.95/0.98  --res_ordering                          kbo
% 1.95/0.98  --res_to_prop_solver                    active
% 1.95/0.98  --res_prop_simpl_new                    false
% 1.95/0.98  --res_prop_simpl_given                  true
% 1.95/0.98  --res_passive_queue_type                priority_queues
% 1.95/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.95/0.98  --res_passive_queues_freq               [15;5]
% 1.95/0.98  --res_forward_subs                      full
% 1.95/0.98  --res_backward_subs                     full
% 1.95/0.98  --res_forward_subs_resolution           true
% 1.95/0.98  --res_backward_subs_resolution          true
% 1.95/0.98  --res_orphan_elimination                true
% 1.95/0.98  --res_time_limit                        2.
% 1.95/0.98  --res_out_proof                         true
% 1.95/0.98  
% 1.95/0.98  ------ Superposition Options
% 1.95/0.98  
% 1.95/0.98  --superposition_flag                    true
% 1.95/0.98  --sup_passive_queue_type                priority_queues
% 1.95/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.95/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.95/0.98  --demod_completeness_check              fast
% 1.95/0.98  --demod_use_ground                      true
% 1.95/0.98  --sup_to_prop_solver                    passive
% 1.95/0.98  --sup_prop_simpl_new                    true
% 1.95/0.98  --sup_prop_simpl_given                  true
% 1.95/0.98  --sup_fun_splitting                     false
% 1.95/0.98  --sup_smt_interval                      50000
% 1.95/0.98  
% 1.95/0.98  ------ Superposition Simplification Setup
% 1.95/0.98  
% 1.95/0.98  --sup_indices_passive                   []
% 1.95/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.95/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_full_bw                           [BwDemod]
% 1.95/0.98  --sup_immed_triv                        [TrivRules]
% 1.95/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.95/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_immed_bw_main                     []
% 1.95/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.95/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/0.98  
% 1.95/0.98  ------ Combination Options
% 1.95/0.98  
% 1.95/0.98  --comb_res_mult                         3
% 1.95/0.98  --comb_sup_mult                         2
% 1.95/0.98  --comb_inst_mult                        10
% 1.95/0.98  
% 1.95/0.98  ------ Debug Options
% 1.95/0.98  
% 1.95/0.98  --dbg_backtrace                         false
% 1.95/0.98  --dbg_dump_prop_clauses                 false
% 1.95/0.98  --dbg_dump_prop_clauses_file            -
% 1.95/0.98  --dbg_out_stat                          false
% 1.95/0.98  ------ Parsing...
% 1.95/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.95/0.98  
% 1.95/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.95/0.98  
% 1.95/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.95/0.98  
% 1.95/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.95/0.98  ------ Proving...
% 1.95/0.98  ------ Problem Properties 
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  clauses                                 21
% 1.95/0.98  conjectures                             2
% 1.95/0.98  EPR                                     4
% 1.95/0.98  Horn                                    16
% 1.95/0.98  unary                                   8
% 1.95/0.98  binary                                  5
% 1.95/0.98  lits                                    45
% 1.95/0.98  lits eq                                 15
% 1.95/0.98  fd_pure                                 0
% 1.95/0.98  fd_pseudo                               0
% 1.95/0.98  fd_cond                                 0
% 1.95/0.98  fd_pseudo_cond                          5
% 1.95/0.98  AC symbols                              0
% 1.95/0.98  
% 1.95/0.98  ------ Schedule dynamic 5 is on 
% 1.95/0.98  
% 1.95/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  ------ 
% 1.95/0.98  Current options:
% 1.95/0.98  ------ 
% 1.95/0.98  
% 1.95/0.98  ------ Input Options
% 1.95/0.98  
% 1.95/0.98  --out_options                           all
% 1.95/0.98  --tptp_safe_out                         true
% 1.95/0.98  --problem_path                          ""
% 1.95/0.98  --include_path                          ""
% 1.95/0.98  --clausifier                            res/vclausify_rel
% 1.95/0.98  --clausifier_options                    --mode clausify
% 1.95/0.98  --stdin                                 false
% 1.95/0.98  --stats_out                             all
% 1.95/0.98  
% 1.95/0.98  ------ General Options
% 1.95/0.98  
% 1.95/0.98  --fof                                   false
% 1.95/0.98  --time_out_real                         305.
% 1.95/0.98  --time_out_virtual                      -1.
% 1.95/0.98  --symbol_type_check                     false
% 1.95/0.98  --clausify_out                          false
% 1.95/0.98  --sig_cnt_out                           false
% 1.95/0.98  --trig_cnt_out                          false
% 1.95/0.98  --trig_cnt_out_tolerance                1.
% 1.95/0.98  --trig_cnt_out_sk_spl                   false
% 1.95/0.98  --abstr_cl_out                          false
% 1.95/0.98  
% 1.95/0.98  ------ Global Options
% 1.95/0.98  
% 1.95/0.98  --schedule                              default
% 1.95/0.98  --add_important_lit                     false
% 1.95/0.98  --prop_solver_per_cl                    1000
% 1.95/0.98  --min_unsat_core                        false
% 1.95/0.98  --soft_assumptions                      false
% 1.95/0.98  --soft_lemma_size                       3
% 1.95/0.98  --prop_impl_unit_size                   0
% 1.95/0.98  --prop_impl_unit                        []
% 1.95/0.98  --share_sel_clauses                     true
% 1.95/0.98  --reset_solvers                         false
% 1.95/0.98  --bc_imp_inh                            [conj_cone]
% 1.95/0.98  --conj_cone_tolerance                   3.
% 1.95/0.98  --extra_neg_conj                        none
% 1.95/0.98  --large_theory_mode                     true
% 1.95/0.98  --prolific_symb_bound                   200
% 1.95/0.98  --lt_threshold                          2000
% 1.95/0.98  --clause_weak_htbl                      true
% 1.95/0.98  --gc_record_bc_elim                     false
% 1.95/0.98  
% 1.95/0.98  ------ Preprocessing Options
% 1.95/0.98  
% 1.95/0.98  --preprocessing_flag                    true
% 1.95/0.98  --time_out_prep_mult                    0.1
% 1.95/0.98  --splitting_mode                        input
% 1.95/0.98  --splitting_grd                         true
% 1.95/0.98  --splitting_cvd                         false
% 1.95/0.98  --splitting_cvd_svl                     false
% 1.95/0.98  --splitting_nvd                         32
% 1.95/0.98  --sub_typing                            true
% 1.95/0.98  --prep_gs_sim                           true
% 1.95/0.98  --prep_unflatten                        true
% 1.95/0.98  --prep_res_sim                          true
% 1.95/0.98  --prep_upred                            true
% 1.95/0.98  --prep_sem_filter                       exhaustive
% 1.95/0.98  --prep_sem_filter_out                   false
% 1.95/0.98  --pred_elim                             true
% 1.95/0.98  --res_sim_input                         true
% 1.95/0.98  --eq_ax_congr_red                       true
% 1.95/0.98  --pure_diseq_elim                       true
% 1.95/0.98  --brand_transform                       false
% 1.95/0.98  --non_eq_to_eq                          false
% 1.95/0.98  --prep_def_merge                        true
% 1.95/0.98  --prep_def_merge_prop_impl              false
% 1.95/0.98  --prep_def_merge_mbd                    true
% 1.95/0.98  --prep_def_merge_tr_red                 false
% 1.95/0.98  --prep_def_merge_tr_cl                  false
% 1.95/0.98  --smt_preprocessing                     true
% 1.95/0.98  --smt_ac_axioms                         fast
% 1.95/0.98  --preprocessed_out                      false
% 1.95/0.98  --preprocessed_stats                    false
% 1.95/0.98  
% 1.95/0.98  ------ Abstraction refinement Options
% 1.95/0.98  
% 1.95/0.98  --abstr_ref                             []
% 1.95/0.98  --abstr_ref_prep                        false
% 1.95/0.98  --abstr_ref_until_sat                   false
% 1.95/0.98  --abstr_ref_sig_restrict                funpre
% 1.95/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.95/0.98  --abstr_ref_under                       []
% 1.95/0.98  
% 1.95/0.98  ------ SAT Options
% 1.95/0.98  
% 1.95/0.98  --sat_mode                              false
% 1.95/0.98  --sat_fm_restart_options                ""
% 1.95/0.98  --sat_gr_def                            false
% 1.95/0.98  --sat_epr_types                         true
% 1.95/0.98  --sat_non_cyclic_types                  false
% 1.95/0.98  --sat_finite_models                     false
% 1.95/0.98  --sat_fm_lemmas                         false
% 1.95/0.98  --sat_fm_prep                           false
% 1.95/0.98  --sat_fm_uc_incr                        true
% 1.95/0.98  --sat_out_model                         small
% 1.95/0.98  --sat_out_clauses                       false
% 1.95/0.98  
% 1.95/0.98  ------ QBF Options
% 1.95/0.98  
% 1.95/0.98  --qbf_mode                              false
% 1.95/0.98  --qbf_elim_univ                         false
% 1.95/0.98  --qbf_dom_inst                          none
% 1.95/0.98  --qbf_dom_pre_inst                      false
% 1.95/0.98  --qbf_sk_in                             false
% 1.95/0.98  --qbf_pred_elim                         true
% 1.95/0.98  --qbf_split                             512
% 1.95/0.98  
% 1.95/0.98  ------ BMC1 Options
% 1.95/0.98  
% 1.95/0.98  --bmc1_incremental                      false
% 1.95/0.98  --bmc1_axioms                           reachable_all
% 1.95/0.98  --bmc1_min_bound                        0
% 1.95/0.98  --bmc1_max_bound                        -1
% 1.95/0.98  --bmc1_max_bound_default                -1
% 1.95/0.98  --bmc1_symbol_reachability              true
% 1.95/0.98  --bmc1_property_lemmas                  false
% 1.95/0.98  --bmc1_k_induction                      false
% 1.95/0.98  --bmc1_non_equiv_states                 false
% 1.95/0.98  --bmc1_deadlock                         false
% 1.95/0.98  --bmc1_ucm                              false
% 1.95/0.98  --bmc1_add_unsat_core                   none
% 1.95/0.98  --bmc1_unsat_core_children              false
% 1.95/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.95/0.98  --bmc1_out_stat                         full
% 1.95/0.98  --bmc1_ground_init                      false
% 1.95/0.98  --bmc1_pre_inst_next_state              false
% 1.95/0.98  --bmc1_pre_inst_state                   false
% 1.95/0.98  --bmc1_pre_inst_reach_state             false
% 1.95/0.98  --bmc1_out_unsat_core                   false
% 1.95/0.98  --bmc1_aig_witness_out                  false
% 1.95/0.98  --bmc1_verbose                          false
% 1.95/0.98  --bmc1_dump_clauses_tptp                false
% 1.95/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.95/0.98  --bmc1_dump_file                        -
% 1.95/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.95/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.95/0.98  --bmc1_ucm_extend_mode                  1
% 1.95/0.98  --bmc1_ucm_init_mode                    2
% 1.95/0.98  --bmc1_ucm_cone_mode                    none
% 1.95/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.95/0.98  --bmc1_ucm_relax_model                  4
% 1.95/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.95/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.95/0.98  --bmc1_ucm_layered_model                none
% 1.95/0.98  --bmc1_ucm_max_lemma_size               10
% 1.95/0.98  
% 1.95/0.98  ------ AIG Options
% 1.95/0.98  
% 1.95/0.98  --aig_mode                              false
% 1.95/0.98  
% 1.95/0.98  ------ Instantiation Options
% 1.95/0.98  
% 1.95/0.98  --instantiation_flag                    true
% 1.95/0.98  --inst_sos_flag                         false
% 1.95/0.98  --inst_sos_phase                        true
% 1.95/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.95/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.95/0.98  --inst_lit_sel_side                     none
% 1.95/0.98  --inst_solver_per_active                1400
% 1.95/0.98  --inst_solver_calls_frac                1.
% 1.95/0.98  --inst_passive_queue_type               priority_queues
% 1.95/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.95/0.98  --inst_passive_queues_freq              [25;2]
% 1.95/0.98  --inst_dismatching                      true
% 1.95/0.98  --inst_eager_unprocessed_to_passive     true
% 1.95/0.98  --inst_prop_sim_given                   true
% 1.95/0.98  --inst_prop_sim_new                     false
% 1.95/0.98  --inst_subs_new                         false
% 1.95/0.98  --inst_eq_res_simp                      false
% 1.95/0.98  --inst_subs_given                       false
% 1.95/0.98  --inst_orphan_elimination               true
% 1.95/0.98  --inst_learning_loop_flag               true
% 1.95/0.98  --inst_learning_start                   3000
% 1.95/0.98  --inst_learning_factor                  2
% 1.95/0.98  --inst_start_prop_sim_after_learn       3
% 1.95/0.98  --inst_sel_renew                        solver
% 1.95/0.98  --inst_lit_activity_flag                true
% 1.95/0.98  --inst_restr_to_given                   false
% 1.95/0.98  --inst_activity_threshold               500
% 1.95/0.98  --inst_out_proof                        true
% 1.95/0.98  
% 1.95/0.98  ------ Resolution Options
% 1.95/0.98  
% 1.95/0.98  --resolution_flag                       false
% 1.95/0.98  --res_lit_sel                           adaptive
% 1.95/0.98  --res_lit_sel_side                      none
% 1.95/0.98  --res_ordering                          kbo
% 1.95/0.98  --res_to_prop_solver                    active
% 1.95/0.98  --res_prop_simpl_new                    false
% 1.95/0.98  --res_prop_simpl_given                  true
% 1.95/0.98  --res_passive_queue_type                priority_queues
% 1.95/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.95/0.98  --res_passive_queues_freq               [15;5]
% 1.95/0.98  --res_forward_subs                      full
% 1.95/0.98  --res_backward_subs                     full
% 1.95/0.98  --res_forward_subs_resolution           true
% 1.95/0.98  --res_backward_subs_resolution          true
% 1.95/0.98  --res_orphan_elimination                true
% 1.95/0.98  --res_time_limit                        2.
% 1.95/0.98  --res_out_proof                         true
% 1.95/0.98  
% 1.95/0.98  ------ Superposition Options
% 1.95/0.98  
% 1.95/0.98  --superposition_flag                    true
% 1.95/0.98  --sup_passive_queue_type                priority_queues
% 1.95/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.95/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.95/0.98  --demod_completeness_check              fast
% 1.95/0.98  --demod_use_ground                      true
% 1.95/0.98  --sup_to_prop_solver                    passive
% 1.95/0.98  --sup_prop_simpl_new                    true
% 1.95/0.98  --sup_prop_simpl_given                  true
% 1.95/0.98  --sup_fun_splitting                     false
% 1.95/0.98  --sup_smt_interval                      50000
% 1.95/0.98  
% 1.95/0.98  ------ Superposition Simplification Setup
% 1.95/0.98  
% 1.95/0.98  --sup_indices_passive                   []
% 1.95/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.95/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_full_bw                           [BwDemod]
% 1.95/0.98  --sup_immed_triv                        [TrivRules]
% 1.95/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.95/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_immed_bw_main                     []
% 1.95/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.95/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/0.98  
% 1.95/0.98  ------ Combination Options
% 1.95/0.98  
% 1.95/0.98  --comb_res_mult                         3
% 1.95/0.98  --comb_sup_mult                         2
% 1.95/0.98  --comb_inst_mult                        10
% 1.95/0.98  
% 1.95/0.98  ------ Debug Options
% 1.95/0.98  
% 1.95/0.98  --dbg_backtrace                         false
% 1.95/0.98  --dbg_dump_prop_clauses                 false
% 1.95/0.98  --dbg_dump_prop_clauses_file            -
% 1.95/0.98  --dbg_out_stat                          false
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  ------ Proving...
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  % SZS status Theorem for theBenchmark.p
% 1.95/0.98  
% 1.95/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.95/0.98  
% 1.95/0.98  fof(f10,axiom,(
% 1.95/0.98    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f18,plain,(
% 1.95/0.98    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.95/0.98    inference(ennf_transformation,[],[f10])).
% 1.95/0.98  
% 1.95/0.98  fof(f53,plain,(
% 1.95/0.98    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f18])).
% 1.95/0.98  
% 1.95/0.98  fof(f7,axiom,(
% 1.95/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f50,plain,(
% 1.95/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f7])).
% 1.95/0.98  
% 1.95/0.98  fof(f8,axiom,(
% 1.95/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f51,plain,(
% 1.95/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f8])).
% 1.95/0.98  
% 1.95/0.98  fof(f9,axiom,(
% 1.95/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f52,plain,(
% 1.95/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f9])).
% 1.95/0.98  
% 1.95/0.98  fof(f57,plain,(
% 1.95/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.95/0.98    inference(definition_unfolding,[],[f51,f52])).
% 1.95/0.98  
% 1.95/0.98  fof(f59,plain,(
% 1.95/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.95/0.98    inference(definition_unfolding,[],[f50,f57])).
% 1.95/0.98  
% 1.95/0.98  fof(f73,plain,(
% 1.95/0.98    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.95/0.98    inference(definition_unfolding,[],[f53,f59])).
% 1.95/0.98  
% 1.95/0.98  fof(f5,axiom,(
% 1.95/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f41,plain,(
% 1.95/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f5])).
% 1.95/0.98  
% 1.95/0.98  fof(f64,plain,(
% 1.95/0.98    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.95/0.98    inference(definition_unfolding,[],[f41,f57,f57])).
% 1.95/0.98  
% 1.95/0.98  fof(f12,conjecture,(
% 1.95/0.98    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 1.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f13,negated_conjecture,(
% 1.95/0.98    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 1.95/0.98    inference(negated_conjecture,[],[f12])).
% 1.95/0.98  
% 1.95/0.98  fof(f19,plain,(
% 1.95/0.98    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 1.95/0.98    inference(ennf_transformation,[],[f13])).
% 1.95/0.98  
% 1.95/0.98  fof(f29,plain,(
% 1.95/0.98    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK2,sK3) & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3))),
% 1.95/0.98    introduced(choice_axiom,[])).
% 1.95/0.98  
% 1.95/0.98  fof(f30,plain,(
% 1.95/0.98    ~r2_hidden(sK2,sK3) & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3)),
% 1.95/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f29])).
% 1.95/0.98  
% 1.95/0.98  fof(f55,plain,(
% 1.95/0.98    r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3)),
% 1.95/0.98    inference(cnf_transformation,[],[f30])).
% 1.95/0.98  
% 1.95/0.98  fof(f11,axiom,(
% 1.95/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.95/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f54,plain,(
% 1.95/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.95/0.99    inference(cnf_transformation,[],[f11])).
% 1.95/0.99  
% 1.95/0.99  fof(f58,plain,(
% 1.95/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.95/0.99    inference(definition_unfolding,[],[f54,f57])).
% 1.95/0.99  
% 1.95/0.99  fof(f74,plain,(
% 1.95/0.99    r1_tarski(k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),sK3)),sK3)),
% 1.95/0.99    inference(definition_unfolding,[],[f55,f58,f59])).
% 1.95/0.99  
% 1.95/0.99  fof(f2,axiom,(
% 1.95/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/0.99  
% 1.95/0.99  fof(f22,plain,(
% 1.95/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.95/0.99    inference(nnf_transformation,[],[f2])).
% 1.95/0.99  
% 1.95/0.99  fof(f23,plain,(
% 1.95/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.95/0.99    inference(flattening,[],[f22])).
% 1.95/0.99  
% 1.95/0.99  fof(f36,plain,(
% 1.95/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.95/0.99    inference(cnf_transformation,[],[f23])).
% 1.95/0.99  
% 1.95/0.99  fof(f4,axiom,(
% 1.95/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/0.99  
% 1.95/0.99  fof(f40,plain,(
% 1.95/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.95/0.99    inference(cnf_transformation,[],[f4])).
% 1.95/0.99  
% 1.95/0.99  fof(f63,plain,(
% 1.95/0.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.95/0.99    inference(definition_unfolding,[],[f40,f58])).
% 1.95/0.99  
% 1.95/0.99  fof(f3,axiom,(
% 1.95/0.99    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/0.99  
% 1.95/0.99  fof(f16,plain,(
% 1.95/0.99    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.95/0.99    inference(ennf_transformation,[],[f3])).
% 1.95/0.99  
% 1.95/0.99  fof(f39,plain,(
% 1.95/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.95/0.99    inference(cnf_transformation,[],[f16])).
% 1.95/0.99  
% 1.95/0.99  fof(f60,plain,(
% 1.95/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | r1_xboole_0(X0,X2)) )),
% 1.95/0.99    inference(definition_unfolding,[],[f39,f58])).
% 1.95/0.99  
% 1.95/0.99  fof(f6,axiom,(
% 1.95/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/0.99  
% 1.95/0.99  fof(f17,plain,(
% 1.95/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.95/0.99    inference(ennf_transformation,[],[f6])).
% 1.95/0.99  
% 1.95/0.99  fof(f24,plain,(
% 1.95/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.95/0.99    inference(nnf_transformation,[],[f17])).
% 1.95/0.99  
% 1.95/0.99  fof(f25,plain,(
% 1.95/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.95/0.99    inference(flattening,[],[f24])).
% 1.95/0.99  
% 1.95/0.99  fof(f26,plain,(
% 1.95/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.95/0.99    inference(rectify,[],[f25])).
% 1.95/0.99  
% 1.95/0.99  fof(f27,plain,(
% 1.95/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 1.95/0.99    introduced(choice_axiom,[])).
% 1.95/0.99  
% 1.95/0.99  fof(f28,plain,(
% 1.95/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.95/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 1.95/0.99  
% 1.95/0.99  fof(f45,plain,(
% 1.95/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.95/0.99    inference(cnf_transformation,[],[f28])).
% 1.95/0.99  
% 1.95/0.99  fof(f69,plain,(
% 1.95/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.95/0.99    inference(definition_unfolding,[],[f45,f52])).
% 1.95/0.99  
% 1.95/0.99  fof(f77,plain,(
% 1.95/0.99    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 1.95/0.99    inference(equality_resolution,[],[f69])).
% 1.95/0.99  
% 1.95/0.99  fof(f78,plain,(
% 1.95/0.99    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 1.95/0.99    inference(equality_resolution,[],[f77])).
% 1.95/0.99  
% 1.95/0.99  fof(f1,axiom,(
% 1.95/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.95/0.99  
% 1.95/0.99  fof(f14,plain,(
% 1.95/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.95/0.99    inference(rectify,[],[f1])).
% 1.95/0.99  
% 1.95/0.99  fof(f15,plain,(
% 1.95/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.95/0.99    inference(ennf_transformation,[],[f14])).
% 1.95/0.99  
% 1.95/0.99  fof(f20,plain,(
% 1.95/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.95/0.99    introduced(choice_axiom,[])).
% 1.95/0.99  
% 1.95/0.99  fof(f21,plain,(
% 1.95/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.95/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f20])).
% 1.95/0.99  
% 1.95/0.99  fof(f33,plain,(
% 1.95/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.95/0.99    inference(cnf_transformation,[],[f21])).
% 1.95/0.99  
% 1.95/0.99  fof(f43,plain,(
% 1.95/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.95/0.99    inference(cnf_transformation,[],[f28])).
% 1.95/0.99  
% 1.95/0.99  fof(f71,plain,(
% 1.95/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.95/0.99    inference(definition_unfolding,[],[f43,f52])).
% 1.95/0.99  
% 1.95/0.99  fof(f81,plain,(
% 1.95/0.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 1.95/0.99    inference(equality_resolution,[],[f71])).
% 1.95/0.99  
% 1.95/0.99  fof(f82,plain,(
% 1.95/0.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 1.95/0.99    inference(equality_resolution,[],[f81])).
% 1.95/0.99  
% 1.95/0.99  fof(f56,plain,(
% 1.95/0.99    ~r2_hidden(sK2,sK3)),
% 1.95/0.99    inference(cnf_transformation,[],[f30])).
% 1.95/0.99  
% 1.95/0.99  cnf(c_19,plain,
% 1.95/0.99      ( r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 1.95/0.99      inference(cnf_transformation,[],[f73]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_702,plain,
% 1.95/0.99      ( r2_hidden(X0,X1) = iProver_top
% 1.95/0.99      | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_10,plain,
% 1.95/0.99      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 1.95/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_21,negated_conjecture,
% 1.95/0.99      ( r1_tarski(k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),sK3)),sK3) ),
% 1.95/0.99      inference(cnf_transformation,[],[f74]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_700,plain,
% 1.95/0.99      ( r1_tarski(k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),sK3)),sK3) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_1008,plain,
% 1.95/0.99      ( r1_tarski(k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
% 1.95/0.99      inference(demodulation,[status(thm)],[c_10,c_700]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3,plain,
% 1.95/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.95/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_716,plain,
% 1.95/0.99      ( X0 = X1
% 1.95/0.99      | r1_tarski(X0,X1) != iProver_top
% 1.95/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_1723,plain,
% 1.95/0.99      ( k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2))) = sK3
% 1.95/0.99      | r1_tarski(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top ),
% 1.95/0.99      inference(superposition,[status(thm)],[c_1008,c_716]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_9,plain,
% 1.95/0.99      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_711,plain,
% 1.95/0.99      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_1862,plain,
% 1.95/0.99      ( k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2))) = sK3 ),
% 1.95/0.99      inference(forward_subsumption_resolution,
% 1.95/0.99                [status(thm)],
% 1.95/0.99                [c_1723,c_711]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_6,plain,
% 1.95/0.99      ( r1_xboole_0(X0,X1)
% 1.95/0.99      | ~ r1_xboole_0(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
% 1.95/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_714,plain,
% 1.95/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 1.95/0.99      | r1_xboole_0(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_1865,plain,
% 1.95/0.99      ( r1_xboole_0(X0,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 1.95/0.99      | r1_xboole_0(X0,sK3) != iProver_top ),
% 1.95/0.99      inference(superposition,[status(thm)],[c_1862,c_714]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_15,plain,
% 1.95/0.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f78]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_706,plain,
% 1.95/0.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_0,plain,
% 1.95/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 1.95/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_719,plain,
% 1.95/0.99      ( r2_hidden(X0,X1) != iProver_top
% 1.95/0.99      | r2_hidden(X0,X2) != iProver_top
% 1.95/0.99      | r1_xboole_0(X2,X1) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2294,plain,
% 1.95/0.99      ( r2_hidden(X0,X1) != iProver_top
% 1.95/0.99      | r1_xboole_0(X1,k2_enumset1(X2,X2,X3,X0)) != iProver_top ),
% 1.95/0.99      inference(superposition,[status(thm)],[c_706,c_719]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2980,plain,
% 1.95/0.99      ( r2_hidden(sK2,X0) != iProver_top
% 1.95/0.99      | r1_xboole_0(X0,sK3) != iProver_top ),
% 1.95/0.99      inference(superposition,[status(thm)],[c_1865,c_2294]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3003,plain,
% 1.95/0.99      ( r2_hidden(X0,sK3) = iProver_top
% 1.95/0.99      | r2_hidden(sK2,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 1.95/0.99      inference(superposition,[status(thm)],[c_702,c_2980]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3005,plain,
% 1.95/0.99      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 1.95/0.99      | r2_hidden(sK2,sK3) = iProver_top ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_3003]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_17,plain,
% 1.95/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 1.95/0.99      inference(cnf_transformation,[],[f82]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_30,plain,
% 1.95/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_32,plain,
% 1.95/0.99      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_30]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_20,negated_conjecture,
% 1.95/0.99      ( ~ r2_hidden(sK2,sK3) ),
% 1.95/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_23,plain,
% 1.95/0.99      ( r2_hidden(sK2,sK3) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(contradiction,plain,
% 1.95/0.99      ( $false ),
% 1.95/0.99      inference(minisat,[status(thm)],[c_3005,c_32,c_23]) ).
% 1.95/0.99  
% 1.95/0.99  
% 1.95/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.95/0.99  
% 1.95/0.99  ------                               Statistics
% 1.95/0.99  
% 1.95/0.99  ------ General
% 1.95/0.99  
% 1.95/0.99  abstr_ref_over_cycles:                  0
% 1.95/0.99  abstr_ref_under_cycles:                 0
% 1.95/0.99  gc_basic_clause_elim:                   0
% 1.95/0.99  forced_gc_time:                         0
% 1.95/0.99  parsing_time:                           0.008
% 1.95/0.99  unif_index_cands_time:                  0.
% 1.95/0.99  unif_index_add_time:                    0.
% 1.95/0.99  orderings_time:                         0.
% 1.95/0.99  out_proof_time:                         0.006
% 1.95/0.99  total_time:                             0.123
% 1.95/0.99  num_of_symbols:                         40
% 1.95/0.99  num_of_terms:                           4497
% 1.95/0.99  
% 1.95/0.99  ------ Preprocessing
% 1.95/0.99  
% 1.95/0.99  num_of_splits:                          0
% 1.95/0.99  num_of_split_atoms:                     0
% 1.95/0.99  num_of_reused_defs:                     0
% 1.95/0.99  num_eq_ax_congr_red:                    18
% 1.95/0.99  num_of_sem_filtered_clauses:            1
% 1.95/0.99  num_of_subtypes:                        0
% 1.95/0.99  monotx_restored_types:                  0
% 1.95/0.99  sat_num_of_epr_types:                   0
% 1.95/0.99  sat_num_of_non_cyclic_types:            0
% 1.95/0.99  sat_guarded_non_collapsed_types:        0
% 1.95/0.99  num_pure_diseq_elim:                    0
% 1.95/0.99  simp_replaced_by:                       0
% 1.95/0.99  res_preprocessed:                       99
% 1.95/0.99  prep_upred:                             0
% 1.95/0.99  prep_unflattend:                        0
% 1.95/0.99  smt_new_axioms:                         0
% 1.95/0.99  pred_elim_cands:                        3
% 1.95/0.99  pred_elim:                              0
% 1.95/0.99  pred_elim_cl:                           0
% 1.95/0.99  pred_elim_cycles:                       2
% 1.95/0.99  merged_defs:                            0
% 1.95/0.99  merged_defs_ncl:                        0
% 1.95/0.99  bin_hyper_res:                          0
% 1.95/0.99  prep_cycles:                            4
% 1.95/0.99  pred_elim_time:                         0.
% 1.95/0.99  splitting_time:                         0.
% 1.95/0.99  sem_filter_time:                        0.
% 1.95/0.99  monotx_time:                            0.
% 1.95/0.99  subtype_inf_time:                       0.
% 1.95/0.99  
% 1.95/0.99  ------ Problem properties
% 1.95/0.99  
% 1.95/0.99  clauses:                                21
% 1.95/0.99  conjectures:                            2
% 1.95/0.99  epr:                                    4
% 1.95/0.99  horn:                                   16
% 1.95/0.99  ground:                                 2
% 1.95/0.99  unary:                                  8
% 1.95/0.99  binary:                                 5
% 1.95/0.99  lits:                                   45
% 1.95/0.99  lits_eq:                                15
% 1.95/0.99  fd_pure:                                0
% 1.95/0.99  fd_pseudo:                              0
% 1.95/0.99  fd_cond:                                0
% 1.95/0.99  fd_pseudo_cond:                         5
% 1.95/0.99  ac_symbols:                             0
% 1.95/0.99  
% 1.95/0.99  ------ Propositional Solver
% 1.95/0.99  
% 1.95/0.99  prop_solver_calls:                      26
% 1.95/0.99  prop_fast_solver_calls:                 509
% 1.95/0.99  smt_solver_calls:                       0
% 1.95/0.99  smt_fast_solver_calls:                  0
% 1.95/0.99  prop_num_of_clauses:                    911
% 1.95/0.99  prop_preprocess_simplified:             5395
% 1.95/0.99  prop_fo_subsumed:                       0
% 1.95/0.99  prop_solver_time:                       0.
% 1.95/0.99  smt_solver_time:                        0.
% 1.95/0.99  smt_fast_solver_time:                   0.
% 1.95/0.99  prop_fast_solver_time:                  0.
% 1.95/0.99  prop_unsat_core_time:                   0.
% 1.95/0.99  
% 1.95/0.99  ------ QBF
% 1.95/0.99  
% 1.95/0.99  qbf_q_res:                              0
% 1.95/0.99  qbf_num_tautologies:                    0
% 1.95/0.99  qbf_prep_cycles:                        0
% 1.95/0.99  
% 1.95/0.99  ------ BMC1
% 1.95/0.99  
% 1.95/0.99  bmc1_current_bound:                     -1
% 1.95/0.99  bmc1_last_solved_bound:                 -1
% 1.95/0.99  bmc1_unsat_core_size:                   -1
% 1.95/0.99  bmc1_unsat_core_parents_size:           -1
% 1.95/0.99  bmc1_merge_next_fun:                    0
% 1.95/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.95/0.99  
% 1.95/0.99  ------ Instantiation
% 1.95/0.99  
% 1.95/0.99  inst_num_of_clauses:                    374
% 1.95/0.99  inst_num_in_passive:                    109
% 1.95/0.99  inst_num_in_active:                     137
% 1.95/0.99  inst_num_in_unprocessed:                128
% 1.95/0.99  inst_num_of_loops:                      140
% 1.95/0.99  inst_num_of_learning_restarts:          0
% 1.95/0.99  inst_num_moves_active_passive:          1
% 1.95/0.99  inst_lit_activity:                      0
% 1.95/0.99  inst_lit_activity_moves:                0
% 1.95/0.99  inst_num_tautologies:                   0
% 1.95/0.99  inst_num_prop_implied:                  0
% 1.95/0.99  inst_num_existing_simplified:           0
% 1.95/0.99  inst_num_eq_res_simplified:             0
% 1.95/0.99  inst_num_child_elim:                    0
% 1.95/0.99  inst_num_of_dismatching_blockings:      331
% 1.95/0.99  inst_num_of_non_proper_insts:           381
% 1.95/0.99  inst_num_of_duplicates:                 0
% 1.95/0.99  inst_inst_num_from_inst_to_res:         0
% 1.95/0.99  inst_dismatching_checking_time:         0.
% 1.95/0.99  
% 1.95/0.99  ------ Resolution
% 1.95/0.99  
% 1.95/0.99  res_num_of_clauses:                     0
% 1.95/0.99  res_num_in_passive:                     0
% 1.95/0.99  res_num_in_active:                      0
% 1.95/0.99  res_num_of_loops:                       103
% 1.95/0.99  res_forward_subset_subsumed:            23
% 1.95/0.99  res_backward_subset_subsumed:           0
% 1.95/0.99  res_forward_subsumed:                   0
% 1.95/0.99  res_backward_subsumed:                  0
% 1.95/0.99  res_forward_subsumption_resolution:     0
% 1.95/0.99  res_backward_subsumption_resolution:    0
% 1.95/0.99  res_clause_to_clause_subsumption:       140
% 1.95/0.99  res_orphan_elimination:                 0
% 1.95/0.99  res_tautology_del:                      12
% 1.95/0.99  res_num_eq_res_simplified:              0
% 1.95/0.99  res_num_sel_changes:                    0
% 1.95/0.99  res_moves_from_active_to_pass:          0
% 1.95/0.99  
% 1.95/0.99  ------ Superposition
% 1.95/0.99  
% 1.95/0.99  sup_time_total:                         0.
% 1.95/0.99  sup_time_generating:                    0.
% 1.95/0.99  sup_time_sim_full:                      0.
% 1.95/0.99  sup_time_sim_immed:                     0.
% 1.95/0.99  
% 1.95/0.99  sup_num_of_clauses:                     43
% 1.95/0.99  sup_num_in_active:                      26
% 1.95/0.99  sup_num_in_passive:                     17
% 1.95/0.99  sup_num_of_loops:                       27
% 1.95/0.99  sup_fw_superposition:                   39
% 1.95/0.99  sup_bw_superposition:                   15
% 1.95/0.99  sup_immediate_simplified:               3
% 1.95/0.99  sup_given_eliminated:                   0
% 1.95/0.99  comparisons_done:                       0
% 1.95/0.99  comparisons_avoided:                    0
% 1.95/0.99  
% 1.95/0.99  ------ Simplifications
% 1.95/0.99  
% 1.95/0.99  
% 1.95/0.99  sim_fw_subset_subsumed:                 0
% 1.95/0.99  sim_bw_subset_subsumed:                 0
% 1.95/0.99  sim_fw_subsumed:                        3
% 1.95/0.99  sim_bw_subsumed:                        0
% 1.95/0.99  sim_fw_subsumption_res:                 1
% 1.95/0.99  sim_bw_subsumption_res:                 0
% 1.95/0.99  sim_tautology_del:                      4
% 1.95/0.99  sim_eq_tautology_del:                   4
% 1.95/0.99  sim_eq_res_simp:                        0
% 1.95/0.99  sim_fw_demodulated:                     0
% 1.95/0.99  sim_bw_demodulated:                     2
% 1.95/0.99  sim_light_normalised:                   0
% 1.95/0.99  sim_joinable_taut:                      0
% 1.95/0.99  sim_joinable_simp:                      0
% 1.95/0.99  sim_ac_normalised:                      0
% 1.95/0.99  sim_smt_subsumption:                    0
% 1.95/0.99  
%------------------------------------------------------------------------------
