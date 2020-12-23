%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:46 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 177 expanded)
%              Number of clauses        :   37 (  38 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  259 ( 406 expanded)
%              Number of equality atoms :  141 ( 265 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f21,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f21])).

fof(f24,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f22])).

fof(f33,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f33])).

fof(f65,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f64,f70])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f67])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f68])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f69])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f84,plain,(
    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(definition_unfolding,[],[f65,f71,f74])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f71])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f52,f70])).

fof(f89,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f82])).

fof(f90,plain,(
    ! [X4,X1] : r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f89])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f83])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_264,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_3,c_12,c_0])).

cnf(c_688,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0))
    | ~ r2_hidden(X0,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1)) ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_13933,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))
    | ~ r2_hidden(X0,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k1_xboole_0))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(c_13935,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK1,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0))
    | ~ r2_hidden(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13933])).

cnf(c_270,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_642,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))
    | X0 != X2
    | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2) ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_5332,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))
    | r2_hidden(X2,k1_xboole_0)
    | X2 != X0
    | k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(instantiation,[status(thm)],[c_642])).

cnf(c_5334,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK1,k1_xboole_0)
    | sK1 != sK1
    | k1_xboole_0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_5332])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2271,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2272,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2271])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2130,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2136,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_2130])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1051,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | ~ r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X0)
    | X0 = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2129,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
    | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(instantiation,[status(thm)],[c_1051])).

cnf(c_2132,plain,
    ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2129])).

cnf(c_271,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1398,plain,
    ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)))
    | r1_tarski(X1,k1_xboole_0)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_271,c_20])).

cnf(c_11,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1615,plain,
    ( r1_tarski(X0,k1_xboole_0)
    | X0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(resolution,[status(thm)],[c_1398,c_11])).

cnf(c_267,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1642,plain,
    ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1615,c_267])).

cnf(c_748,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k5_xboole_0(X3,X4))
    | X2 != X0
    | k5_xboole_0(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_769,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k5_xboole_0(X1,k1_xboole_0))
    | X2 != X0
    | k5_xboole_0(X1,k1_xboole_0) != X1 ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_830,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))
    | r2_hidden(X2,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k1_xboole_0))
    | X2 != X0
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k1_xboole_0) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(instantiation,[status(thm)],[c_769])).

cnf(c_832,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK1,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0))
    | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_18,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_25,plain,
    ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_22,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13935,c_5334,c_2272,c_2136,c_2132,c_1642,c_832,c_25,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.78/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/0.98  
% 3.78/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/0.98  
% 3.78/0.98  ------  iProver source info
% 3.78/0.98  
% 3.78/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.78/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/0.98  git: non_committed_changes: false
% 3.78/0.98  git: last_make_outside_of_git: false
% 3.78/0.98  
% 3.78/0.98  ------ 
% 3.78/0.98  ------ Parsing...
% 3.78/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/0.98  ------ Proving...
% 3.78/0.98  ------ Problem Properties 
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  clauses                                 20
% 3.78/0.98  conjectures                             1
% 3.78/0.98  EPR                                     3
% 3.78/0.98  Horn                                    15
% 3.78/0.98  unary                                   11
% 3.78/0.98  binary                                  0
% 3.78/0.98  lits                                    39
% 3.78/0.98  lits eq                                 16
% 3.78/0.98  fd_pure                                 0
% 3.78/0.98  fd_pseudo                               0
% 3.78/0.98  fd_cond                                 0
% 3.78/0.98  fd_pseudo_cond                          4
% 3.78/0.98  AC symbols                              1
% 3.78/0.98  
% 3.78/0.98  ------ Input Options Time Limit: Unbounded
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  ------ 
% 3.78/0.98  Current options:
% 3.78/0.98  ------ 
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  ------ Proving...
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  % SZS status Theorem for theBenchmark.p
% 3.78/0.98  
% 3.78/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.78/0.98  
% 3.78/0.98  fof(f2,axiom,(
% 3.78/0.98    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f23,plain,(
% 3.78/0.98    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 3.78/0.98    inference(ennf_transformation,[],[f2])).
% 3.78/0.98  
% 3.78/0.98  fof(f25,plain,(
% 3.78/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 3.78/0.98    inference(nnf_transformation,[],[f23])).
% 3.78/0.98  
% 3.78/0.98  fof(f37,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 3.78/0.98    inference(cnf_transformation,[],[f25])).
% 3.78/0.98  
% 3.78/0.98  fof(f9,axiom,(
% 3.78/0.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f48,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f9])).
% 3.78/0.98  
% 3.78/0.98  fof(f1,axiom,(
% 3.78/0.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f35,plain,(
% 3.78/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f1])).
% 3.78/0.98  
% 3.78/0.98  fof(f7,axiom,(
% 3.78/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f46,plain,(
% 3.78/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.78/0.98    inference(cnf_transformation,[],[f7])).
% 3.78/0.98  
% 3.78/0.98  fof(f5,axiom,(
% 3.78/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f44,plain,(
% 3.78/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f5])).
% 3.78/0.98  
% 3.78/0.98  fof(f3,axiom,(
% 3.78/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f26,plain,(
% 3.78/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.78/0.98    inference(nnf_transformation,[],[f3])).
% 3.78/0.98  
% 3.78/0.98  fof(f27,plain,(
% 3.78/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.78/0.98    inference(flattening,[],[f26])).
% 3.78/0.98  
% 3.78/0.98  fof(f42,plain,(
% 3.78/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f27])).
% 3.78/0.98  
% 3.78/0.98  fof(f21,conjecture,(
% 3.78/0.98    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f22,negated_conjecture,(
% 3.78/0.98    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.78/0.98    inference(negated_conjecture,[],[f21])).
% 3.78/0.98  
% 3.78/0.98  fof(f24,plain,(
% 3.78/0.98    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 3.78/0.98    inference(ennf_transformation,[],[f22])).
% 3.78/0.98  
% 3.78/0.98  fof(f33,plain,(
% 3.78/0.98    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f34,plain,(
% 3.78/0.98    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 3.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f33])).
% 3.78/0.98  
% 3.78/0.98  fof(f65,plain,(
% 3.78/0.98    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 3.78/0.98    inference(cnf_transformation,[],[f34])).
% 3.78/0.98  
% 3.78/0.98  fof(f20,axiom,(
% 3.78/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f64,plain,(
% 3.78/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.78/0.98    inference(cnf_transformation,[],[f20])).
% 3.78/0.98  
% 3.78/0.98  fof(f71,plain,(
% 3.78/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.78/0.98    inference(definition_unfolding,[],[f64,f70])).
% 3.78/0.98  
% 3.78/0.98  fof(f13,axiom,(
% 3.78/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f57,plain,(
% 3.78/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f13])).
% 3.78/0.98  
% 3.78/0.98  fof(f14,axiom,(
% 3.78/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f58,plain,(
% 3.78/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f14])).
% 3.78/0.98  
% 3.78/0.98  fof(f15,axiom,(
% 3.78/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f59,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f15])).
% 3.78/0.98  
% 3.78/0.98  fof(f16,axiom,(
% 3.78/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f60,plain,(
% 3.78/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f16])).
% 3.78/0.98  
% 3.78/0.98  fof(f17,axiom,(
% 3.78/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f61,plain,(
% 3.78/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f17])).
% 3.78/0.98  
% 3.78/0.98  fof(f18,axiom,(
% 3.78/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f62,plain,(
% 3.78/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f18])).
% 3.78/0.98  
% 3.78/0.98  fof(f19,axiom,(
% 3.78/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f63,plain,(
% 3.78/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f19])).
% 3.78/0.98  
% 3.78/0.98  fof(f66,plain,(
% 3.78/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.78/0.98    inference(definition_unfolding,[],[f62,f63])).
% 3.78/0.98  
% 3.78/0.98  fof(f67,plain,(
% 3.78/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.78/0.98    inference(definition_unfolding,[],[f61,f66])).
% 3.78/0.98  
% 3.78/0.98  fof(f68,plain,(
% 3.78/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.78/0.98    inference(definition_unfolding,[],[f60,f67])).
% 3.78/0.98  
% 3.78/0.98  fof(f69,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.78/0.98    inference(definition_unfolding,[],[f59,f68])).
% 3.78/0.98  
% 3.78/0.98  fof(f70,plain,(
% 3.78/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.78/0.98    inference(definition_unfolding,[],[f58,f69])).
% 3.78/0.98  
% 3.78/0.98  fof(f74,plain,(
% 3.78/0.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.78/0.98    inference(definition_unfolding,[],[f57,f70])).
% 3.78/0.98  
% 3.78/0.98  fof(f84,plain,(
% 3.78/0.98    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))),
% 3.78/0.98    inference(definition_unfolding,[],[f65,f71,f74])).
% 3.78/0.98  
% 3.78/0.98  fof(f8,axiom,(
% 3.78/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f47,plain,(
% 3.78/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.78/0.98    inference(cnf_transformation,[],[f8])).
% 3.78/0.98  
% 3.78/0.98  fof(f76,plain,(
% 3.78/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.78/0.98    inference(definition_unfolding,[],[f47,f71])).
% 3.78/0.98  
% 3.78/0.98  fof(f12,axiom,(
% 3.78/0.98    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f28,plain,(
% 3.78/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.78/0.98    inference(nnf_transformation,[],[f12])).
% 3.78/0.98  
% 3.78/0.98  fof(f29,plain,(
% 3.78/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.78/0.98    inference(flattening,[],[f28])).
% 3.78/0.98  
% 3.78/0.98  fof(f30,plain,(
% 3.78/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.78/0.98    inference(rectify,[],[f29])).
% 3.78/0.98  
% 3.78/0.98  fof(f31,plain,(
% 3.78/0.98    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f32,plain,(
% 3.78/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.78/0.98  
% 3.78/0.98  fof(f52,plain,(
% 3.78/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.78/0.98    inference(cnf_transformation,[],[f32])).
% 3.78/0.98  
% 3.78/0.98  fof(f82,plain,(
% 3.78/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 3.78/0.98    inference(definition_unfolding,[],[f52,f70])).
% 3.78/0.98  
% 3.78/0.98  fof(f89,plain,(
% 3.78/0.98    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2) )),
% 3.78/0.98    inference(equality_resolution,[],[f82])).
% 3.78/0.98  
% 3.78/0.98  fof(f90,plain,(
% 3.78/0.98    ( ! [X4,X1] : (r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1))) )),
% 3.78/0.98    inference(equality_resolution,[],[f89])).
% 3.78/0.98  
% 3.78/0.98  fof(f51,plain,(
% 3.78/0.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.78/0.98    inference(cnf_transformation,[],[f32])).
% 3.78/0.98  
% 3.78/0.98  fof(f83,plain,(
% 3.78/0.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 3.78/0.98    inference(definition_unfolding,[],[f51,f70])).
% 3.78/0.98  
% 3.78/0.98  fof(f91,plain,(
% 3.78/0.98    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.78/0.98    inference(equality_resolution,[],[f83])).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,X1)
% 3.78/0.98      | ~ r2_hidden(X0,X2)
% 3.78/0.98      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 3.78/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_12,plain,
% 3.78/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.78/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_0,plain,
% 3.78/0.98      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 3.78/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_264,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,X1)
% 3.78/0.98      | ~ r2_hidden(X0,X2)
% 3.78/0.98      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 3.78/0.98      inference(theory_normalisation,[status(thm)],[c_3,c_12,c_0]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_688,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,X1)
% 3.78/0.98      | ~ r2_hidden(X0,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0))
% 3.78/0.98      | ~ r2_hidden(X0,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1)) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_264]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_13933,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))
% 3.78/0.98      | ~ r2_hidden(X0,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k1_xboole_0))
% 3.78/0.98      | ~ r2_hidden(X0,k1_xboole_0) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_688]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_13935,plain,
% 3.78/0.98      ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 3.78/0.98      | ~ r2_hidden(sK1,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0))
% 3.78/0.98      | ~ r2_hidden(sK1,k1_xboole_0) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_13933]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_270,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.78/0.98      theory(equality) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_642,plain,
% 3.78/0.98      ( r2_hidden(X0,X1)
% 3.78/0.98      | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))
% 3.78/0.98      | X0 != X2
% 3.78/0.98      | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_270]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5332,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))
% 3.78/0.98      | r2_hidden(X2,k1_xboole_0)
% 3.78/0.98      | X2 != X0
% 3.78/0.98      | k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_642]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5334,plain,
% 3.78/0.98      ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 3.78/0.98      | r2_hidden(sK1,k1_xboole_0)
% 3.78/0.98      | sK1 != sK1
% 3.78/0.98      | k1_xboole_0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_5332]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_10,plain,
% 3.78/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.78/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2271,plain,
% 3.78/0.98      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2272,plain,
% 3.78/0.98      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_2271]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_8,plain,
% 3.78/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.78/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2130,plain,
% 3.78/0.98      ( r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2136,plain,
% 3.78/0.98      ( r1_tarski(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_2130]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5,plain,
% 3.78/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.78/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1051,plain,
% 3.78/0.98      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 3.78/0.98      | ~ r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X0)
% 3.78/0.98      | X0 = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2129,plain,
% 3.78/0.98      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_xboole_0)
% 3.78/0.98      | ~ r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
% 3.78/0.98      | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_1051]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2132,plain,
% 3.78/0.98      ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)
% 3.78/0.98      | ~ r1_tarski(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 3.78/0.98      | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_2129]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_271,plain,
% 3.78/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.78/0.98      theory(equality) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_20,negated_conjecture,
% 3.78/0.98      ( k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)) ),
% 3.78/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1398,plain,
% 3.78/0.98      ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)))
% 3.78/0.98      | r1_tarski(X1,k1_xboole_0)
% 3.78/0.98      | X1 != X0 ),
% 3.78/0.98      inference(resolution,[status(thm)],[c_271,c_20]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_11,plain,
% 3.78/0.98      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 3.78/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1615,plain,
% 3.78/0.98      ( r1_tarski(X0,k1_xboole_0)
% 3.78/0.98      | X0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 3.78/0.98      inference(resolution,[status(thm)],[c_1398,c_11]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_267,plain,( X0 = X0 ),theory(equality) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1642,plain,
% 3.78/0.98      ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) ),
% 3.78/0.98      inference(resolution,[status(thm)],[c_1615,c_267]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_748,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,X1)
% 3.78/0.98      | r2_hidden(X2,k5_xboole_0(X3,X4))
% 3.78/0.98      | X2 != X0
% 3.78/0.98      | k5_xboole_0(X3,X4) != X1 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_270]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_769,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,X1)
% 3.78/0.98      | r2_hidden(X2,k5_xboole_0(X1,k1_xboole_0))
% 3.78/0.98      | X2 != X0
% 3.78/0.98      | k5_xboole_0(X1,k1_xboole_0) != X1 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_748]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_830,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))
% 3.78/0.98      | r2_hidden(X2,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k1_xboole_0))
% 3.78/0.98      | X2 != X0
% 3.78/0.98      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k1_xboole_0) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_769]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_832,plain,
% 3.78/0.98      ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 3.78/0.98      | r2_hidden(sK1,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0))
% 3.78/0.98      | k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 3.78/0.98      | sK1 != sK1 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_830]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_18,plain,
% 3.78/0.98      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.78/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_25,plain,
% 3.78/0.98      ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_19,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 3.78/0.98      | X0 = X1
% 3.78/0.98      | X0 = X2 ),
% 3.78/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_22,plain,
% 3.78/0.98      ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 3.78/0.98      | sK1 = sK1 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_19]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(contradiction,plain,
% 3.78/0.98      ( $false ),
% 3.78/0.98      inference(minisat,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_13935,c_5334,c_2272,c_2136,c_2132,c_1642,c_832,c_25,
% 3.78/0.98                 c_22]) ).
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.78/0.98  
% 3.78/0.98  ------                               Statistics
% 3.78/0.98  
% 3.78/0.98  ------ Selected
% 3.78/0.98  
% 3.78/0.98  total_time:                             0.483
% 3.78/0.98  
%------------------------------------------------------------------------------
