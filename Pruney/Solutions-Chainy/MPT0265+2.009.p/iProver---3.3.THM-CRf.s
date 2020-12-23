%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:21 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  101 (1487 expanded)
%              Number of clauses        :   52 ( 281 expanded)
%              Number of leaves         :   14 ( 432 expanded)
%              Depth                    :   20
%              Number of atoms          :  380 (6620 expanded)
%              Number of equality atoms :  180 (3240 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f11,plain,(
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

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f26,f29])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
          | ( X0 != X2
            & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
        & ( X0 = X2
          | ~ r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) )
   => ( k3_xboole_0(k2_tarski(sK2,sK4),sK3) != k1_tarski(sK2)
      & ( sK2 = sK4
        | ~ r2_hidden(sK4,sK3) )
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k3_xboole_0(k2_tarski(sK2,sK4),sK3) != k1_tarski(sK2)
    & ( sK2 = sK4
      | ~ r2_hidden(sK4,sK3) )
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f21])).

fof(f41,plain,(
    k3_xboole_0(k2_tarski(sK2,sK4),sK3) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f56,plain,(
    k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),sK3)) != k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f41,f29,f42,f43])).

fof(f40,plain,
    ( sK2 = sK4
    | ~ r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f62,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f54])).

fof(f63,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f62])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f39,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f32,f42])).

fof(f60,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f53])).

fof(f61,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f60])).

cnf(c_157,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_156,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2135,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X2,X3,X4))
    | r2_hidden(X5,k2_enumset1(X6,X7,X8,X9))
    | X6 != X1
    | X7 != X2
    | X8 != X3
    | X9 != X4
    | X5 != X0 ),
    inference(resolution,[status(thm)],[c_157,c_156])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_12,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),sK3)) != k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1021,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK4))
    | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(resolution,[status(thm)],[c_2,c_12])).

cnf(c_7541,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X2,X3,X4))
    | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
    | X0 != sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2))
    | X4 != sK4
    | X1 != sK2
    | X2 != sK2
    | X3 != sK2 ),
    inference(resolution,[status(thm)],[c_2135,c_1021])).

cnf(c_153,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7721,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(X0,X1,X2,X3))
    | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
    | X3 != sK4
    | X0 != sK2
    | X1 != sK2
    | X2 != sK2 ),
    inference(resolution,[status(thm)],[c_7541,c_153])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(sK4,sK3)
    | sK2 = sK4 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_18,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_493,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK4))
    | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),sK3)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_601,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_869,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3) ),
    inference(resolution,[status(thm)],[c_1,c_12])).

cnf(c_1049,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3)
    | sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = sK2 ),
    inference(resolution,[status(thm)],[c_869,c_11])).

cnf(c_154,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1240,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3)
    | X0 != sK2
    | sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = X0 ),
    inference(resolution,[status(thm)],[c_1049,c_154])).

cnf(c_617,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_154,c_153])).

cnf(c_1356,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3)
    | X0 = sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2))
    | X0 != sK2 ),
    inference(resolution,[status(thm)],[c_1240,c_617])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_480,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2,sK3)
    | X1 != sK3
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_600,plain,
    ( r2_hidden(X0,sK3)
    | ~ r2_hidden(sK2,sK3)
    | X0 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_1838,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3)
    | ~ r2_hidden(sK2,sK3)
    | sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_1908,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1356,c_14,c_601,c_1049,c_1838])).

cnf(c_848,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_156,c_153])).

cnf(c_1230,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
    | sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = sK4
    | sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = sK2 ),
    inference(resolution,[status(thm)],[c_1021,c_11])).

cnf(c_1254,plain,
    ( sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = sK4
    | sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = sK2 ),
    inference(resolution,[status(thm)],[c_1230,c_11])).

cnf(c_1341,plain,
    ( sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = sK2
    | sK4 = sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(resolution,[status(thm)],[c_1254,c_617])).

cnf(c_2291,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),X0)
    | ~ r2_hidden(sK2,X0)
    | sK4 = sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(resolution,[status(thm)],[c_848,c_1341])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3354,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK4))
    | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3)
    | ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),sK3)) = k2_enumset1(sK2,sK2,sK2,sK2)
    | sK4 = sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(resolution,[status(thm)],[c_2291,c_0])).

cnf(c_1380,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK4,sK3)
    | sK3 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_2583,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),X0)
    | r2_hidden(sK4,sK3)
    | sK3 != X0
    | sK4 != sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_1380])).

cnf(c_5534,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3)
    | r2_hidden(sK4,sK3)
    | sK3 != sK3
    | sK4 != sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_2583])).

cnf(c_7723,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
    | sK2 != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_7721])).

cnf(c_8534,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7721,c_14,c_13,c_12,c_18,c_21,c_493,c_601,c_1049,c_1838,c_3354,c_5534,c_7723])).

cnf(c_8546,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK4))
    | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3)
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),sK3)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(resolution,[status(thm)],[c_8534,c_0])).

cnf(c_524,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK4))
    | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3)
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),sK3)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_9633,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8546,c_14,c_13,c_12,c_18,c_21,c_493,c_524,c_601,c_1049,c_1838,c_3354,c_5534,c_7723])).

cnf(c_2295,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),X0)
    | ~ r2_hidden(sK4,X0)
    | sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = sK2 ),
    inference(resolution,[status(thm)],[c_848,c_1254])).

cnf(c_2313,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),X0)
    | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),X1)
    | ~ r2_hidden(sK4,X0)
    | ~ r2_hidden(sK2,X1) ),
    inference(resolution,[status(thm)],[c_2295,c_848])).

cnf(c_10057,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),X0)
    | ~ r2_hidden(sK4,X0)
    | ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK4)) ),
    inference(resolution,[status(thm)],[c_9633,c_2313])).

cnf(c_10070,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),X0)
    | ~ r2_hidden(sK4,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10057,c_10])).

cnf(c_10635,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK2,sK2,sK2,sK4)) ),
    inference(resolution,[status(thm)],[c_10070,c_9633])).

cnf(c_9,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5494,plain,
    ( r2_hidden(sK4,k2_enumset1(X0,X0,X0,sK4)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5500,plain,
    ( r2_hidden(sK4,k2_enumset1(sK2,sK2,sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_5494])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10635,c_5500])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.08/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/0.99  
% 4.08/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.08/0.99  
% 4.08/0.99  ------  iProver source info
% 4.08/0.99  
% 4.08/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.08/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.08/0.99  git: non_committed_changes: false
% 4.08/0.99  git: last_make_outside_of_git: false
% 4.08/0.99  
% 4.08/0.99  ------ 
% 4.08/0.99  ------ Parsing...
% 4.08/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.08/0.99  
% 4.08/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.08/0.99  
% 4.08/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.08/0.99  
% 4.08/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.08/0.99  ------ Proving...
% 4.08/0.99  ------ Problem Properties 
% 4.08/0.99  
% 4.08/0.99  
% 4.08/0.99  clauses                                 15
% 4.08/0.99  conjectures                             3
% 4.08/0.99  EPR                                     2
% 4.08/0.99  Horn                                    11
% 4.08/0.99  unary                                   4
% 4.08/0.99  binary                                  3
% 4.08/0.99  lits                                    36
% 4.08/0.99  lits eq                                 14
% 4.08/0.99  fd_pure                                 0
% 4.08/0.99  fd_pseudo                               0
% 4.08/0.99  fd_cond                                 0
% 4.08/0.99  fd_pseudo_cond                          6
% 4.08/0.99  AC symbols                              0
% 4.08/0.99  
% 4.08/0.99  ------ Input Options Time Limit: Unbounded
% 4.08/0.99  
% 4.08/0.99  
% 4.08/0.99  ------ 
% 4.08/0.99  Current options:
% 4.08/0.99  ------ 
% 4.08/0.99  
% 4.08/0.99  
% 4.08/0.99  
% 4.08/0.99  
% 4.08/0.99  ------ Proving...
% 4.08/0.99  
% 4.08/0.99  
% 4.08/0.99  % SZS status Theorem for theBenchmark.p
% 4.08/0.99  
% 4.08/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.08/0.99  
% 4.08/0.99  fof(f1,axiom,(
% 4.08/0.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f11,plain,(
% 4.08/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.08/0.99    inference(nnf_transformation,[],[f1])).
% 4.08/0.99  
% 4.08/0.99  fof(f12,plain,(
% 4.08/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.08/0.99    inference(flattening,[],[f11])).
% 4.08/0.99  
% 4.08/0.99  fof(f13,plain,(
% 4.08/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.08/0.99    inference(rectify,[],[f12])).
% 4.08/0.99  
% 4.08/0.99  fof(f14,plain,(
% 4.08/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 4.08/0.99    introduced(choice_axiom,[])).
% 4.08/0.99  
% 4.08/0.99  fof(f15,plain,(
% 4.08/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).
% 4.08/0.99  
% 4.08/0.99  fof(f26,plain,(
% 4.08/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f15])).
% 4.08/0.99  
% 4.08/0.99  fof(f2,axiom,(
% 4.08/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f29,plain,(
% 4.08/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.08/0.99    inference(cnf_transformation,[],[f2])).
% 4.08/0.99  
% 4.08/0.99  fof(f46,plain,(
% 4.08/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.08/0.99    inference(definition_unfolding,[],[f26,f29])).
% 4.08/0.99  
% 4.08/0.99  fof(f7,conjecture,(
% 4.08/0.99    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))))),
% 4.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f8,negated_conjecture,(
% 4.08/0.99    ~! [X0,X1,X2] : (r2_hidden(X0,X1) => (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))))),
% 4.08/0.99    inference(negated_conjecture,[],[f7])).
% 4.08/0.99  
% 4.08/0.99  fof(f9,plain,(
% 4.08/0.99    ? [X0,X1,X2] : ((k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1))) & r2_hidden(X0,X1))),
% 4.08/0.99    inference(ennf_transformation,[],[f8])).
% 4.08/0.99  
% 4.08/0.99  fof(f10,plain,(
% 4.08/0.99    ? [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 4.08/0.99    inference(flattening,[],[f9])).
% 4.08/0.99  
% 4.08/0.99  fof(f21,plain,(
% 4.08/0.99    ? [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1)) => (k3_xboole_0(k2_tarski(sK2,sK4),sK3) != k1_tarski(sK2) & (sK2 = sK4 | ~r2_hidden(sK4,sK3)) & r2_hidden(sK2,sK3))),
% 4.08/0.99    introduced(choice_axiom,[])).
% 4.08/0.99  
% 4.08/0.99  fof(f22,plain,(
% 4.08/0.99    k3_xboole_0(k2_tarski(sK2,sK4),sK3) != k1_tarski(sK2) & (sK2 = sK4 | ~r2_hidden(sK4,sK3)) & r2_hidden(sK2,sK3)),
% 4.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f21])).
% 4.08/0.99  
% 4.08/0.99  fof(f41,plain,(
% 4.08/0.99    k3_xboole_0(k2_tarski(sK2,sK4),sK3) != k1_tarski(sK2)),
% 4.08/0.99    inference(cnf_transformation,[],[f22])).
% 4.08/0.99  
% 4.08/0.99  fof(f4,axiom,(
% 4.08/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f36,plain,(
% 4.08/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f4])).
% 4.08/0.99  
% 4.08/0.99  fof(f5,axiom,(
% 4.08/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f37,plain,(
% 4.08/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f5])).
% 4.08/0.99  
% 4.08/0.99  fof(f6,axiom,(
% 4.08/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f38,plain,(
% 4.08/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f6])).
% 4.08/0.99  
% 4.08/0.99  fof(f42,plain,(
% 4.08/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 4.08/0.99    inference(definition_unfolding,[],[f37,f38])).
% 4.08/0.99  
% 4.08/0.99  fof(f43,plain,(
% 4.08/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 4.08/0.99    inference(definition_unfolding,[],[f36,f42])).
% 4.08/0.99  
% 4.08/0.99  fof(f56,plain,(
% 4.08/0.99    k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),sK3)) != k2_enumset1(sK2,sK2,sK2,sK2)),
% 4.08/0.99    inference(definition_unfolding,[],[f41,f29,f42,f43])).
% 4.08/0.99  
% 4.08/0.99  fof(f40,plain,(
% 4.08/0.99    sK2 = sK4 | ~r2_hidden(sK4,sK3)),
% 4.08/0.99    inference(cnf_transformation,[],[f22])).
% 4.08/0.99  
% 4.08/0.99  fof(f3,axiom,(
% 4.08/0.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 4.08/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/0.99  
% 4.08/0.99  fof(f16,plain,(
% 4.08/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 4.08/0.99    inference(nnf_transformation,[],[f3])).
% 4.08/0.99  
% 4.08/0.99  fof(f17,plain,(
% 4.08/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 4.08/0.99    inference(flattening,[],[f16])).
% 4.08/0.99  
% 4.08/0.99  fof(f18,plain,(
% 4.08/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 4.08/0.99    inference(rectify,[],[f17])).
% 4.08/0.99  
% 4.08/0.99  fof(f19,plain,(
% 4.08/0.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 4.08/0.99    introduced(choice_axiom,[])).
% 4.08/0.99  
% 4.08/0.99  fof(f20,plain,(
% 4.08/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 4.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).
% 4.08/0.99  
% 4.08/0.99  fof(f30,plain,(
% 4.08/0.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 4.08/0.99    inference(cnf_transformation,[],[f20])).
% 4.08/0.99  
% 4.08/0.99  fof(f55,plain,(
% 4.08/0.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 4.08/0.99    inference(definition_unfolding,[],[f30,f42])).
% 4.08/0.99  
% 4.08/0.99  fof(f64,plain,(
% 4.08/0.99    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 4.08/0.99    inference(equality_resolution,[],[f55])).
% 4.08/0.99  
% 4.08/0.99  fof(f31,plain,(
% 4.08/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 4.08/0.99    inference(cnf_transformation,[],[f20])).
% 4.08/0.99  
% 4.08/0.99  fof(f54,plain,(
% 4.08/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 4.08/0.99    inference(definition_unfolding,[],[f31,f42])).
% 4.08/0.99  
% 4.08/0.99  fof(f62,plain,(
% 4.08/0.99    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 4.08/0.99    inference(equality_resolution,[],[f54])).
% 4.08/0.99  
% 4.08/0.99  fof(f63,plain,(
% 4.08/0.99    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 4.08/0.99    inference(equality_resolution,[],[f62])).
% 4.08/0.99  
% 4.08/0.99  fof(f27,plain,(
% 4.08/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f15])).
% 4.08/0.99  
% 4.08/0.99  fof(f45,plain,(
% 4.08/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.08/0.99    inference(definition_unfolding,[],[f27,f29])).
% 4.08/0.99  
% 4.08/0.99  fof(f39,plain,(
% 4.08/0.99    r2_hidden(sK2,sK3)),
% 4.08/0.99    inference(cnf_transformation,[],[f22])).
% 4.08/0.99  
% 4.08/0.99  fof(f28,plain,(
% 4.08/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.08/0.99    inference(cnf_transformation,[],[f15])).
% 4.08/0.99  
% 4.08/0.99  fof(f44,plain,(
% 4.08/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.08/0.99    inference(definition_unfolding,[],[f28,f29])).
% 4.08/0.99  
% 4.08/0.99  fof(f32,plain,(
% 4.08/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 4.08/0.99    inference(cnf_transformation,[],[f20])).
% 4.08/0.99  
% 4.08/0.99  fof(f53,plain,(
% 4.08/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 4.08/0.99    inference(definition_unfolding,[],[f32,f42])).
% 4.08/0.99  
% 4.08/0.99  fof(f60,plain,(
% 4.08/0.99    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 4.08/0.99    inference(equality_resolution,[],[f53])).
% 4.08/0.99  
% 4.08/0.99  fof(f61,plain,(
% 4.08/0.99    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 4.08/0.99    inference(equality_resolution,[],[f60])).
% 4.08/0.99  
% 4.08/0.99  cnf(c_157,plain,
% 4.08/0.99      ( X0 != X1
% 4.08/0.99      | X2 != X3
% 4.08/0.99      | X4 != X5
% 4.08/0.99      | X6 != X7
% 4.08/0.99      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 4.08/0.99      theory(equality) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_156,plain,
% 4.08/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.08/0.99      theory(equality) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_2135,plain,
% 4.08/0.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X2,X3,X4))
% 4.08/0.99      | r2_hidden(X5,k2_enumset1(X6,X7,X8,X9))
% 4.08/0.99      | X6 != X1
% 4.08/0.99      | X7 != X2
% 4.08/0.99      | X8 != X3
% 4.08/0.99      | X9 != X4
% 4.08/0.99      | X5 != X0 ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_157,c_156]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_2,plain,
% 4.08/0.99      ( r2_hidden(sK0(X0,X1,X2),X0)
% 4.08/0.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 4.08/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 4.08/0.99      inference(cnf_transformation,[],[f46]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_12,negated_conjecture,
% 4.08/0.99      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),sK3)) != k2_enumset1(sK2,sK2,sK2,sK2) ),
% 4.08/0.99      inference(cnf_transformation,[],[f56]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1021,plain,
% 4.08/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK4))
% 4.08/0.99      | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_2,c_12]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_7541,plain,
% 4.08/0.99      ( r2_hidden(X0,k2_enumset1(X1,X2,X3,X4))
% 4.08/0.99      | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
% 4.08/0.99      | X0 != sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2))
% 4.08/0.99      | X4 != sK4
% 4.08/0.99      | X1 != sK2
% 4.08/0.99      | X2 != sK2
% 4.08/0.99      | X3 != sK2 ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_2135,c_1021]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_153,plain,( X0 = X0 ),theory(equality) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_7721,plain,
% 4.08/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(X0,X1,X2,X3))
% 4.08/0.99      | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
% 4.08/0.99      | X3 != sK4
% 4.08/0.99      | X0 != sK2
% 4.08/0.99      | X1 != sK2
% 4.08/0.99      | X2 != sK2 ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_7541,c_153]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_13,negated_conjecture,
% 4.08/0.99      ( ~ r2_hidden(sK4,sK3) | sK2 = sK4 ),
% 4.08/0.99      inference(cnf_transformation,[],[f40]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_11,plain,
% 4.08/0.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 4.08/0.99      inference(cnf_transformation,[],[f64]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_18,plain,
% 4.08/0.99      ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) | sK2 = sK2 ),
% 4.08/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_10,plain,
% 4.08/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 4.08/0.99      inference(cnf_transformation,[],[f63]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_21,plain,
% 4.08/0.99      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 4.08/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_493,plain,
% 4.08/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK4))
% 4.08/0.99      | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
% 4.08/0.99      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),sK3)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 4.08/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_601,plain,
% 4.08/0.99      ( sK3 = sK3 ),
% 4.08/0.99      inference(instantiation,[status(thm)],[c_153]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1,plain,
% 4.08/0.99      ( r2_hidden(sK0(X0,X1,X2),X1)
% 4.08/0.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 4.08/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 4.08/0.99      inference(cnf_transformation,[],[f45]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_869,plain,
% 4.08/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
% 4.08/0.99      | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3) ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_1,c_12]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1049,plain,
% 4.08/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3)
% 4.08/0.99      | sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = sK2 ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_869,c_11]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_154,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1240,plain,
% 4.08/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3)
% 4.08/0.99      | X0 != sK2
% 4.08/0.99      | sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = X0 ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_1049,c_154]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_617,plain,
% 4.08/0.99      ( X0 != X1 | X1 = X0 ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_154,c_153]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1356,plain,
% 4.08/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3)
% 4.08/0.99      | X0 = sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2))
% 4.08/0.99      | X0 != sK2 ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_1240,c_617]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_14,negated_conjecture,
% 4.08/0.99      ( r2_hidden(sK2,sK3) ),
% 4.08/0.99      inference(cnf_transformation,[],[f39]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_480,plain,
% 4.08/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(sK2,sK3) | X1 != sK3 | X0 != sK2 ),
% 4.08/0.99      inference(instantiation,[status(thm)],[c_156]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_600,plain,
% 4.08/0.99      ( r2_hidden(X0,sK3)
% 4.08/0.99      | ~ r2_hidden(sK2,sK3)
% 4.08/0.99      | X0 != sK2
% 4.08/0.99      | sK3 != sK3 ),
% 4.08/0.99      inference(instantiation,[status(thm)],[c_480]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1838,plain,
% 4.08/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3)
% 4.08/0.99      | ~ r2_hidden(sK2,sK3)
% 4.08/0.99      | sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) != sK2
% 4.08/0.99      | sK3 != sK3 ),
% 4.08/0.99      inference(instantiation,[status(thm)],[c_600]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1908,plain,
% 4.08/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3) ),
% 4.08/0.99      inference(global_propositional_subsumption,
% 4.08/0.99                [status(thm)],
% 4.08/0.99                [c_1356,c_14,c_601,c_1049,c_1838]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_848,plain,
% 4.08/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_156,c_153]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1230,plain,
% 4.08/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
% 4.08/0.99      | sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = sK4
% 4.08/0.99      | sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = sK2 ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_1021,c_11]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1254,plain,
% 4.08/0.99      ( sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = sK4
% 4.08/0.99      | sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = sK2 ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_1230,c_11]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1341,plain,
% 4.08/0.99      ( sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = sK2
% 4.08/0.99      | sK4 = sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_1254,c_617]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_2291,plain,
% 4.08/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),X0)
% 4.08/0.99      | ~ r2_hidden(sK2,X0)
% 4.08/0.99      | sK4 = sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_848,c_1341]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_0,plain,
% 4.08/0.99      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 4.08/0.99      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 4.08/0.99      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 4.08/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 4.08/0.99      inference(cnf_transformation,[],[f44]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_3354,plain,
% 4.08/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK4))
% 4.08/0.99      | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3)
% 4.08/0.99      | ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
% 4.08/0.99      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),sK3)) = k2_enumset1(sK2,sK2,sK2,sK2)
% 4.08/0.99      | sK4 = sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_2291,c_0]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_1380,plain,
% 4.08/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(sK4,sK3) | sK3 != X1 | sK4 != X0 ),
% 4.08/0.99      inference(instantiation,[status(thm)],[c_156]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_2583,plain,
% 4.08/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),X0)
% 4.08/0.99      | r2_hidden(sK4,sK3)
% 4.08/0.99      | sK3 != X0
% 4.08/0.99      | sK4 != sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 4.08/0.99      inference(instantiation,[status(thm)],[c_1380]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_5534,plain,
% 4.08/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3)
% 4.08/0.99      | r2_hidden(sK4,sK3)
% 4.08/0.99      | sK3 != sK3
% 4.08/0.99      | sK4 != sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 4.08/0.99      inference(instantiation,[status(thm)],[c_2583]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_7723,plain,
% 4.08/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
% 4.08/0.99      | sK2 != sK4
% 4.08/0.99      | sK2 != sK2 ),
% 4.08/0.99      inference(instantiation,[status(thm)],[c_7721]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_8534,plain,
% 4.08/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 4.08/0.99      inference(global_propositional_subsumption,
% 4.08/0.99                [status(thm)],
% 4.08/0.99                [c_7721,c_14,c_13,c_12,c_18,c_21,c_493,c_601,c_1049,
% 4.08/0.99                 c_1838,c_3354,c_5534,c_7723]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_8546,plain,
% 4.08/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK4))
% 4.08/0.99      | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3)
% 4.08/0.99      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),sK3)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_8534,c_0]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_524,plain,
% 4.08/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK4))
% 4.08/0.99      | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
% 4.08/0.99      | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),sK3)
% 4.08/0.99      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK4),sK3)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 4.08/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_9633,plain,
% 4.08/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK4)) ),
% 4.08/0.99      inference(global_propositional_subsumption,
% 4.08/0.99                [status(thm)],
% 4.08/0.99                [c_8546,c_14,c_13,c_12,c_18,c_21,c_493,c_524,c_601,
% 4.08/0.99                 c_1049,c_1838,c_3354,c_5534,c_7723]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_2295,plain,
% 4.08/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),X0)
% 4.08/0.99      | ~ r2_hidden(sK4,X0)
% 4.08/0.99      | sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = sK2 ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_848,c_1254]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_2313,plain,
% 4.08/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),X0)
% 4.08/0.99      | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),X1)
% 4.08/0.99      | ~ r2_hidden(sK4,X0)
% 4.08/0.99      | ~ r2_hidden(sK2,X1) ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_2295,c_848]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_10057,plain,
% 4.08/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),X0)
% 4.08/0.99      | ~ r2_hidden(sK4,X0)
% 4.08/0.99      | ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK4)) ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_9633,c_2313]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_10070,plain,
% 4.08/0.99      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK4),sK3,k2_enumset1(sK2,sK2,sK2,sK2)),X0)
% 4.08/0.99      | ~ r2_hidden(sK4,X0) ),
% 4.08/0.99      inference(forward_subsumption_resolution,
% 4.08/0.99                [status(thm)],
% 4.08/0.99                [c_10057,c_10]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_10635,plain,
% 4.08/0.99      ( ~ r2_hidden(sK4,k2_enumset1(sK2,sK2,sK2,sK4)) ),
% 4.08/0.99      inference(resolution,[status(thm)],[c_10070,c_9633]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_9,plain,
% 4.08/0.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 4.08/0.99      inference(cnf_transformation,[],[f61]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_5494,plain,
% 4.08/0.99      ( r2_hidden(sK4,k2_enumset1(X0,X0,X0,sK4)) ),
% 4.08/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(c_5500,plain,
% 4.08/0.99      ( r2_hidden(sK4,k2_enumset1(sK2,sK2,sK2,sK4)) ),
% 4.08/0.99      inference(instantiation,[status(thm)],[c_5494]) ).
% 4.08/0.99  
% 4.08/0.99  cnf(contradiction,plain,
% 4.08/0.99      ( $false ),
% 4.08/0.99      inference(minisat,[status(thm)],[c_10635,c_5500]) ).
% 4.08/0.99  
% 4.08/0.99  
% 4.08/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.08/0.99  
% 4.08/0.99  ------                               Statistics
% 4.08/0.99  
% 4.08/0.99  ------ Selected
% 4.08/0.99  
% 4.08/0.99  total_time:                             0.456
% 4.08/0.99  
%------------------------------------------------------------------------------
