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
% DateTime   : Thu Dec  3 11:35:21 EST 2020

% Result     : Theorem 39.73s
% Output     : CNFRefutation 39.73s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_157746)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f56,plain,(
    k4_xboole_0(k1_enumset1(sK2,sK2,sK4),k4_xboole_0(k1_enumset1(sK2,sK2,sK4),sK3)) != k1_enumset1(sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f41,f30,f38,f42])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f4])).

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

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f60,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f53])).

fof(f61,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f60])).

fof(f39,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f29,plain,(
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
    inference(definition_unfolding,[],[f29,f30])).

fof(f28,plain,(
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
    inference(definition_unfolding,[],[f28,f30])).

fof(f31,plain,(
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
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f62,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f54])).

fof(f63,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f62])).

fof(f40,plain,
    ( sK2 = sK4
    | ~ r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_13,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(sK2,sK2,sK4),k4_xboole_0(k1_enumset1(sK2,sK2,sK4),sK3)) != k1_enumset1(sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_175210,plain,
    ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2)) ),
    inference(resolution,[status(thm)],[c_3,c_13])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_40892,plain,
    ( r2_hidden(sK4,k1_enumset1(X0,X0,sK4)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_40894,plain,
    ( r2_hidden(sK4,k1_enumset1(sK2,sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_40892])).

cnf(c_130,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_146318,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
    | k1_enumset1(sK2,sK2,sK4) != X1
    | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) != X0 ),
    inference(instantiation,[status(thm)],[c_130])).

cnf(c_158218,plain,
    ( ~ r2_hidden(X0,k1_enumset1(sK2,sK2,sK4))
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
    | k1_enumset1(sK2,sK2,sK4) != k1_enumset1(sK2,sK2,sK4)
    | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) != X0 ),
    inference(instantiation,[status(thm)],[c_146318])).

cnf(c_158219,plain,
    ( ~ r2_hidden(X0,k1_enumset1(sK2,sK2,sK4))
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
    | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) != X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_158218])).

cnf(c_158311,plain,
    ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
    | ~ r2_hidden(sK4,k1_enumset1(sK2,sK2,sK4))
    | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) != sK4 ),
    inference(instantiation,[status(thm)],[c_158219])).

cnf(c_131,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k1_enumset1(X0,X2,X4) = k1_enumset1(X1,X3,X5) ),
    theory(equality)).

cnf(c_146773,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
    | r2_hidden(X4,k1_enumset1(X5,X6,X7))
    | X5 != X1
    | X6 != X2
    | X7 != X3
    | X4 != X0 ),
    inference(resolution,[status(thm)],[c_131,c_130])).

cnf(c_145922,plain,
    ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2)) ),
    inference(resolution,[status(thm)],[c_3,c_13])).

cnf(c_158718,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X3))
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
    | X0 != sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2))
    | X3 != sK4
    | X1 != sK2
    | X2 != sK2 ),
    inference(resolution,[status(thm)],[c_146773,c_145922])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_672,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
    | ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
    | ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
    | k4_xboole_0(k1_enumset1(sK2,sK2,sK4),k4_xboole_0(k1_enumset1(sK2,sK2,sK4),sK3)) = k1_enumset1(sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_145710,plain,
    ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),sK3) ),
    inference(resolution,[status(thm)],[c_2,c_13])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_145952,plain,
    ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
    | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK2 ),
    inference(resolution,[status(thm)],[c_145710,c_12])).

cnf(c_127,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_145596,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_130,c_127])).

cnf(c_146073,plain,
    ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),X0)
    | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
    | ~ r2_hidden(sK2,X0) ),
    inference(resolution,[status(thm)],[c_145952,c_145596])).

cnf(c_146306,plain,
    ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
    | ~ r2_hidden(sK2,sK3) ),
    inference(factoring,[status(thm)],[c_146073])).

cnf(c_158221,plain,
    ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
    | ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK4))
    | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_158219])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_158982,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_159044,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(X0,X0,X1))
    | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = X0
    | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = X1 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_159046,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
    | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_159044])).

cnf(c_160025,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X3))
    | X0 != sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2))
    | X3 != sK4
    | X1 != sK2
    | X2 != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_158718,c_15,c_13,c_672,c_146306,c_158221,c_158982,c_159046])).

cnf(c_128,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_145716,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | X3 != X2
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X3 ),
    inference(resolution,[status(thm)],[c_2,c_128])).

cnf(c_146061,plain,
    ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
    | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK4
    | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK2 ),
    inference(resolution,[status(thm)],[c_145922,c_12])).

cnf(c_146089,plain,
    ( sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK4
    | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK2 ),
    inference(resolution,[status(thm)],[c_146061,c_12])).

cnf(c_145466,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_128,c_127])).

cnf(c_146279,plain,
    ( sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK2
    | sK4 = sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) ),
    inference(resolution,[status(thm)],[c_146089,c_145466])).

cnf(c_149172,plain,
    ( r2_hidden(sK0(X0,X1,sK2),X1)
    | r2_hidden(sK0(X0,X1,sK2),sK2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2))
    | sK4 = sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) ),
    inference(resolution,[status(thm)],[c_145716,c_146279])).

cnf(c_160133,plain,
    ( r2_hidden(sK0(X0,X1,sK2),X1)
    | r2_hidden(sK0(X0,X1,sK2),sK2)
    | r2_hidden(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_enumset1(X2,X3,X4))
    | X4 != sK4
    | X2 != sK2
    | X3 != sK2
    | sK4 = sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) ),
    inference(resolution,[status(thm)],[c_160025,c_149172])).

cnf(c_22,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_146579,plain,
    ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),X0)
    | ~ r2_hidden(sK2,X0)
    | sK4 = sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) ),
    inference(resolution,[status(thm)],[c_146279,c_145596])).

cnf(c_148187,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
    | ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
    | ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2))
    | k4_xboole_0(k1_enumset1(sK2,sK2,sK4),k4_xboole_0(k1_enumset1(sK2,sK2,sK4),sK3)) = k1_enumset1(sK2,sK2,sK2)
    | sK4 = sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) ),
    inference(resolution,[status(thm)],[c_146579,c_1])).

cnf(c_162186,plain,
    ( sK4 = sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_160133,c_15,c_13,c_22,c_146279,c_146306,c_148187,c_158221,c_158982])).

cnf(c_162192,plain,
    ( sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK4 ),
    inference(resolution,[status(thm)],[c_162186,c_145466])).

cnf(c_175446,plain,
    ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_175210,c_15,c_13,c_672,c_145922,c_146306,c_158221,c_158982,c_159046])).

cnf(c_175458,plain,
    ( sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK4
    | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK2 ),
    inference(resolution,[status(thm)],[c_175446,c_12])).

cnf(c_175716,plain,
    ( sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_175458,c_15,c_13,c_22,c_672,c_146061,c_146306,c_157746,c_158221,c_158982,c_159046])).

cnf(c_174713,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_128,c_127])).

cnf(c_175722,plain,
    ( sK4 = sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) ),
    inference(resolution,[status(thm)],[c_175716,c_174713])).

cnf(c_174840,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_130,c_127])).

cnf(c_175734,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),X0)
    | r2_hidden(sK4,X0) ),
    inference(resolution,[status(thm)],[c_175722,c_174840])).

cnf(c_176185,plain,
    ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
    | r2_hidden(sK4,sK3)
    | k4_xboole_0(k1_enumset1(sK2,sK2,sK4),k4_xboole_0(k1_enumset1(sK2,sK2,sK4),sK3)) = k1_enumset1(sK2,sK2,sK2) ),
    inference(resolution,[status(thm)],[c_175734,c_2])).

cnf(c_160079,plain,
    ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(X0,X1,X2))
    | X2 != sK4
    | X0 != sK2
    | X1 != sK2 ),
    inference(resolution,[status(thm)],[c_160025,c_127])).

cnf(c_161061,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
    | ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
    | k4_xboole_0(k1_enumset1(sK2,sK2,sK4),k4_xboole_0(k1_enumset1(sK2,sK2,sK4),sK3)) = k1_enumset1(sK2,sK2,sK2)
    | sK2 != sK4
    | sK2 != sK2 ),
    inference(resolution,[status(thm)],[c_160079,c_1])).

cnf(c_161062,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
    | ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
    | k4_xboole_0(k1_enumset1(sK2,sK2,sK4),k4_xboole_0(k1_enumset1(sK2,sK2,sK4),sK3)) = k1_enumset1(sK2,sK2,sK2)
    | sK2 != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_161061])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(sK4,sK3)
    | sK2 = sK4 ),
    inference(cnf_transformation,[],[f40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_176185,c_162192,c_161062,c_158311,c_146306,c_40894,c_672,c_13,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:41:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 39.73/5.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.73/5.49  
% 39.73/5.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.73/5.49  
% 39.73/5.49  ------  iProver source info
% 39.73/5.49  
% 39.73/5.49  git: date: 2020-06-30 10:37:57 +0100
% 39.73/5.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.73/5.49  git: non_committed_changes: false
% 39.73/5.49  git: last_make_outside_of_git: false
% 39.73/5.49  
% 39.73/5.49  ------ 
% 39.73/5.49  ------ Parsing...
% 39.73/5.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.73/5.49  
% 39.73/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 39.73/5.49  
% 39.73/5.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.73/5.49  
% 39.73/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.73/5.49  ------ Proving...
% 39.73/5.49  ------ Problem Properties 
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  clauses                                 16
% 39.73/5.49  conjectures                             3
% 39.73/5.49  EPR                                     2
% 39.73/5.49  Horn                                    12
% 39.73/5.49  unary                                   5
% 39.73/5.49  binary                                  3
% 39.73/5.49  lits                                    37
% 39.73/5.49  lits eq                                 15
% 39.73/5.49  fd_pure                                 0
% 39.73/5.49  fd_pseudo                               0
% 39.73/5.49  fd_cond                                 0
% 39.73/5.49  fd_pseudo_cond                          6
% 39.73/5.49  AC symbols                              0
% 39.73/5.49  
% 39.73/5.49  ------ Input Options Time Limit: Unbounded
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 39.73/5.49  Current options:
% 39.73/5.49  ------ 
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  ------ Proving...
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.73/5.49  
% 39.73/5.49  ------ Proving...
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.73/5.49  
% 39.73/5.49  ------ Proving...
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.73/5.49  
% 39.73/5.49  ------ Proving...
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.73/5.49  
% 39.73/5.49  ------ Proving...
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.73/5.49  
% 39.73/5.49  ------ Proving...
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.73/5.49  
% 39.73/5.49  ------ Proving...
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.73/5.49  
% 39.73/5.49  ------ Proving...
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.73/5.49  
% 39.73/5.49  ------ Proving...
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.73/5.49  
% 39.73/5.49  ------ Proving...
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.73/5.49  
% 39.73/5.49  ------ Proving...
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  % SZS status Theorem for theBenchmark.p
% 39.73/5.49  
% 39.73/5.49  % SZS output start CNFRefutation for theBenchmark.p
% 39.73/5.49  
% 39.73/5.49  fof(f2,axiom,(
% 39.73/5.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 39.73/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.73/5.49  
% 39.73/5.49  fof(f11,plain,(
% 39.73/5.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 39.73/5.49    inference(nnf_transformation,[],[f2])).
% 39.73/5.49  
% 39.73/5.49  fof(f12,plain,(
% 39.73/5.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 39.73/5.49    inference(flattening,[],[f11])).
% 39.73/5.49  
% 39.73/5.49  fof(f13,plain,(
% 39.73/5.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 39.73/5.49    inference(rectify,[],[f12])).
% 39.73/5.49  
% 39.73/5.49  fof(f14,plain,(
% 39.73/5.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 39.73/5.49    introduced(choice_axiom,[])).
% 39.73/5.49  
% 39.73/5.49  fof(f15,plain,(
% 39.73/5.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 39.73/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).
% 39.73/5.49  
% 39.73/5.49  fof(f27,plain,(
% 39.73/5.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 39.73/5.49    inference(cnf_transformation,[],[f15])).
% 39.73/5.49  
% 39.73/5.49  fof(f3,axiom,(
% 39.73/5.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 39.73/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.73/5.49  
% 39.73/5.49  fof(f30,plain,(
% 39.73/5.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 39.73/5.49    inference(cnf_transformation,[],[f3])).
% 39.73/5.49  
% 39.73/5.49  fof(f46,plain,(
% 39.73/5.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 39.73/5.49    inference(definition_unfolding,[],[f27,f30])).
% 39.73/5.49  
% 39.73/5.49  fof(f7,conjecture,(
% 39.73/5.49    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))))),
% 39.73/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.73/5.49  
% 39.73/5.49  fof(f8,negated_conjecture,(
% 39.73/5.49    ~! [X0,X1,X2] : (r2_hidden(X0,X1) => (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))))),
% 39.73/5.49    inference(negated_conjecture,[],[f7])).
% 39.73/5.49  
% 39.73/5.49  fof(f9,plain,(
% 39.73/5.49    ? [X0,X1,X2] : ((k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1))) & r2_hidden(X0,X1))),
% 39.73/5.49    inference(ennf_transformation,[],[f8])).
% 39.73/5.49  
% 39.73/5.49  fof(f10,plain,(
% 39.73/5.49    ? [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 39.73/5.49    inference(flattening,[],[f9])).
% 39.73/5.49  
% 39.73/5.49  fof(f21,plain,(
% 39.73/5.49    ? [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1)) => (k3_xboole_0(k2_tarski(sK2,sK4),sK3) != k1_tarski(sK2) & (sK2 = sK4 | ~r2_hidden(sK4,sK3)) & r2_hidden(sK2,sK3))),
% 39.73/5.49    introduced(choice_axiom,[])).
% 39.73/5.49  
% 39.73/5.49  fof(f22,plain,(
% 39.73/5.49    k3_xboole_0(k2_tarski(sK2,sK4),sK3) != k1_tarski(sK2) & (sK2 = sK4 | ~r2_hidden(sK4,sK3)) & r2_hidden(sK2,sK3)),
% 39.73/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f21])).
% 39.73/5.49  
% 39.73/5.49  fof(f41,plain,(
% 39.73/5.49    k3_xboole_0(k2_tarski(sK2,sK4),sK3) != k1_tarski(sK2)),
% 39.73/5.49    inference(cnf_transformation,[],[f22])).
% 39.73/5.49  
% 39.73/5.49  fof(f5,axiom,(
% 39.73/5.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 39.73/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.73/5.49  
% 39.73/5.49  fof(f37,plain,(
% 39.73/5.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 39.73/5.49    inference(cnf_transformation,[],[f5])).
% 39.73/5.49  
% 39.73/5.49  fof(f6,axiom,(
% 39.73/5.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 39.73/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.73/5.49  
% 39.73/5.49  fof(f38,plain,(
% 39.73/5.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 39.73/5.49    inference(cnf_transformation,[],[f6])).
% 39.73/5.49  
% 39.73/5.49  fof(f42,plain,(
% 39.73/5.49    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 39.73/5.49    inference(definition_unfolding,[],[f37,f38])).
% 39.73/5.49  
% 39.73/5.49  fof(f56,plain,(
% 39.73/5.49    k4_xboole_0(k1_enumset1(sK2,sK2,sK4),k4_xboole_0(k1_enumset1(sK2,sK2,sK4),sK3)) != k1_enumset1(sK2,sK2,sK2)),
% 39.73/5.49    inference(definition_unfolding,[],[f41,f30,f38,f42])).
% 39.73/5.49  
% 39.73/5.49  fof(f4,axiom,(
% 39.73/5.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 39.73/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.73/5.49  
% 39.73/5.49  fof(f16,plain,(
% 39.73/5.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 39.73/5.49    inference(nnf_transformation,[],[f4])).
% 39.73/5.49  
% 39.73/5.49  fof(f17,plain,(
% 39.73/5.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 39.73/5.49    inference(flattening,[],[f16])).
% 39.73/5.49  
% 39.73/5.49  fof(f18,plain,(
% 39.73/5.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 39.73/5.49    inference(rectify,[],[f17])).
% 39.73/5.49  
% 39.73/5.49  fof(f19,plain,(
% 39.73/5.49    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 39.73/5.49    introduced(choice_axiom,[])).
% 39.73/5.49  
% 39.73/5.49  fof(f20,plain,(
% 39.73/5.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 39.73/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).
% 39.73/5.49  
% 39.73/5.49  fof(f33,plain,(
% 39.73/5.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 39.73/5.49    inference(cnf_transformation,[],[f20])).
% 39.73/5.49  
% 39.73/5.49  fof(f53,plain,(
% 39.73/5.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 39.73/5.49    inference(definition_unfolding,[],[f33,f38])).
% 39.73/5.49  
% 39.73/5.49  fof(f60,plain,(
% 39.73/5.49    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 39.73/5.49    inference(equality_resolution,[],[f53])).
% 39.73/5.49  
% 39.73/5.49  fof(f61,plain,(
% 39.73/5.49    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 39.73/5.49    inference(equality_resolution,[],[f60])).
% 39.73/5.49  
% 39.73/5.49  fof(f39,plain,(
% 39.73/5.49    r2_hidden(sK2,sK3)),
% 39.73/5.49    inference(cnf_transformation,[],[f22])).
% 39.73/5.49  
% 39.73/5.49  fof(f29,plain,(
% 39.73/5.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 39.73/5.49    inference(cnf_transformation,[],[f15])).
% 39.73/5.49  
% 39.73/5.49  fof(f44,plain,(
% 39.73/5.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 39.73/5.49    inference(definition_unfolding,[],[f29,f30])).
% 39.73/5.49  
% 39.73/5.49  fof(f28,plain,(
% 39.73/5.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 39.73/5.49    inference(cnf_transformation,[],[f15])).
% 39.73/5.49  
% 39.73/5.49  fof(f45,plain,(
% 39.73/5.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 39.73/5.49    inference(definition_unfolding,[],[f28,f30])).
% 39.73/5.49  
% 39.73/5.49  fof(f31,plain,(
% 39.73/5.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 39.73/5.49    inference(cnf_transformation,[],[f20])).
% 39.73/5.49  
% 39.73/5.49  fof(f55,plain,(
% 39.73/5.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 39.73/5.49    inference(definition_unfolding,[],[f31,f38])).
% 39.73/5.49  
% 39.73/5.49  fof(f64,plain,(
% 39.73/5.49    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k1_enumset1(X0,X0,X1))) )),
% 39.73/5.49    inference(equality_resolution,[],[f55])).
% 39.73/5.49  
% 39.73/5.49  fof(f32,plain,(
% 39.73/5.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 39.73/5.49    inference(cnf_transformation,[],[f20])).
% 39.73/5.49  
% 39.73/5.49  fof(f54,plain,(
% 39.73/5.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 39.73/5.49    inference(definition_unfolding,[],[f32,f38])).
% 39.73/5.49  
% 39.73/5.49  fof(f62,plain,(
% 39.73/5.49    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 39.73/5.49    inference(equality_resolution,[],[f54])).
% 39.73/5.49  
% 39.73/5.49  fof(f63,plain,(
% 39.73/5.49    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 39.73/5.49    inference(equality_resolution,[],[f62])).
% 39.73/5.49  
% 39.73/5.49  fof(f40,plain,(
% 39.73/5.49    sK2 = sK4 | ~r2_hidden(sK4,sK3)),
% 39.73/5.49    inference(cnf_transformation,[],[f22])).
% 39.73/5.49  
% 39.73/5.49  cnf(c_3,plain,
% 39.73/5.49      ( r2_hidden(sK0(X0,X1,X2),X0)
% 39.73/5.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 39.73/5.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 39.73/5.49      inference(cnf_transformation,[],[f46]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_13,negated_conjecture,
% 39.73/5.49      ( k4_xboole_0(k1_enumset1(sK2,sK2,sK4),k4_xboole_0(k1_enumset1(sK2,sK2,sK4),sK3)) != k1_enumset1(sK2,sK2,sK2) ),
% 39.73/5.49      inference(cnf_transformation,[],[f56]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_175210,plain,
% 39.73/5.49      ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
% 39.73/5.49      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2)) ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_3,c_13]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_10,plain,
% 39.73/5.49      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
% 39.73/5.49      inference(cnf_transformation,[],[f61]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_40892,plain,
% 39.73/5.49      ( r2_hidden(sK4,k1_enumset1(X0,X0,sK4)) ),
% 39.73/5.49      inference(instantiation,[status(thm)],[c_10]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_40894,plain,
% 39.73/5.49      ( r2_hidden(sK4,k1_enumset1(sK2,sK2,sK4)) ),
% 39.73/5.49      inference(instantiation,[status(thm)],[c_40892]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_130,plain,
% 39.73/5.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 39.73/5.49      theory(equality) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_146318,plain,
% 39.73/5.49      ( ~ r2_hidden(X0,X1)
% 39.73/5.49      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
% 39.73/5.49      | k1_enumset1(sK2,sK2,sK4) != X1
% 39.73/5.49      | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) != X0 ),
% 39.73/5.49      inference(instantiation,[status(thm)],[c_130]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_158218,plain,
% 39.73/5.49      ( ~ r2_hidden(X0,k1_enumset1(sK2,sK2,sK4))
% 39.73/5.49      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
% 39.73/5.49      | k1_enumset1(sK2,sK2,sK4) != k1_enumset1(sK2,sK2,sK4)
% 39.73/5.49      | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) != X0 ),
% 39.73/5.49      inference(instantiation,[status(thm)],[c_146318]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_158219,plain,
% 39.73/5.49      ( ~ r2_hidden(X0,k1_enumset1(sK2,sK2,sK4))
% 39.73/5.49      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
% 39.73/5.49      | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) != X0 ),
% 39.73/5.49      inference(equality_resolution_simp,[status(thm)],[c_158218]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_158311,plain,
% 39.73/5.49      ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
% 39.73/5.49      | ~ r2_hidden(sK4,k1_enumset1(sK2,sK2,sK4))
% 39.73/5.49      | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) != sK4 ),
% 39.73/5.49      inference(instantiation,[status(thm)],[c_158219]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_131,plain,
% 39.73/5.49      ( X0 != X1
% 39.73/5.49      | X2 != X3
% 39.73/5.49      | X4 != X5
% 39.73/5.49      | k1_enumset1(X0,X2,X4) = k1_enumset1(X1,X3,X5) ),
% 39.73/5.49      theory(equality) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_146773,plain,
% 39.73/5.49      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
% 39.73/5.49      | r2_hidden(X4,k1_enumset1(X5,X6,X7))
% 39.73/5.49      | X5 != X1
% 39.73/5.49      | X6 != X2
% 39.73/5.49      | X7 != X3
% 39.73/5.49      | X4 != X0 ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_131,c_130]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_145922,plain,
% 39.73/5.49      ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
% 39.73/5.49      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2)) ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_3,c_13]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_158718,plain,
% 39.73/5.49      ( r2_hidden(X0,k1_enumset1(X1,X2,X3))
% 39.73/5.49      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
% 39.73/5.49      | X0 != sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2))
% 39.73/5.49      | X3 != sK4
% 39.73/5.49      | X1 != sK2
% 39.73/5.49      | X2 != sK2 ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_146773,c_145922]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_15,negated_conjecture,
% 39.73/5.49      ( r2_hidden(sK2,sK3) ),
% 39.73/5.49      inference(cnf_transformation,[],[f39]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_1,plain,
% 39.73/5.49      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 39.73/5.49      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 39.73/5.49      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 39.73/5.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 39.73/5.49      inference(cnf_transformation,[],[f44]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_672,plain,
% 39.73/5.49      ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
% 39.73/5.49      | ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
% 39.73/5.49      | ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
% 39.73/5.49      | k4_xboole_0(k1_enumset1(sK2,sK2,sK4),k4_xboole_0(k1_enumset1(sK2,sK2,sK4),sK3)) = k1_enumset1(sK2,sK2,sK2) ),
% 39.73/5.49      inference(instantiation,[status(thm)],[c_1]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_2,plain,
% 39.73/5.49      ( r2_hidden(sK0(X0,X1,X2),X1)
% 39.73/5.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 39.73/5.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 39.73/5.49      inference(cnf_transformation,[],[f45]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_145710,plain,
% 39.73/5.49      ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
% 39.73/5.49      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),sK3) ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_2,c_13]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_12,plain,
% 39.73/5.49      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 39.73/5.49      inference(cnf_transformation,[],[f64]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_145952,plain,
% 39.73/5.49      ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
% 39.73/5.49      | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK2 ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_145710,c_12]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_127,plain,( X0 = X0 ),theory(equality) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_145596,plain,
% 39.73/5.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_130,c_127]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_146073,plain,
% 39.73/5.49      ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),X0)
% 39.73/5.49      | r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
% 39.73/5.49      | ~ r2_hidden(sK2,X0) ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_145952,c_145596]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_146306,plain,
% 39.73/5.49      ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
% 39.73/5.49      | ~ r2_hidden(sK2,sK3) ),
% 39.73/5.49      inference(factoring,[status(thm)],[c_146073]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_158221,plain,
% 39.73/5.49      ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
% 39.73/5.49      | ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK4))
% 39.73/5.49      | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) != sK2 ),
% 39.73/5.49      inference(instantiation,[status(thm)],[c_158219]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_11,plain,
% 39.73/5.49      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 39.73/5.49      inference(cnf_transformation,[],[f63]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_158982,plain,
% 39.73/5.49      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK4)) ),
% 39.73/5.49      inference(instantiation,[status(thm)],[c_11]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_159044,plain,
% 39.73/5.49      ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(X0,X0,X1))
% 39.73/5.49      | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = X0
% 39.73/5.49      | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = X1 ),
% 39.73/5.49      inference(instantiation,[status(thm)],[c_12]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_159046,plain,
% 39.73/5.49      ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
% 39.73/5.49      | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK2 ),
% 39.73/5.49      inference(instantiation,[status(thm)],[c_159044]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_160025,plain,
% 39.73/5.49      ( r2_hidden(X0,k1_enumset1(X1,X2,X3))
% 39.73/5.49      | X0 != sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2))
% 39.73/5.49      | X3 != sK4
% 39.73/5.49      | X1 != sK2
% 39.73/5.49      | X2 != sK2 ),
% 39.73/5.49      inference(global_propositional_subsumption,
% 39.73/5.49                [status(thm)],
% 39.73/5.49                [c_158718,c_15,c_13,c_672,c_146306,c_158221,c_158982,
% 39.73/5.49                 c_159046]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_128,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_145716,plain,
% 39.73/5.49      ( r2_hidden(sK0(X0,X1,X2),X1)
% 39.73/5.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 39.73/5.49      | X3 != X2
% 39.73/5.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X3 ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_2,c_128]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_146061,plain,
% 39.73/5.49      ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
% 39.73/5.49      | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK4
% 39.73/5.49      | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK2 ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_145922,c_12]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_146089,plain,
% 39.73/5.49      ( sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK4
% 39.73/5.49      | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK2 ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_146061,c_12]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_145466,plain,
% 39.73/5.49      ( X0 != X1 | X1 = X0 ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_128,c_127]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_146279,plain,
% 39.73/5.49      ( sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK2
% 39.73/5.49      | sK4 = sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_146089,c_145466]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_149172,plain,
% 39.73/5.49      ( r2_hidden(sK0(X0,X1,sK2),X1)
% 39.73/5.49      | r2_hidden(sK0(X0,X1,sK2),sK2)
% 39.73/5.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2))
% 39.73/5.49      | sK4 = sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_145716,c_146279]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_160133,plain,
% 39.73/5.49      ( r2_hidden(sK0(X0,X1,sK2),X1)
% 39.73/5.49      | r2_hidden(sK0(X0,X1,sK2),sK2)
% 39.73/5.49      | r2_hidden(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_enumset1(X2,X3,X4))
% 39.73/5.49      | X4 != sK4
% 39.73/5.49      | X2 != sK2
% 39.73/5.49      | X3 != sK2
% 39.73/5.49      | sK4 = sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_160025,c_149172]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_22,plain,
% 39.73/5.49      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) ),
% 39.73/5.49      inference(instantiation,[status(thm)],[c_11]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_146579,plain,
% 39.73/5.49      ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),X0)
% 39.73/5.49      | ~ r2_hidden(sK2,X0)
% 39.73/5.49      | sK4 = sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_146279,c_145596]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_148187,plain,
% 39.73/5.49      ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
% 39.73/5.49      | ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
% 39.73/5.49      | ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2))
% 39.73/5.49      | k4_xboole_0(k1_enumset1(sK2,sK2,sK4),k4_xboole_0(k1_enumset1(sK2,sK2,sK4),sK3)) = k1_enumset1(sK2,sK2,sK2)
% 39.73/5.49      | sK4 = sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_146579,c_1]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_162186,plain,
% 39.73/5.49      ( sK4 = sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) ),
% 39.73/5.49      inference(global_propositional_subsumption,
% 39.73/5.49                [status(thm)],
% 39.73/5.49                [c_160133,c_15,c_13,c_22,c_146279,c_146306,c_148187,
% 39.73/5.49                 c_158221,c_158982]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_162192,plain,
% 39.73/5.49      ( sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK4 ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_162186,c_145466]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_175446,plain,
% 39.73/5.49      ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4)) ),
% 39.73/5.49      inference(global_propositional_subsumption,
% 39.73/5.49                [status(thm)],
% 39.73/5.49                [c_175210,c_15,c_13,c_672,c_145922,c_146306,c_158221,
% 39.73/5.49                 c_158982,c_159046]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_175458,plain,
% 39.73/5.49      ( sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK4
% 39.73/5.49      | sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK2 ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_175446,c_12]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_175716,plain,
% 39.73/5.49      ( sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) = sK4 ),
% 39.73/5.49      inference(global_propositional_subsumption,
% 39.73/5.49                [status(thm)],
% 39.73/5.49                [c_175458,c_15,c_13,c_22,c_672,c_146061,c_146306,
% 39.73/5.49                 c_157746,c_158221,c_158982,c_159046]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_174713,plain,
% 39.73/5.49      ( X0 != X1 | X1 = X0 ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_128,c_127]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_175722,plain,
% 39.73/5.49      ( sK4 = sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)) ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_175716,c_174713]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_174840,plain,
% 39.73/5.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_130,c_127]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_175734,plain,
% 39.73/5.49      ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),X0)
% 39.73/5.49      | r2_hidden(sK4,X0) ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_175722,c_174840]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_176185,plain,
% 39.73/5.49      ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK2))
% 39.73/5.49      | r2_hidden(sK4,sK3)
% 39.73/5.49      | k4_xboole_0(k1_enumset1(sK2,sK2,sK4),k4_xboole_0(k1_enumset1(sK2,sK2,sK4),sK3)) = k1_enumset1(sK2,sK2,sK2) ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_175734,c_2]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_160079,plain,
% 39.73/5.49      ( r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(X0,X1,X2))
% 39.73/5.49      | X2 != sK4
% 39.73/5.49      | X0 != sK2
% 39.73/5.49      | X1 != sK2 ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_160025,c_127]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_161061,plain,
% 39.73/5.49      ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
% 39.73/5.49      | ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
% 39.73/5.49      | k4_xboole_0(k1_enumset1(sK2,sK2,sK4),k4_xboole_0(k1_enumset1(sK2,sK2,sK4),sK3)) = k1_enumset1(sK2,sK2,sK2)
% 39.73/5.49      | sK2 != sK4
% 39.73/5.49      | sK2 != sK2 ),
% 39.73/5.49      inference(resolution,[status(thm)],[c_160079,c_1]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_161062,plain,
% 39.73/5.49      ( ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK2,sK2,sK4))
% 39.73/5.49      | ~ r2_hidden(sK0(k1_enumset1(sK2,sK2,sK4),sK3,k1_enumset1(sK2,sK2,sK2)),sK3)
% 39.73/5.49      | k4_xboole_0(k1_enumset1(sK2,sK2,sK4),k4_xboole_0(k1_enumset1(sK2,sK2,sK4),sK3)) = k1_enumset1(sK2,sK2,sK2)
% 39.73/5.49      | sK2 != sK4 ),
% 39.73/5.49      inference(equality_resolution_simp,[status(thm)],[c_161061]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(c_14,negated_conjecture,
% 39.73/5.49      ( ~ r2_hidden(sK4,sK3) | sK2 = sK4 ),
% 39.73/5.49      inference(cnf_transformation,[],[f40]) ).
% 39.73/5.49  
% 39.73/5.49  cnf(contradiction,plain,
% 39.73/5.49      ( $false ),
% 39.73/5.49      inference(minisat,
% 39.73/5.49                [status(thm)],
% 39.73/5.49                [c_176185,c_162192,c_161062,c_158311,c_146306,c_40894,
% 39.73/5.49                 c_672,c_13,c_14,c_15]) ).
% 39.73/5.49  
% 39.73/5.49  
% 39.73/5.49  % SZS output end CNFRefutation for theBenchmark.p
% 39.73/5.49  
% 39.73/5.49  ------                               Statistics
% 39.73/5.49  
% 39.73/5.49  ------ Selected
% 39.73/5.49  
% 39.73/5.49  total_time:                             4.935
% 39.73/5.49  
%------------------------------------------------------------------------------
