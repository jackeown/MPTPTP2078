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
% DateTime   : Thu Dec  3 11:35:06 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 144 expanded)
%              Number of clauses        :   30 (  33 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  239 ( 636 expanded)
%              Number of equality atoms :  103 ( 211 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f74,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)
      & ~ r1_xboole_0(k1_tarski(sK3),sK4) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)
    & ~ r1_xboole_0(k1_tarski(sK3),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f29])).

fof(f53,plain,(
    ~ r1_xboole_0(k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f53,f56])).

fof(f54,plain,(
    k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f67,plain,(
    k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f54,f41,f56,f56])).

cnf(c_391,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_907,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_2251,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_907])).

cnf(c_12844,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2251])).

cnf(c_389,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2525,plain,
    ( X0 != X1
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != X1
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_8435,plain,
    ( sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != X0
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_2525])).

cnf(c_8436,plain,
    ( sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != sK3
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_8435])).

cnf(c_388,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5368,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3441,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(X0,X0,X0,X0))
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3443,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_3441])).

cnf(c_2515,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(X0,X0,X0,X0))
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2517,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_2515])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_742,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_707,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_709,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_688,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_690,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_138,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_19,negated_conjecture,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_255,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != X0
    | k4_xboole_0(X0,X1) != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_138,c_19])).

cnf(c_256,plain,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_255])).

cnf(c_18,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12844,c_8436,c_5368,c_3443,c_2517,c_742,c_707,c_709,c_688,c_690,c_256,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.53/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.53/0.99  
% 3.53/0.99  ------  iProver source info
% 3.53/0.99  
% 3.53/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.53/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.53/0.99  git: non_committed_changes: false
% 3.53/0.99  git: last_make_outside_of_git: false
% 3.53/0.99  
% 3.53/0.99  ------ 
% 3.53/0.99  
% 3.53/0.99  ------ Input Options
% 3.53/0.99  
% 3.53/0.99  --out_options                           all
% 3.53/0.99  --tptp_safe_out                         true
% 3.53/0.99  --problem_path                          ""
% 3.53/0.99  --include_path                          ""
% 3.53/0.99  --clausifier                            res/vclausify_rel
% 3.53/0.99  --clausifier_options                    ""
% 3.53/0.99  --stdin                                 false
% 3.53/0.99  --stats_out                             all
% 3.53/0.99  
% 3.53/0.99  ------ General Options
% 3.53/0.99  
% 3.53/0.99  --fof                                   false
% 3.53/0.99  --time_out_real                         305.
% 3.53/0.99  --time_out_virtual                      -1.
% 3.53/0.99  --symbol_type_check                     false
% 3.53/0.99  --clausify_out                          false
% 3.53/0.99  --sig_cnt_out                           false
% 3.53/0.99  --trig_cnt_out                          false
% 3.53/0.99  --trig_cnt_out_tolerance                1.
% 3.53/0.99  --trig_cnt_out_sk_spl                   false
% 3.53/0.99  --abstr_cl_out                          false
% 3.53/0.99  
% 3.53/0.99  ------ Global Options
% 3.53/0.99  
% 3.53/0.99  --schedule                              default
% 3.53/0.99  --add_important_lit                     false
% 3.53/0.99  --prop_solver_per_cl                    1000
% 3.53/0.99  --min_unsat_core                        false
% 3.53/0.99  --soft_assumptions                      false
% 3.53/0.99  --soft_lemma_size                       3
% 3.53/0.99  --prop_impl_unit_size                   0
% 3.53/0.99  --prop_impl_unit                        []
% 3.53/0.99  --share_sel_clauses                     true
% 3.53/0.99  --reset_solvers                         false
% 3.53/0.99  --bc_imp_inh                            [conj_cone]
% 3.53/0.99  --conj_cone_tolerance                   3.
% 3.53/0.99  --extra_neg_conj                        none
% 3.53/0.99  --large_theory_mode                     true
% 3.53/0.99  --prolific_symb_bound                   200
% 3.53/0.99  --lt_threshold                          2000
% 3.53/0.99  --clause_weak_htbl                      true
% 3.53/0.99  --gc_record_bc_elim                     false
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing Options
% 3.53/0.99  
% 3.53/0.99  --preprocessing_flag                    true
% 3.53/0.99  --time_out_prep_mult                    0.1
% 3.53/0.99  --splitting_mode                        input
% 3.53/0.99  --splitting_grd                         true
% 3.53/0.99  --splitting_cvd                         false
% 3.53/0.99  --splitting_cvd_svl                     false
% 3.53/0.99  --splitting_nvd                         32
% 3.53/0.99  --sub_typing                            true
% 3.53/0.99  --prep_gs_sim                           true
% 3.53/0.99  --prep_unflatten                        true
% 3.53/0.99  --prep_res_sim                          true
% 3.53/0.99  --prep_upred                            true
% 3.53/0.99  --prep_sem_filter                       exhaustive
% 3.53/0.99  --prep_sem_filter_out                   false
% 3.53/0.99  --pred_elim                             true
% 3.53/0.99  --res_sim_input                         true
% 3.53/0.99  --eq_ax_congr_red                       true
% 3.53/0.99  --pure_diseq_elim                       true
% 3.53/0.99  --brand_transform                       false
% 3.53/0.99  --non_eq_to_eq                          false
% 3.53/0.99  --prep_def_merge                        true
% 3.53/0.99  --prep_def_merge_prop_impl              false
% 3.53/0.99  --prep_def_merge_mbd                    true
% 3.53/0.99  --prep_def_merge_tr_red                 false
% 3.53/0.99  --prep_def_merge_tr_cl                  false
% 3.53/0.99  --smt_preprocessing                     true
% 3.53/0.99  --smt_ac_axioms                         fast
% 3.53/0.99  --preprocessed_out                      false
% 3.53/0.99  --preprocessed_stats                    false
% 3.53/0.99  
% 3.53/0.99  ------ Abstraction refinement Options
% 3.53/0.99  
% 3.53/0.99  --abstr_ref                             []
% 3.53/0.99  --abstr_ref_prep                        false
% 3.53/0.99  --abstr_ref_until_sat                   false
% 3.53/0.99  --abstr_ref_sig_restrict                funpre
% 3.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/0.99  --abstr_ref_under                       []
% 3.53/0.99  
% 3.53/0.99  ------ SAT Options
% 3.53/0.99  
% 3.53/0.99  --sat_mode                              false
% 3.53/0.99  --sat_fm_restart_options                ""
% 3.53/0.99  --sat_gr_def                            false
% 3.53/0.99  --sat_epr_types                         true
% 3.53/0.99  --sat_non_cyclic_types                  false
% 3.53/0.99  --sat_finite_models                     false
% 3.53/0.99  --sat_fm_lemmas                         false
% 3.53/0.99  --sat_fm_prep                           false
% 3.53/0.99  --sat_fm_uc_incr                        true
% 3.53/0.99  --sat_out_model                         small
% 3.53/0.99  --sat_out_clauses                       false
% 3.53/0.99  
% 3.53/0.99  ------ QBF Options
% 3.53/0.99  
% 3.53/0.99  --qbf_mode                              false
% 3.53/0.99  --qbf_elim_univ                         false
% 3.53/0.99  --qbf_dom_inst                          none
% 3.53/0.99  --qbf_dom_pre_inst                      false
% 3.53/0.99  --qbf_sk_in                             false
% 3.53/0.99  --qbf_pred_elim                         true
% 3.53/0.99  --qbf_split                             512
% 3.53/0.99  
% 3.53/0.99  ------ BMC1 Options
% 3.53/0.99  
% 3.53/0.99  --bmc1_incremental                      false
% 3.53/0.99  --bmc1_axioms                           reachable_all
% 3.53/0.99  --bmc1_min_bound                        0
% 3.53/0.99  --bmc1_max_bound                        -1
% 3.53/0.99  --bmc1_max_bound_default                -1
% 3.53/0.99  --bmc1_symbol_reachability              true
% 3.53/0.99  --bmc1_property_lemmas                  false
% 3.53/0.99  --bmc1_k_induction                      false
% 3.53/0.99  --bmc1_non_equiv_states                 false
% 3.53/0.99  --bmc1_deadlock                         false
% 3.53/0.99  --bmc1_ucm                              false
% 3.53/0.99  --bmc1_add_unsat_core                   none
% 3.53/0.99  --bmc1_unsat_core_children              false
% 3.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/0.99  --bmc1_out_stat                         full
% 3.53/0.99  --bmc1_ground_init                      false
% 3.53/0.99  --bmc1_pre_inst_next_state              false
% 3.53/0.99  --bmc1_pre_inst_state                   false
% 3.53/0.99  --bmc1_pre_inst_reach_state             false
% 3.53/0.99  --bmc1_out_unsat_core                   false
% 3.53/0.99  --bmc1_aig_witness_out                  false
% 3.53/0.99  --bmc1_verbose                          false
% 3.53/0.99  --bmc1_dump_clauses_tptp                false
% 3.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.53/0.99  --bmc1_dump_file                        -
% 3.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.53/0.99  --bmc1_ucm_extend_mode                  1
% 3.53/0.99  --bmc1_ucm_init_mode                    2
% 3.53/0.99  --bmc1_ucm_cone_mode                    none
% 3.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.53/0.99  --bmc1_ucm_relax_model                  4
% 3.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/0.99  --bmc1_ucm_layered_model                none
% 3.53/0.99  --bmc1_ucm_max_lemma_size               10
% 3.53/0.99  
% 3.53/0.99  ------ AIG Options
% 3.53/0.99  
% 3.53/0.99  --aig_mode                              false
% 3.53/0.99  
% 3.53/0.99  ------ Instantiation Options
% 3.53/0.99  
% 3.53/0.99  --instantiation_flag                    true
% 3.53/0.99  --inst_sos_flag                         true
% 3.53/0.99  --inst_sos_phase                        true
% 3.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel_side                     num_symb
% 3.53/0.99  --inst_solver_per_active                1400
% 3.53/0.99  --inst_solver_calls_frac                1.
% 3.53/0.99  --inst_passive_queue_type               priority_queues
% 3.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/0.99  --inst_passive_queues_freq              [25;2]
% 3.53/0.99  --inst_dismatching                      true
% 3.53/0.99  --inst_eager_unprocessed_to_passive     true
% 3.53/0.99  --inst_prop_sim_given                   true
% 3.53/0.99  --inst_prop_sim_new                     false
% 3.53/0.99  --inst_subs_new                         false
% 3.53/0.99  --inst_eq_res_simp                      false
% 3.53/0.99  --inst_subs_given                       false
% 3.53/0.99  --inst_orphan_elimination               true
% 3.53/0.99  --inst_learning_loop_flag               true
% 3.53/0.99  --inst_learning_start                   3000
% 3.53/0.99  --inst_learning_factor                  2
% 3.53/0.99  --inst_start_prop_sim_after_learn       3
% 3.53/0.99  --inst_sel_renew                        solver
% 3.53/0.99  --inst_lit_activity_flag                true
% 3.53/0.99  --inst_restr_to_given                   false
% 3.53/0.99  --inst_activity_threshold               500
% 3.53/0.99  --inst_out_proof                        true
% 3.53/0.99  
% 3.53/0.99  ------ Resolution Options
% 3.53/0.99  
% 3.53/0.99  --resolution_flag                       true
% 3.53/0.99  --res_lit_sel                           adaptive
% 3.53/0.99  --res_lit_sel_side                      none
% 3.53/0.99  --res_ordering                          kbo
% 3.53/0.99  --res_to_prop_solver                    active
% 3.53/0.99  --res_prop_simpl_new                    false
% 3.53/0.99  --res_prop_simpl_given                  true
% 3.53/0.99  --res_passive_queue_type                priority_queues
% 3.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/0.99  --res_passive_queues_freq               [15;5]
% 3.53/0.99  --res_forward_subs                      full
% 3.53/0.99  --res_backward_subs                     full
% 3.53/0.99  --res_forward_subs_resolution           true
% 3.53/0.99  --res_backward_subs_resolution          true
% 3.53/0.99  --res_orphan_elimination                true
% 3.53/0.99  --res_time_limit                        2.
% 3.53/0.99  --res_out_proof                         true
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Options
% 3.53/0.99  
% 3.53/0.99  --superposition_flag                    true
% 3.53/0.99  --sup_passive_queue_type                priority_queues
% 3.53/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.53/0.99  --demod_completeness_check              fast
% 3.53/0.99  --demod_use_ground                      true
% 3.53/0.99  --sup_to_prop_solver                    passive
% 3.53/0.99  --sup_prop_simpl_new                    true
% 3.53/0.99  --sup_prop_simpl_given                  true
% 3.53/0.99  --sup_fun_splitting                     true
% 3.53/0.99  --sup_smt_interval                      50000
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Simplification Setup
% 3.53/0.99  
% 3.53/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.53/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.53/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.53/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.53/0.99  --sup_immed_triv                        [TrivRules]
% 3.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.99  --sup_immed_bw_main                     []
% 3.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.99  --sup_input_bw                          []
% 3.53/0.99  
% 3.53/0.99  ------ Combination Options
% 3.53/0.99  
% 3.53/0.99  --comb_res_mult                         3
% 3.53/0.99  --comb_sup_mult                         2
% 3.53/0.99  --comb_inst_mult                        10
% 3.53/0.99  
% 3.53/0.99  ------ Debug Options
% 3.53/0.99  
% 3.53/0.99  --dbg_backtrace                         false
% 3.53/0.99  --dbg_dump_prop_clauses                 false
% 3.53/0.99  --dbg_dump_prop_clauses_file            -
% 3.53/0.99  --dbg_out_stat                          false
% 3.53/0.99  ------ Parsing...
% 3.53/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/0.99  ------ Proving...
% 3.53/0.99  ------ Problem Properties 
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  clauses                                 19
% 3.53/0.99  conjectures                             1
% 3.53/0.99  EPR                                     0
% 3.53/0.99  Horn                                    12
% 3.53/0.99  unary                                   6
% 3.53/0.99  binary                                  5
% 3.53/0.99  lits                                    41
% 3.53/0.99  lits eq                                 22
% 3.53/0.99  fd_pure                                 0
% 3.53/0.99  fd_pseudo                               0
% 3.53/0.99  fd_cond                                 0
% 3.53/0.99  fd_pseudo_cond                          7
% 3.53/0.99  AC symbols                              0
% 3.53/0.99  
% 3.53/0.99  ------ Schedule dynamic 5 is on 
% 3.53/0.99  
% 3.53/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  ------ 
% 3.53/0.99  Current options:
% 3.53/0.99  ------ 
% 3.53/0.99  
% 3.53/0.99  ------ Input Options
% 3.53/0.99  
% 3.53/0.99  --out_options                           all
% 3.53/0.99  --tptp_safe_out                         true
% 3.53/0.99  --problem_path                          ""
% 3.53/0.99  --include_path                          ""
% 3.53/0.99  --clausifier                            res/vclausify_rel
% 3.53/0.99  --clausifier_options                    ""
% 3.53/0.99  --stdin                                 false
% 3.53/0.99  --stats_out                             all
% 3.53/0.99  
% 3.53/0.99  ------ General Options
% 3.53/0.99  
% 3.53/0.99  --fof                                   false
% 3.53/0.99  --time_out_real                         305.
% 3.53/0.99  --time_out_virtual                      -1.
% 3.53/0.99  --symbol_type_check                     false
% 3.53/0.99  --clausify_out                          false
% 3.53/0.99  --sig_cnt_out                           false
% 3.53/0.99  --trig_cnt_out                          false
% 3.53/0.99  --trig_cnt_out_tolerance                1.
% 3.53/0.99  --trig_cnt_out_sk_spl                   false
% 3.53/0.99  --abstr_cl_out                          false
% 3.53/0.99  
% 3.53/0.99  ------ Global Options
% 3.53/0.99  
% 3.53/0.99  --schedule                              default
% 3.53/0.99  --add_important_lit                     false
% 3.53/0.99  --prop_solver_per_cl                    1000
% 3.53/0.99  --min_unsat_core                        false
% 3.53/0.99  --soft_assumptions                      false
% 3.53/0.99  --soft_lemma_size                       3
% 3.53/0.99  --prop_impl_unit_size                   0
% 3.53/0.99  --prop_impl_unit                        []
% 3.53/0.99  --share_sel_clauses                     true
% 3.53/0.99  --reset_solvers                         false
% 3.53/0.99  --bc_imp_inh                            [conj_cone]
% 3.53/0.99  --conj_cone_tolerance                   3.
% 3.53/0.99  --extra_neg_conj                        none
% 3.53/0.99  --large_theory_mode                     true
% 3.53/0.99  --prolific_symb_bound                   200
% 3.53/0.99  --lt_threshold                          2000
% 3.53/0.99  --clause_weak_htbl                      true
% 3.53/0.99  --gc_record_bc_elim                     false
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing Options
% 3.53/0.99  
% 3.53/0.99  --preprocessing_flag                    true
% 3.53/0.99  --time_out_prep_mult                    0.1
% 3.53/0.99  --splitting_mode                        input
% 3.53/0.99  --splitting_grd                         true
% 3.53/0.99  --splitting_cvd                         false
% 3.53/0.99  --splitting_cvd_svl                     false
% 3.53/0.99  --splitting_nvd                         32
% 3.53/0.99  --sub_typing                            true
% 3.53/0.99  --prep_gs_sim                           true
% 3.53/0.99  --prep_unflatten                        true
% 3.53/0.99  --prep_res_sim                          true
% 3.53/0.99  --prep_upred                            true
% 3.53/0.99  --prep_sem_filter                       exhaustive
% 3.53/0.99  --prep_sem_filter_out                   false
% 3.53/0.99  --pred_elim                             true
% 3.53/0.99  --res_sim_input                         true
% 3.53/0.99  --eq_ax_congr_red                       true
% 3.53/0.99  --pure_diseq_elim                       true
% 3.53/0.99  --brand_transform                       false
% 3.53/0.99  --non_eq_to_eq                          false
% 3.53/0.99  --prep_def_merge                        true
% 3.53/0.99  --prep_def_merge_prop_impl              false
% 3.53/0.99  --prep_def_merge_mbd                    true
% 3.53/0.99  --prep_def_merge_tr_red                 false
% 3.53/0.99  --prep_def_merge_tr_cl                  false
% 3.53/0.99  --smt_preprocessing                     true
% 3.53/0.99  --smt_ac_axioms                         fast
% 3.53/0.99  --preprocessed_out                      false
% 3.53/0.99  --preprocessed_stats                    false
% 3.53/0.99  
% 3.53/0.99  ------ Abstraction refinement Options
% 3.53/0.99  
% 3.53/0.99  --abstr_ref                             []
% 3.53/0.99  --abstr_ref_prep                        false
% 3.53/0.99  --abstr_ref_until_sat                   false
% 3.53/0.99  --abstr_ref_sig_restrict                funpre
% 3.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/0.99  --abstr_ref_under                       []
% 3.53/0.99  
% 3.53/0.99  ------ SAT Options
% 3.53/0.99  
% 3.53/0.99  --sat_mode                              false
% 3.53/0.99  --sat_fm_restart_options                ""
% 3.53/0.99  --sat_gr_def                            false
% 3.53/0.99  --sat_epr_types                         true
% 3.53/0.99  --sat_non_cyclic_types                  false
% 3.53/0.99  --sat_finite_models                     false
% 3.53/0.99  --sat_fm_lemmas                         false
% 3.53/0.99  --sat_fm_prep                           false
% 3.53/0.99  --sat_fm_uc_incr                        true
% 3.53/0.99  --sat_out_model                         small
% 3.53/0.99  --sat_out_clauses                       false
% 3.53/0.99  
% 3.53/0.99  ------ QBF Options
% 3.53/0.99  
% 3.53/0.99  --qbf_mode                              false
% 3.53/0.99  --qbf_elim_univ                         false
% 3.53/0.99  --qbf_dom_inst                          none
% 3.53/0.99  --qbf_dom_pre_inst                      false
% 3.53/0.99  --qbf_sk_in                             false
% 3.53/0.99  --qbf_pred_elim                         true
% 3.53/0.99  --qbf_split                             512
% 3.53/0.99  
% 3.53/0.99  ------ BMC1 Options
% 3.53/0.99  
% 3.53/0.99  --bmc1_incremental                      false
% 3.53/0.99  --bmc1_axioms                           reachable_all
% 3.53/0.99  --bmc1_min_bound                        0
% 3.53/0.99  --bmc1_max_bound                        -1
% 3.53/0.99  --bmc1_max_bound_default                -1
% 3.53/0.99  --bmc1_symbol_reachability              true
% 3.53/0.99  --bmc1_property_lemmas                  false
% 3.53/0.99  --bmc1_k_induction                      false
% 3.53/0.99  --bmc1_non_equiv_states                 false
% 3.53/0.99  --bmc1_deadlock                         false
% 3.53/0.99  --bmc1_ucm                              false
% 3.53/0.99  --bmc1_add_unsat_core                   none
% 3.53/0.99  --bmc1_unsat_core_children              false
% 3.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/0.99  --bmc1_out_stat                         full
% 3.53/0.99  --bmc1_ground_init                      false
% 3.53/0.99  --bmc1_pre_inst_next_state              false
% 3.53/0.99  --bmc1_pre_inst_state                   false
% 3.53/0.99  --bmc1_pre_inst_reach_state             false
% 3.53/0.99  --bmc1_out_unsat_core                   false
% 3.53/0.99  --bmc1_aig_witness_out                  false
% 3.53/0.99  --bmc1_verbose                          false
% 3.53/0.99  --bmc1_dump_clauses_tptp                false
% 3.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.53/0.99  --bmc1_dump_file                        -
% 3.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.53/0.99  --bmc1_ucm_extend_mode                  1
% 3.53/0.99  --bmc1_ucm_init_mode                    2
% 3.53/0.99  --bmc1_ucm_cone_mode                    none
% 3.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.53/0.99  --bmc1_ucm_relax_model                  4
% 3.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/0.99  --bmc1_ucm_layered_model                none
% 3.53/0.99  --bmc1_ucm_max_lemma_size               10
% 3.53/0.99  
% 3.53/0.99  ------ AIG Options
% 3.53/0.99  
% 3.53/0.99  --aig_mode                              false
% 3.53/0.99  
% 3.53/0.99  ------ Instantiation Options
% 3.53/0.99  
% 3.53/0.99  --instantiation_flag                    true
% 3.53/0.99  --inst_sos_flag                         true
% 3.53/0.99  --inst_sos_phase                        true
% 3.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel_side                     none
% 3.53/0.99  --inst_solver_per_active                1400
% 3.53/0.99  --inst_solver_calls_frac                1.
% 3.53/0.99  --inst_passive_queue_type               priority_queues
% 3.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/0.99  --inst_passive_queues_freq              [25;2]
% 3.53/0.99  --inst_dismatching                      true
% 3.53/0.99  --inst_eager_unprocessed_to_passive     true
% 3.53/0.99  --inst_prop_sim_given                   true
% 3.53/0.99  --inst_prop_sim_new                     false
% 3.53/0.99  --inst_subs_new                         false
% 3.53/0.99  --inst_eq_res_simp                      false
% 3.53/0.99  --inst_subs_given                       false
% 3.53/0.99  --inst_orphan_elimination               true
% 3.53/0.99  --inst_learning_loop_flag               true
% 3.53/0.99  --inst_learning_start                   3000
% 3.53/0.99  --inst_learning_factor                  2
% 3.53/0.99  --inst_start_prop_sim_after_learn       3
% 3.53/0.99  --inst_sel_renew                        solver
% 3.53/0.99  --inst_lit_activity_flag                true
% 3.53/0.99  --inst_restr_to_given                   false
% 3.53/0.99  --inst_activity_threshold               500
% 3.53/0.99  --inst_out_proof                        true
% 3.53/0.99  
% 3.53/0.99  ------ Resolution Options
% 3.53/0.99  
% 3.53/0.99  --resolution_flag                       false
% 3.53/0.99  --res_lit_sel                           adaptive
% 3.53/0.99  --res_lit_sel_side                      none
% 3.53/0.99  --res_ordering                          kbo
% 3.53/0.99  --res_to_prop_solver                    active
% 3.53/0.99  --res_prop_simpl_new                    false
% 3.53/0.99  --res_prop_simpl_given                  true
% 3.53/0.99  --res_passive_queue_type                priority_queues
% 3.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/0.99  --res_passive_queues_freq               [15;5]
% 3.53/0.99  --res_forward_subs                      full
% 3.53/0.99  --res_backward_subs                     full
% 3.53/0.99  --res_forward_subs_resolution           true
% 3.53/0.99  --res_backward_subs_resolution          true
% 3.53/0.99  --res_orphan_elimination                true
% 3.53/0.99  --res_time_limit                        2.
% 3.53/0.99  --res_out_proof                         true
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Options
% 3.53/0.99  
% 3.53/0.99  --superposition_flag                    true
% 3.53/0.99  --sup_passive_queue_type                priority_queues
% 3.53/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.53/0.99  --demod_completeness_check              fast
% 3.53/0.99  --demod_use_ground                      true
% 3.53/0.99  --sup_to_prop_solver                    passive
% 3.53/0.99  --sup_prop_simpl_new                    true
% 3.53/0.99  --sup_prop_simpl_given                  true
% 3.53/0.99  --sup_fun_splitting                     true
% 3.53/0.99  --sup_smt_interval                      50000
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Simplification Setup
% 3.53/0.99  
% 3.53/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.53/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.53/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.53/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.53/0.99  --sup_immed_triv                        [TrivRules]
% 3.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.99  --sup_immed_bw_main                     []
% 3.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.99  --sup_input_bw                          []
% 3.53/0.99  
% 3.53/0.99  ------ Combination Options
% 3.53/0.99  
% 3.53/0.99  --comb_res_mult                         3
% 3.53/0.99  --comb_sup_mult                         2
% 3.53/0.99  --comb_inst_mult                        10
% 3.53/0.99  
% 3.53/0.99  ------ Debug Options
% 3.53/0.99  
% 3.53/0.99  --dbg_backtrace                         false
% 3.53/0.99  --dbg_dump_prop_clauses                 false
% 3.53/0.99  --dbg_dump_prop_clauses_file            -
% 3.53/0.99  --dbg_out_stat                          false
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  ------ Proving...
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  % SZS status Theorem for theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  fof(f7,axiom,(
% 3.53/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f23,plain,(
% 3.53/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.53/0.99    inference(nnf_transformation,[],[f7])).
% 3.53/0.99  
% 3.53/0.99  fof(f24,plain,(
% 3.53/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.53/0.99    inference(rectify,[],[f23])).
% 3.53/0.99  
% 3.53/0.99  fof(f25,plain,(
% 3.53/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f26,plain,(
% 3.53/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.53/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).
% 3.53/0.99  
% 3.53/0.99  fof(f44,plain,(
% 3.53/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.53/0.99    inference(cnf_transformation,[],[f26])).
% 3.53/0.99  
% 3.53/0.99  fof(f8,axiom,(
% 3.53/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f48,plain,(
% 3.53/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f8])).
% 3.53/0.99  
% 3.53/0.99  fof(f9,axiom,(
% 3.53/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f49,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f9])).
% 3.53/0.99  
% 3.53/0.99  fof(f10,axiom,(
% 3.53/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f50,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f10])).
% 3.53/0.99  
% 3.53/0.99  fof(f55,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f49,f50])).
% 3.53/0.99  
% 3.53/0.99  fof(f56,plain,(
% 3.53/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f48,f55])).
% 3.53/0.99  
% 3.53/0.99  fof(f64,plain,(
% 3.53/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.53/0.99    inference(definition_unfolding,[],[f44,f56])).
% 3.53/0.99  
% 3.53/0.99  fof(f74,plain,(
% 3.53/0.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 3.53/0.99    inference(equality_resolution,[],[f64])).
% 3.53/0.99  
% 3.53/0.99  fof(f2,axiom,(
% 3.53/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f16,plain,(
% 3.53/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.53/0.99    inference(nnf_transformation,[],[f2])).
% 3.53/0.99  
% 3.53/0.99  fof(f17,plain,(
% 3.53/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.53/0.99    inference(flattening,[],[f16])).
% 3.53/0.99  
% 3.53/0.99  fof(f18,plain,(
% 3.53/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.53/0.99    inference(rectify,[],[f17])).
% 3.53/0.99  
% 3.53/0.99  fof(f19,plain,(
% 3.53/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f20,plain,(
% 3.53/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.53/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 3.53/0.99  
% 3.53/0.99  fof(f33,plain,(
% 3.53/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.53/0.99    inference(cnf_transformation,[],[f20])).
% 3.53/0.99  
% 3.53/0.99  fof(f70,plain,(
% 3.53/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.53/0.99    inference(equality_resolution,[],[f33])).
% 3.53/0.99  
% 3.53/0.99  fof(f37,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f20])).
% 3.53/0.99  
% 3.53/0.99  fof(f35,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f20])).
% 3.53/0.99  
% 3.53/0.99  fof(f6,axiom,(
% 3.53/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f22,plain,(
% 3.53/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.53/0.99    inference(nnf_transformation,[],[f6])).
% 3.53/0.99  
% 3.53/0.99  fof(f43,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.53/0.99    inference(cnf_transformation,[],[f22])).
% 3.53/0.99  
% 3.53/0.99  fof(f12,conjecture,(
% 3.53/0.99    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r1_xboole_0(k1_tarski(X0),X1))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f13,negated_conjecture,(
% 3.53/0.99    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r1_xboole_0(k1_tarski(X0),X1))),
% 3.53/0.99    inference(negated_conjecture,[],[f12])).
% 3.53/0.99  
% 3.53/0.99  fof(f15,plain,(
% 3.53/0.99    ? [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 3.53/0.99    inference(ennf_transformation,[],[f13])).
% 3.53/0.99  
% 3.53/0.99  fof(f29,plain,(
% 3.53/0.99    ? [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) & ~r1_xboole_0(k1_tarski(sK3),sK4))),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f30,plain,(
% 3.53/0.99    k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) & ~r1_xboole_0(k1_tarski(sK3),sK4)),
% 3.53/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f29])).
% 3.53/0.99  
% 3.53/0.99  fof(f53,plain,(
% 3.53/0.99    ~r1_xboole_0(k1_tarski(sK3),sK4)),
% 3.53/0.99    inference(cnf_transformation,[],[f30])).
% 3.53/0.99  
% 3.53/0.99  fof(f68,plain,(
% 3.53/0.99    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 3.53/0.99    inference(definition_unfolding,[],[f53,f56])).
% 3.53/0.99  
% 3.53/0.99  fof(f54,plain,(
% 3.53/0.99    k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)),
% 3.53/0.99    inference(cnf_transformation,[],[f30])).
% 3.53/0.99  
% 3.53/0.99  fof(f5,axiom,(
% 3.53/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f41,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f5])).
% 3.53/0.99  
% 3.53/0.99  fof(f67,plain,(
% 3.53/0.99    k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3)),
% 3.53/0.99    inference(definition_unfolding,[],[f54,f41,f56,f56])).
% 3.53/0.99  
% 3.53/0.99  cnf(c_391,plain,
% 3.53/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.53/0.99      theory(equality) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_907,plain,
% 3.53/0.99      ( ~ r2_hidden(X0,X1)
% 3.53/0.99      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 3.53/0.99      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != X0
% 3.53/0.99      | sK4 != X1 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_391]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2251,plain,
% 3.53/0.99      ( ~ r2_hidden(X0,sK4)
% 3.53/0.99      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 3.53/0.99      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != X0
% 3.53/0.99      | sK4 != sK4 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_907]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_12844,plain,
% 3.53/0.99      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 3.53/0.99      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 3.53/0.99      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
% 3.53/0.99      | sK4 != sK4 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_2251]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_389,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2525,plain,
% 3.53/0.99      ( X0 != X1
% 3.53/0.99      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != X1
% 3.53/0.99      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = X0 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_389]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_8435,plain,
% 3.53/0.99      ( sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != X0
% 3.53/0.99      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
% 3.53/0.99      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != X0 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_2525]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_8436,plain,
% 3.53/0.99      ( sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
% 3.53/0.99      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) != sK3
% 3.53/0.99      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != sK3 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_8435]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_388,plain,( X0 = X0 ),theory(equality) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_5368,plain,
% 3.53/0.99      ( sK4 = sK4 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_388]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_15,plain,
% 3.53/0.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 3.53/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3441,plain,
% 3.53/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(X0,X0,X0,X0))
% 3.53/0.99      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = X0 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3443,plain,
% 3.53/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 3.53/0.99      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_3441]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2515,plain,
% 3.53/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(X0,X0,X0,X0))
% 3.53/0.99      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = X0 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2517,plain,
% 3.53/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 3.53/0.99      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_2515]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_5,plain,
% 3.53/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.53/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_742,plain,
% 3.53/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 3.53/0.99      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1,plain,
% 3.53/0.99      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 3.53/0.99      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.53/0.99      | r2_hidden(sK0(X0,X1,X2),X1)
% 3.53/0.99      | k4_xboole_0(X0,X1) = X2 ),
% 3.53/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_707,plain,
% 3.53/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 3.53/0.99      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 3.53/0.99      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3,plain,
% 3.53/0.99      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.53/0.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.53/0.99      | k4_xboole_0(X0,X1) = X2 ),
% 3.53/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_709,plain,
% 3.53/0.99      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 3.53/0.99      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_688,plain,
% 3.53/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 3.53/0.99      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 3.53/0.99      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_690,plain,
% 3.53/0.99      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 3.53/0.99      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_10,plain,
% 3.53/0.99      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.53/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_138,plain,
% 3.53/0.99      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.53/0.99      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_19,negated_conjecture,
% 3.53/0.99      ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 3.53/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_255,plain,
% 3.53/0.99      ( k2_enumset1(sK3,sK3,sK3,sK3) != X0
% 3.53/0.99      | k4_xboole_0(X0,X1) != X0
% 3.53/0.99      | sK4 != X1 ),
% 3.53/0.99      inference(resolution_lifted,[status(thm)],[c_138,c_19]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_256,plain,
% 3.53/0.99      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.53/0.99      inference(unflattening,[status(thm)],[c_255]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_18,negated_conjecture,
% 3.53/0.99      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.53/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(contradiction,plain,
% 3.53/0.99      ( $false ),
% 3.53/0.99      inference(minisat,
% 3.53/0.99                [status(thm)],
% 3.53/0.99                [c_12844,c_8436,c_5368,c_3443,c_2517,c_742,c_707,c_709,
% 3.53/0.99                 c_688,c_690,c_256,c_18]) ).
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  ------                               Statistics
% 3.53/0.99  
% 3.53/0.99  ------ General
% 3.53/0.99  
% 3.53/0.99  abstr_ref_over_cycles:                  0
% 3.53/0.99  abstr_ref_under_cycles:                 0
% 3.53/0.99  gc_basic_clause_elim:                   0
% 3.53/0.99  forced_gc_time:                         0
% 3.53/0.99  parsing_time:                           0.011
% 3.53/0.99  unif_index_cands_time:                  0.
% 3.53/0.99  unif_index_add_time:                    0.
% 3.53/0.99  orderings_time:                         0.
% 3.53/0.99  out_proof_time:                         0.01
% 3.53/0.99  total_time:                             0.456
% 3.53/0.99  num_of_symbols:                         41
% 3.53/0.99  num_of_terms:                           13624
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing
% 3.53/0.99  
% 3.53/0.99  num_of_splits:                          0
% 3.53/0.99  num_of_split_atoms:                     0
% 3.53/0.99  num_of_reused_defs:                     0
% 3.53/0.99  num_eq_ax_congr_red:                    21
% 3.53/0.99  num_of_sem_filtered_clauses:            1
% 3.53/0.99  num_of_subtypes:                        0
% 3.53/0.99  monotx_restored_types:                  0
% 3.53/0.99  sat_num_of_epr_types:                   0
% 3.53/0.99  sat_num_of_non_cyclic_types:            0
% 3.53/0.99  sat_guarded_non_collapsed_types:        0
% 3.53/0.99  num_pure_diseq_elim:                    0
% 3.53/0.99  simp_replaced_by:                       0
% 3.53/0.99  res_preprocessed:                       88
% 3.53/0.99  prep_upred:                             0
% 3.53/0.99  prep_unflattend:                        4
% 3.53/0.99  smt_new_axioms:                         0
% 3.53/0.99  pred_elim_cands:                        1
% 3.53/0.99  pred_elim:                              1
% 3.53/0.99  pred_elim_cl:                           1
% 3.53/0.99  pred_elim_cycles:                       3
% 3.53/0.99  merged_defs:                            10
% 3.53/0.99  merged_defs_ncl:                        0
% 3.53/0.99  bin_hyper_res:                          10
% 3.53/0.99  prep_cycles:                            4
% 3.53/0.99  pred_elim_time:                         0.001
% 3.53/0.99  splitting_time:                         0.
% 3.53/0.99  sem_filter_time:                        0.
% 3.53/0.99  monotx_time:                            0.001
% 3.53/0.99  subtype_inf_time:                       0.
% 3.53/0.99  
% 3.53/0.99  ------ Problem properties
% 3.53/0.99  
% 3.53/0.99  clauses:                                19
% 3.53/0.99  conjectures:                            1
% 3.53/0.99  epr:                                    0
% 3.53/0.99  horn:                                   12
% 3.53/0.99  ground:                                 3
% 3.53/0.99  unary:                                  6
% 3.53/0.99  binary:                                 5
% 3.53/0.99  lits:                                   41
% 3.53/0.99  lits_eq:                                22
% 3.53/0.99  fd_pure:                                0
% 3.53/0.99  fd_pseudo:                              0
% 3.53/0.99  fd_cond:                                0
% 3.53/0.99  fd_pseudo_cond:                         7
% 3.53/0.99  ac_symbols:                             0
% 3.53/0.99  
% 3.53/0.99  ------ Propositional Solver
% 3.53/0.99  
% 3.53/0.99  prop_solver_calls:                      29
% 3.53/0.99  prop_fast_solver_calls:                 839
% 3.53/0.99  smt_solver_calls:                       0
% 3.53/0.99  smt_fast_solver_calls:                  0
% 3.53/0.99  prop_num_of_clauses:                    4753
% 3.53/0.99  prop_preprocess_simplified:             10168
% 3.53/0.99  prop_fo_subsumed:                       6
% 3.53/0.99  prop_solver_time:                       0.
% 3.53/0.99  smt_solver_time:                        0.
% 3.53/0.99  smt_fast_solver_time:                   0.
% 3.53/0.99  prop_fast_solver_time:                  0.
% 3.53/0.99  prop_unsat_core_time:                   0.
% 3.53/0.99  
% 3.53/0.99  ------ QBF
% 3.53/0.99  
% 3.53/0.99  qbf_q_res:                              0
% 3.53/0.99  qbf_num_tautologies:                    0
% 3.53/0.99  qbf_prep_cycles:                        0
% 3.53/0.99  
% 3.53/0.99  ------ BMC1
% 3.53/0.99  
% 3.53/0.99  bmc1_current_bound:                     -1
% 3.53/0.99  bmc1_last_solved_bound:                 -1
% 3.53/0.99  bmc1_unsat_core_size:                   -1
% 3.53/0.99  bmc1_unsat_core_parents_size:           -1
% 3.53/0.99  bmc1_merge_next_fun:                    0
% 3.53/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.53/0.99  
% 3.53/0.99  ------ Instantiation
% 3.53/0.99  
% 3.53/0.99  inst_num_of_clauses:                    1330
% 3.53/0.99  inst_num_in_passive:                    174
% 3.53/0.99  inst_num_in_active:                     614
% 3.53/0.99  inst_num_in_unprocessed:                541
% 3.53/0.99  inst_num_of_loops:                      707
% 3.53/0.99  inst_num_of_learning_restarts:          0
% 3.53/0.99  inst_num_moves_active_passive:          91
% 3.53/0.99  inst_lit_activity:                      0
% 3.53/0.99  inst_lit_activity_moves:                0
% 3.53/0.99  inst_num_tautologies:                   0
% 3.53/0.99  inst_num_prop_implied:                  0
% 3.53/0.99  inst_num_existing_simplified:           0
% 3.53/0.99  inst_num_eq_res_simplified:             0
% 3.53/0.99  inst_num_child_elim:                    0
% 3.53/0.99  inst_num_of_dismatching_blockings:      1131
% 3.53/0.99  inst_num_of_non_proper_insts:           1872
% 3.53/0.99  inst_num_of_duplicates:                 0
% 3.53/0.99  inst_inst_num_from_inst_to_res:         0
% 3.53/0.99  inst_dismatching_checking_time:         0.
% 3.53/0.99  
% 3.53/0.99  ------ Resolution
% 3.53/0.99  
% 3.53/0.99  res_num_of_clauses:                     0
% 3.53/0.99  res_num_in_passive:                     0
% 3.53/0.99  res_num_in_active:                      0
% 3.53/0.99  res_num_of_loops:                       92
% 3.53/0.99  res_forward_subset_subsumed:            172
% 3.53/0.99  res_backward_subset_subsumed:           2
% 3.53/0.99  res_forward_subsumed:                   0
% 3.53/0.99  res_backward_subsumed:                  0
% 3.53/0.99  res_forward_subsumption_resolution:     0
% 3.53/0.99  res_backward_subsumption_resolution:    0
% 3.53/0.99  res_clause_to_clause_subsumption:       6306
% 3.53/0.99  res_orphan_elimination:                 0
% 3.53/0.99  res_tautology_del:                      108
% 3.53/0.99  res_num_eq_res_simplified:              0
% 3.53/0.99  res_num_sel_changes:                    0
% 3.53/0.99  res_moves_from_active_to_pass:          0
% 3.53/0.99  
% 3.53/0.99  ------ Superposition
% 3.53/0.99  
% 3.53/0.99  sup_time_total:                         0.
% 3.53/0.99  sup_time_generating:                    0.
% 3.53/0.99  sup_time_sim_full:                      0.
% 3.53/0.99  sup_time_sim_immed:                     0.
% 3.53/0.99  
% 3.53/0.99  sup_num_of_clauses:                     518
% 3.53/0.99  sup_num_in_active:                      133
% 3.53/0.99  sup_num_in_passive:                     385
% 3.53/0.99  sup_num_of_loops:                       140
% 3.53/0.99  sup_fw_superposition:                   1476
% 3.53/0.99  sup_bw_superposition:                   517
% 3.53/0.99  sup_immediate_simplified:               1022
% 3.53/0.99  sup_given_eliminated:                   1
% 3.53/0.99  comparisons_done:                       0
% 3.53/0.99  comparisons_avoided:                    23
% 3.53/0.99  
% 3.53/0.99  ------ Simplifications
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  sim_fw_subset_subsumed:                 107
% 3.53/0.99  sim_bw_subset_subsumed:                 2
% 3.53/0.99  sim_fw_subsumed:                        199
% 3.53/0.99  sim_bw_subsumed:                        17
% 3.53/0.99  sim_fw_subsumption_res:                 0
% 3.53/0.99  sim_bw_subsumption_res:                 0
% 3.53/0.99  sim_tautology_del:                      60
% 3.53/0.99  sim_eq_tautology_del:                   293
% 3.53/0.99  sim_eq_res_simp:                        8
% 3.53/0.99  sim_fw_demodulated:                     630
% 3.53/0.99  sim_bw_demodulated:                     5
% 3.53/0.99  sim_light_normalised:                   507
% 3.53/0.99  sim_joinable_taut:                      0
% 3.53/0.99  sim_joinable_simp:                      0
% 3.53/0.99  sim_ac_normalised:                      0
% 3.53/0.99  sim_smt_subsumption:                    0
% 3.53/0.99  
%------------------------------------------------------------------------------
