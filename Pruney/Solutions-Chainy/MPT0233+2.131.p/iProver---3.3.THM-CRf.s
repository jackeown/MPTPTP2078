%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:31 EST 2020

% Result     : Theorem 11.12s
% Output     : CNFRefutation 11.12s
% Verified   : 
% Statistics : Number of formulae       :  138 (1431 expanded)
%              Number of clauses        :   72 ( 325 expanded)
%              Number of leaves         :   19 ( 385 expanded)
%              Depth                    :   30
%              Number of atoms          :  430 (3906 expanded)
%              Number of equality atoms :  333 (3025 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK1 != sK4
      & sK1 != sK3
      & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( sK1 != sK4
    & sK1 != sK3
    & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f30])).

fof(f56,plain,(
    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f78,plain,(
    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f56,f59,f59])).

fof(f57,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f53,f59])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f59])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f28])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f47,f59,f59])).

fof(f58,plain,(
    sK1 != sK4 ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f40,f59])).

fof(f83,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k5_enumset1(X4,X4,X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f67])).

fof(f84,plain,(
    ! [X4,X1] : r2_hidden(X4,k5_enumset1(X4,X4,X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f83])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f39,f59])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k1_tarski(X0)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( X1 = X2
      | k2_tarski(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | k2_tarski(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) != k1_tarski(X0) ) ),
    inference(definition_unfolding,[],[f55,f59])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( X0 = X1
      | k2_tarski(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | k2_tarski(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) != k1_tarski(X0) ) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f89,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f72])).

cnf(c_627,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | k5_enumset1(X0,X2,X4,X6,X8,X10,X12) = k5_enumset1(X1,X3,X5,X7,X9,X11,X13) ),
    theory(equality)).

cnf(c_624,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4404,plain,
    ( ~ r1_tarski(X0,k5_enumset1(X1,X2,X3,X4,X5,X6,X7))
    | r1_tarski(X8,k5_enumset1(X9,X10,X11,X12,X13,X14,X15))
    | X8 != X0
    | X9 != X1
    | X10 != X2
    | X11 != X3
    | X12 != X4
    | X13 != X5
    | X14 != X6
    | X15 != X7 ),
    inference(resolution,[status(thm)],[c_627,c_624])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_22137,plain,
    ( r1_tarski(X0,k5_enumset1(X1,X2,X3,X4,X5,X6,X7))
    | X0 != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | X1 != sK3
    | X2 != sK3
    | X3 != sK3
    | X4 != sK3
    | X5 != sK3
    | X6 != sK3
    | X7 != sK4 ),
    inference(resolution,[status(thm)],[c_4404,c_23])).

cnf(c_622,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_27223,plain,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))
    | X0 != sK3
    | X1 != sK3
    | X2 != sK3
    | X3 != sK3
    | X4 != sK3
    | X5 != sK3
    | X6 != sK4 ),
    inference(resolution,[status(thm)],[c_22137,c_622])).

cnf(c_22,negated_conjecture,
    ( sK1 != sK3 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_623,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1194,plain,
    ( sK3 != X0
    | sK1 != X0
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_18,plain,
    ( ~ r1_tarski(k1_tarski(X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
    | X1 = X0
    | X2 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1245,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k5_enumset1(X0,X0,X0,X0,X0,X0,sK1))
    | X0 = sK3
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1556,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK1))
    | sK3 = sK3
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_17,plain,
    ( r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1557,plain,
    ( r1_tarski(k1_tarski(sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1493,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_2287,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1493])).

cnf(c_1042,plain,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0
    | k1_tarski(X2) = X0
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1044,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = X2
    | k1_tarski(X1) = X2
    | k1_tarski(X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2911,plain,
    ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK3)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1042,c_1044])).

cnf(c_1043,plain,
    ( X0 = X1
    | X2 = X1
    | r1_tarski(k1_tarski(X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3263,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK3)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK3 = X0
    | sK4 = X0
    | r1_tarski(k1_tarski(X0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2911,c_1043])).

cnf(c_21,negated_conjecture,
    ( sK1 != sK4 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_30,plain,
    ( r1_tarski(k1_tarski(sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1192,plain,
    ( sK4 != X0
    | sK1 != X0
    | sK1 = sK4 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_1193,plain,
    ( sK4 != sK1
    | sK1 = sK4
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1192])).

cnf(c_1195,plain,
    ( sK3 != sK1
    | sK1 = sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1194])).

cnf(c_10,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1050,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1049,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3261,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK3)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK3 = X0
    | sK4 = X0
    | r2_hidden(X0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2911,c_1049])).

cnf(c_4601,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK3)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK3 = sK1
    | sK4 = sK1 ),
    inference(superposition,[status(thm)],[c_1050,c_3261])).

cnf(c_4781,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3263,c_22,c_21,c_27,c_30,c_1193,c_1195,c_4601])).

cnf(c_4782,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK3)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4781])).

cnf(c_20,plain,
    ( X0 = X1
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X0) != k1_tarski(X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_4794,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | k1_tarski(X0) != k1_tarski(sK3)
    | sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_4782,c_20])).

cnf(c_5511,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | k1_tarski(X0) != k1_tarski(sK3)
    | sK2 = sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4794,c_20])).

cnf(c_5513,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK2 = sK1 ),
    inference(equality_resolution,[status(thm)],[c_5511])).

cnf(c_1046,plain,
    ( r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1056,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2235,plain,
    ( k5_xboole_0(k1_tarski(X0),k3_xboole_0(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1046,c_1056])).

cnf(c_4788,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4782,c_2235])).

cnf(c_19,plain,
    ( X0 = X1
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X2) != k1_tarski(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4797,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | k1_tarski(X0) != k1_tarski(sK3)
    | sK1 = X0 ),
    inference(superposition,[status(thm)],[c_4782,c_19])).

cnf(c_5823,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK3 = sK1 ),
    inference(equality_resolution,[status(thm)],[c_4797])).

cnf(c_6172,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4788,c_22,c_27,c_30,c_1195,c_5823])).

cnf(c_6173,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6172])).

cnf(c_6189,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | k1_tarski(X0) != k1_tarski(sK4)
    | sK1 = X0 ),
    inference(superposition,[status(thm)],[c_6173,c_19])).

cnf(c_6581,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
    | sK4 = sK1 ),
    inference(equality_resolution,[status(thm)],[c_6189])).

cnf(c_6730,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5513,c_21,c_27,c_30,c_1193,c_6581])).

cnf(c_6752,plain,
    ( r1_tarski(k1_tarski(sK1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6730,c_1046])).

cnf(c_5,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1055,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2117,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1055])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1058,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2869,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2117,c_1058])).

cnf(c_9177,plain,
    ( k1_tarski(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6752,c_2869])).

cnf(c_11679,plain,
    ( sK1 = X0
    | sK1 = X1
    | r1_tarski(k1_xboole_0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9177,c_1043])).

cnf(c_15,plain,
    ( r1_tarski(k1_xboole_0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_11758,plain,
    ( ~ r1_tarski(k1_xboole_0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1))
    | sK1 = X0
    | sK1 = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11679])).

cnf(c_12741,plain,
    ( sK1 = X1
    | sK1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11679,c_15,c_11758])).

cnf(c_12742,plain,
    ( sK1 = X0
    | sK1 = X1 ),
    inference(renaming,[status(thm)],[c_12741])).

cnf(c_12900,plain,
    ( sK1 = X0
    | sK1 != sK1 ),
    inference(equality_factoring,[status(thm)],[c_12742])).

cnf(c_12903,plain,
    ( sK1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_12900])).

cnf(c_27254,plain,
    ( X0 != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_27223,c_22,c_1194,c_1556,c_1557,c_2287,c_12903])).

cnf(c_35172,plain,
    ( $false ),
    inference(resolution,[status(thm)],[c_27254,c_622])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:00:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.12/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.12/1.98  
% 11.12/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.12/1.98  
% 11.12/1.98  ------  iProver source info
% 11.12/1.98  
% 11.12/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.12/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.12/1.98  git: non_committed_changes: false
% 11.12/1.98  git: last_make_outside_of_git: false
% 11.12/1.98  
% 11.12/1.98  ------ 
% 11.12/1.98  ------ Parsing...
% 11.12/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.12/1.98  
% 11.12/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.12/1.98  
% 11.12/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.12/1.98  
% 11.12/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.12/1.98  ------ Proving...
% 11.12/1.98  ------ Problem Properties 
% 11.12/1.98  
% 11.12/1.98  
% 11.12/1.98  clauses                                 22
% 11.12/1.98  conjectures                             3
% 11.12/1.98  EPR                                     4
% 11.12/1.98  Horn                                    18
% 11.12/1.98  unary                                   11
% 11.12/1.98  binary                                  4
% 11.12/1.98  lits                                    43
% 11.12/1.98  lits eq                                 25
% 11.12/1.98  fd_pure                                 0
% 11.12/1.98  fd_pseudo                               0
% 11.12/1.98  fd_cond                                 0
% 11.12/1.98  fd_pseudo_cond                          8
% 11.12/1.98  AC symbols                              0
% 11.12/1.98  
% 11.12/1.98  ------ Input Options Time Limit: Unbounded
% 11.12/1.98  
% 11.12/1.98  
% 11.12/1.98  ------ 
% 11.12/1.98  Current options:
% 11.12/1.98  ------ 
% 11.12/1.98  
% 11.12/1.98  
% 11.12/1.98  
% 11.12/1.98  
% 11.12/1.98  ------ Proving...
% 11.12/1.98  
% 11.12/1.98  
% 11.12/1.98  % SZS status Theorem for theBenchmark.p
% 11.12/1.98  
% 11.12/1.98   Resolution empty clause
% 11.12/1.98  
% 11.12/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.12/1.98  
% 11.12/1.98  fof(f13,conjecture,(
% 11.12/1.98    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 11.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/1.98  
% 11.12/1.98  fof(f14,negated_conjecture,(
% 11.12/1.98    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 11.12/1.98    inference(negated_conjecture,[],[f13])).
% 11.12/1.98  
% 11.12/1.98  fof(f19,plain,(
% 11.12/1.98    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 11.12/1.98    inference(ennf_transformation,[],[f14])).
% 11.12/1.98  
% 11.12/1.98  fof(f30,plain,(
% 11.12/1.98    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 11.12/1.98    introduced(choice_axiom,[])).
% 11.12/1.98  
% 11.12/1.98  fof(f31,plain,(
% 11.12/1.98    sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 11.12/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f30])).
% 11.12/1.98  
% 11.12/1.98  fof(f56,plain,(
% 11.12/1.98    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 11.12/1.98    inference(cnf_transformation,[],[f31])).
% 11.12/1.98  
% 11.12/1.98  fof(f6,axiom,(
% 11.12/1.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/1.98  
% 11.12/1.98  fof(f45,plain,(
% 11.12/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.12/1.98    inference(cnf_transformation,[],[f6])).
% 11.12/1.98  
% 11.12/1.98  fof(f7,axiom,(
% 11.12/1.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)),
% 11.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/1.98  
% 11.12/1.98  fof(f46,plain,(
% 11.12/1.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 11.12/1.98    inference(cnf_transformation,[],[f7])).
% 11.12/1.98  
% 11.12/1.98  fof(f59,plain,(
% 11.12/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 11.12/1.98    inference(definition_unfolding,[],[f45,f46])).
% 11.12/1.98  
% 11.12/1.98  fof(f78,plain,(
% 11.12/1.98    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 11.12/1.98    inference(definition_unfolding,[],[f56,f59,f59])).
% 11.12/1.98  
% 11.12/1.98  fof(f57,plain,(
% 11.12/1.98    sK1 != sK3),
% 11.12/1.98    inference(cnf_transformation,[],[f31])).
% 11.12/1.98  
% 11.12/1.98  fof(f10,axiom,(
% 11.12/1.98    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 11.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/1.98  
% 11.12/1.98  fof(f16,plain,(
% 11.12/1.98    ! [X0,X1,X2] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 11.12/1.98    inference(ennf_transformation,[],[f10])).
% 11.12/1.98  
% 11.12/1.98  fof(f53,plain,(
% 11.12/1.98    ( ! [X2,X0,X1] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 11.12/1.98    inference(cnf_transformation,[],[f16])).
% 11.12/1.98  
% 11.12/1.98  fof(f75,plain,(
% 11.12/1.98    ( ! [X2,X0,X1] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) )),
% 11.12/1.98    inference(definition_unfolding,[],[f53,f59])).
% 11.12/1.98  
% 11.12/1.98  fof(f9,axiom,(
% 11.12/1.98    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 11.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/1.98  
% 11.12/1.98  fof(f52,plain,(
% 11.12/1.98    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 11.12/1.98    inference(cnf_transformation,[],[f9])).
% 11.12/1.98  
% 11.12/1.98  fof(f74,plain,(
% 11.12/1.98    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 11.12/1.98    inference(definition_unfolding,[],[f52,f59])).
% 11.12/1.98  
% 11.12/1.98  fof(f8,axiom,(
% 11.12/1.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 11.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/1.98  
% 11.12/1.98  fof(f15,plain,(
% 11.12/1.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 11.12/1.98    inference(ennf_transformation,[],[f8])).
% 11.12/1.98  
% 11.12/1.98  fof(f28,plain,(
% 11.12/1.98    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 11.12/1.98    inference(nnf_transformation,[],[f15])).
% 11.12/1.98  
% 11.12/1.98  fof(f29,plain,(
% 11.12/1.98    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 11.12/1.98    inference(flattening,[],[f28])).
% 11.12/1.98  
% 11.12/1.98  fof(f47,plain,(
% 11.12/1.98    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 11.12/1.98    inference(cnf_transformation,[],[f29])).
% 11.12/1.98  
% 11.12/1.98  fof(f73,plain,(
% 11.12/1.98    ( ! [X2,X0,X1] : (k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) )),
% 11.12/1.98    inference(definition_unfolding,[],[f47,f59,f59])).
% 11.12/1.98  
% 11.12/1.98  fof(f58,plain,(
% 11.12/1.98    sK1 != sK4),
% 11.12/1.98    inference(cnf_transformation,[],[f31])).
% 11.12/1.98  
% 11.12/1.98  fof(f5,axiom,(
% 11.12/1.98    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 11.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/1.98  
% 11.12/1.98  fof(f23,plain,(
% 11.12/1.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 11.12/1.98    inference(nnf_transformation,[],[f5])).
% 11.12/1.98  
% 11.12/1.98  fof(f24,plain,(
% 11.12/1.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 11.12/1.98    inference(flattening,[],[f23])).
% 11.12/1.98  
% 11.12/1.98  fof(f25,plain,(
% 11.12/1.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 11.12/1.98    inference(rectify,[],[f24])).
% 11.12/1.98  
% 11.12/1.98  fof(f26,plain,(
% 11.12/1.98    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.12/1.98    introduced(choice_axiom,[])).
% 11.12/1.98  
% 11.12/1.98  fof(f27,plain,(
% 11.12/1.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 11.12/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 11.12/1.98  
% 11.12/1.98  fof(f40,plain,(
% 11.12/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 11.12/1.98    inference(cnf_transformation,[],[f27])).
% 11.12/1.98  
% 11.12/1.98  fof(f67,plain,(
% 11.12/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 11.12/1.98    inference(definition_unfolding,[],[f40,f59])).
% 11.12/1.98  
% 11.12/1.98  fof(f83,plain,(
% 11.12/1.98    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k5_enumset1(X4,X4,X4,X4,X4,X4,X1) != X2) )),
% 11.12/1.98    inference(equality_resolution,[],[f67])).
% 11.12/1.98  
% 11.12/1.98  fof(f84,plain,(
% 11.12/1.98    ( ! [X4,X1] : (r2_hidden(X4,k5_enumset1(X4,X4,X4,X4,X4,X4,X1))) )),
% 11.12/1.98    inference(equality_resolution,[],[f83])).
% 11.12/1.98  
% 11.12/1.98  fof(f39,plain,(
% 11.12/1.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 11.12/1.98    inference(cnf_transformation,[],[f27])).
% 11.12/1.98  
% 11.12/1.98  fof(f68,plain,(
% 11.12/1.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 11.12/1.98    inference(definition_unfolding,[],[f39,f59])).
% 11.12/1.98  
% 11.12/1.98  fof(f85,plain,(
% 11.12/1.98    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 11.12/1.98    inference(equality_resolution,[],[f68])).
% 11.12/1.98  
% 11.12/1.98  fof(f12,axiom,(
% 11.12/1.98    ! [X0,X1,X2] : (k2_tarski(X1,X2) = k1_tarski(X0) => X1 = X2)),
% 11.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/1.98  
% 11.12/1.98  fof(f18,plain,(
% 11.12/1.98    ! [X0,X1,X2] : (X1 = X2 | k2_tarski(X1,X2) != k1_tarski(X0))),
% 11.12/1.98    inference(ennf_transformation,[],[f12])).
% 11.12/1.98  
% 11.12/1.98  fof(f55,plain,(
% 11.12/1.98    ( ! [X2,X0,X1] : (X1 = X2 | k2_tarski(X1,X2) != k1_tarski(X0)) )),
% 11.12/1.98    inference(cnf_transformation,[],[f18])).
% 11.12/1.98  
% 11.12/1.98  fof(f77,plain,(
% 11.12/1.98    ( ! [X2,X0,X1] : (X1 = X2 | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) != k1_tarski(X0)) )),
% 11.12/1.98    inference(definition_unfolding,[],[f55,f59])).
% 11.12/1.98  
% 11.12/1.98  fof(f2,axiom,(
% 11.12/1.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/1.98  
% 11.12/1.98  fof(f22,plain,(
% 11.12/1.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 11.12/1.98    inference(nnf_transformation,[],[f2])).
% 11.12/1.98  
% 11.12/1.98  fof(f36,plain,(
% 11.12/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.12/1.98    inference(cnf_transformation,[],[f22])).
% 11.12/1.98  
% 11.12/1.98  fof(f3,axiom,(
% 11.12/1.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/1.98  
% 11.12/1.98  fof(f37,plain,(
% 11.12/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.12/1.98    inference(cnf_transformation,[],[f3])).
% 11.12/1.98  
% 11.12/1.98  fof(f60,plain,(
% 11.12/1.98    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 11.12/1.98    inference(definition_unfolding,[],[f36,f37])).
% 11.12/1.98  
% 11.12/1.98  fof(f11,axiom,(
% 11.12/1.98    ! [X0,X1,X2] : (k2_tarski(X1,X2) = k1_tarski(X0) => X0 = X1)),
% 11.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/1.98  
% 11.12/1.98  fof(f17,plain,(
% 11.12/1.98    ! [X0,X1,X2] : (X0 = X1 | k2_tarski(X1,X2) != k1_tarski(X0))),
% 11.12/1.98    inference(ennf_transformation,[],[f11])).
% 11.12/1.98  
% 11.12/1.98  fof(f54,plain,(
% 11.12/1.98    ( ! [X2,X0,X1] : (X0 = X1 | k2_tarski(X1,X2) != k1_tarski(X0)) )),
% 11.12/1.98    inference(cnf_transformation,[],[f17])).
% 11.12/1.98  
% 11.12/1.98  fof(f76,plain,(
% 11.12/1.98    ( ! [X2,X0,X1] : (X0 = X1 | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) != k1_tarski(X0)) )),
% 11.12/1.98    inference(definition_unfolding,[],[f54,f59])).
% 11.12/1.98  
% 11.12/1.98  fof(f4,axiom,(
% 11.12/1.98    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 11.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/1.98  
% 11.12/1.98  fof(f38,plain,(
% 11.12/1.98    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 11.12/1.98    inference(cnf_transformation,[],[f4])).
% 11.12/1.98  
% 11.12/1.98  fof(f62,plain,(
% 11.12/1.98    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 11.12/1.98    inference(definition_unfolding,[],[f38,f37])).
% 11.12/1.98  
% 11.12/1.98  fof(f35,plain,(
% 11.12/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 11.12/1.98    inference(cnf_transformation,[],[f22])).
% 11.12/1.98  
% 11.12/1.98  fof(f61,plain,(
% 11.12/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.12/1.98    inference(definition_unfolding,[],[f35,f37])).
% 11.12/1.98  
% 11.12/1.98  fof(f1,axiom,(
% 11.12/1.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.12/1.98  
% 11.12/1.98  fof(f20,plain,(
% 11.12/1.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.12/1.98    inference(nnf_transformation,[],[f1])).
% 11.12/1.98  
% 11.12/1.98  fof(f21,plain,(
% 11.12/1.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.12/1.98    inference(flattening,[],[f20])).
% 11.12/1.98  
% 11.12/1.98  fof(f34,plain,(
% 11.12/1.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.12/1.98    inference(cnf_transformation,[],[f21])).
% 11.12/1.98  
% 11.12/1.98  fof(f48,plain,(
% 11.12/1.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 11.12/1.98    inference(cnf_transformation,[],[f29])).
% 11.12/1.98  
% 11.12/1.98  fof(f72,plain,(
% 11.12/1.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) | k1_xboole_0 != X0) )),
% 11.12/1.98    inference(definition_unfolding,[],[f48,f59])).
% 11.12/1.98  
% 11.12/1.98  fof(f89,plain,(
% 11.12/1.98    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) )),
% 11.12/1.98    inference(equality_resolution,[],[f72])).
% 11.12/1.98  
% 11.12/1.98  cnf(c_627,plain,
% 11.12/1.98      ( X0 != X1
% 11.12/1.98      | X2 != X3
% 11.12/1.98      | X4 != X5
% 11.12/1.98      | X6 != X7
% 11.12/1.98      | X8 != X9
% 11.12/1.98      | X10 != X11
% 11.12/1.98      | X12 != X13
% 11.12/1.98      | k5_enumset1(X0,X2,X4,X6,X8,X10,X12) = k5_enumset1(X1,X3,X5,X7,X9,X11,X13) ),
% 11.12/1.98      theory(equality) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_624,plain,
% 11.12/1.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.12/1.98      theory(equality) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_4404,plain,
% 11.12/1.98      ( ~ r1_tarski(X0,k5_enumset1(X1,X2,X3,X4,X5,X6,X7))
% 11.12/1.98      | r1_tarski(X8,k5_enumset1(X9,X10,X11,X12,X13,X14,X15))
% 11.12/1.98      | X8 != X0
% 11.12/1.98      | X9 != X1
% 11.12/1.98      | X10 != X2
% 11.12/1.98      | X11 != X3
% 11.12/1.98      | X12 != X4
% 11.12/1.98      | X13 != X5
% 11.12/1.98      | X14 != X6
% 11.12/1.98      | X15 != X7 ),
% 11.12/1.98      inference(resolution,[status(thm)],[c_627,c_624]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_23,negated_conjecture,
% 11.12/1.98      ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 11.12/1.98      inference(cnf_transformation,[],[f78]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_22137,plain,
% 11.12/1.98      ( r1_tarski(X0,k5_enumset1(X1,X2,X3,X4,X5,X6,X7))
% 11.12/1.98      | X0 != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 11.12/1.98      | X1 != sK3
% 11.12/1.98      | X2 != sK3
% 11.12/1.98      | X3 != sK3
% 11.12/1.98      | X4 != sK3
% 11.12/1.98      | X5 != sK3
% 11.12/1.98      | X6 != sK3
% 11.12/1.98      | X7 != sK4 ),
% 11.12/1.98      inference(resolution,[status(thm)],[c_4404,c_23]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_622,plain,( X0 = X0 ),theory(equality) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_27223,plain,
% 11.12/1.98      ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))
% 11.12/1.98      | X0 != sK3
% 11.12/1.98      | X1 != sK3
% 11.12/1.98      | X2 != sK3
% 11.12/1.98      | X3 != sK3
% 11.12/1.98      | X4 != sK3
% 11.12/1.98      | X5 != sK3
% 11.12/1.98      | X6 != sK4 ),
% 11.12/1.98      inference(resolution,[status(thm)],[c_22137,c_622]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_22,negated_conjecture,
% 11.12/1.98      ( sK1 != sK3 ),
% 11.12/1.98      inference(cnf_transformation,[],[f57]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_623,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_1194,plain,
% 11.12/1.98      ( sK3 != X0 | sK1 != X0 | sK1 = sK3 ),
% 11.12/1.98      inference(instantiation,[status(thm)],[c_623]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_18,plain,
% 11.12/1.98      ( ~ r1_tarski(k1_tarski(X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
% 11.12/1.98      | X1 = X0
% 11.12/1.98      | X2 = X0 ),
% 11.12/1.98      inference(cnf_transformation,[],[f75]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_1245,plain,
% 11.12/1.98      ( ~ r1_tarski(k1_tarski(sK3),k5_enumset1(X0,X0,X0,X0,X0,X0,sK1))
% 11.12/1.98      | X0 = sK3
% 11.12/1.98      | sK1 = sK3 ),
% 11.12/1.98      inference(instantiation,[status(thm)],[c_18]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_1556,plain,
% 11.12/1.98      ( ~ r1_tarski(k1_tarski(sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK1))
% 11.12/1.98      | sK3 = sK3
% 11.12/1.98      | sK1 = sK3 ),
% 11.12/1.98      inference(instantiation,[status(thm)],[c_1245]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_17,plain,
% 11.12/1.98      ( r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 11.12/1.98      inference(cnf_transformation,[],[f74]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_1557,plain,
% 11.12/1.98      ( r1_tarski(k1_tarski(sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK1)) ),
% 11.12/1.98      inference(instantiation,[status(thm)],[c_17]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_1493,plain,
% 11.12/1.98      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 11.12/1.98      inference(instantiation,[status(thm)],[c_623]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_2287,plain,
% 11.12/1.98      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 11.12/1.98      inference(instantiation,[status(thm)],[c_1493]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_1042,plain,
% 11.12/1.98      ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = iProver_top ),
% 11.12/1.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_16,plain,
% 11.12/1.98      ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
% 11.12/1.98      | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0
% 11.12/1.98      | k1_tarski(X2) = X0
% 11.12/1.98      | k1_tarski(X1) = X0
% 11.12/1.98      | k1_xboole_0 = X0 ),
% 11.12/1.98      inference(cnf_transformation,[],[f73]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_1044,plain,
% 11.12/1.98      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = X2
% 11.12/1.98      | k1_tarski(X1) = X2
% 11.12/1.98      | k1_tarski(X0) = X2
% 11.12/1.98      | k1_xboole_0 = X2
% 11.12/1.98      | r1_tarski(X2,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
% 11.12/1.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_2911,plain,
% 11.12/1.98      ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK3)
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 11.12/1.98      inference(superposition,[status(thm)],[c_1042,c_1044]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_1043,plain,
% 11.12/1.98      ( X0 = X1
% 11.12/1.98      | X2 = X1
% 11.12/1.98      | r1_tarski(k1_tarski(X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) != iProver_top ),
% 11.12/1.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_3263,plain,
% 11.12/1.98      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK3)
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 11.12/1.98      | sK3 = X0
% 11.12/1.98      | sK4 = X0
% 11.12/1.98      | r1_tarski(k1_tarski(X0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 11.12/1.98      inference(superposition,[status(thm)],[c_2911,c_1043]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_21,negated_conjecture,
% 11.12/1.98      ( sK1 != sK4 ),
% 11.12/1.98      inference(cnf_transformation,[],[f58]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_27,plain,
% 11.12/1.98      ( ~ r1_tarski(k1_tarski(sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 11.12/1.98      | sK1 = sK1 ),
% 11.12/1.98      inference(instantiation,[status(thm)],[c_18]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_30,plain,
% 11.12/1.98      ( r1_tarski(k1_tarski(sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 11.12/1.98      inference(instantiation,[status(thm)],[c_17]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_1192,plain,
% 11.12/1.98      ( sK4 != X0 | sK1 != X0 | sK1 = sK4 ),
% 11.12/1.98      inference(instantiation,[status(thm)],[c_623]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_1193,plain,
% 11.12/1.98      ( sK4 != sK1 | sK1 = sK4 | sK1 != sK1 ),
% 11.12/1.98      inference(instantiation,[status(thm)],[c_1192]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_1195,plain,
% 11.12/1.98      ( sK3 != sK1 | sK1 = sK3 | sK1 != sK1 ),
% 11.12/1.98      inference(instantiation,[status(thm)],[c_1194]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_10,plain,
% 11.12/1.98      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 11.12/1.98      inference(cnf_transformation,[],[f84]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_1050,plain,
% 11.12/1.98      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 11.12/1.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_11,plain,
% 11.12/1.98      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 11.12/1.98      inference(cnf_transformation,[],[f85]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_1049,plain,
% 11.12/1.98      ( X0 = X1
% 11.12/1.98      | X0 = X2
% 11.12/1.98      | r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
% 11.12/1.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_3261,plain,
% 11.12/1.98      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK3)
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 11.12/1.98      | sK3 = X0
% 11.12/1.98      | sK4 = X0
% 11.12/1.98      | r2_hidden(X0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != iProver_top ),
% 11.12/1.98      inference(superposition,[status(thm)],[c_2911,c_1049]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_4601,plain,
% 11.12/1.98      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK3)
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 11.12/1.98      | sK3 = sK1
% 11.12/1.98      | sK4 = sK1 ),
% 11.12/1.98      inference(superposition,[status(thm)],[c_1050,c_3261]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_4781,plain,
% 11.12/1.98      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK3) ),
% 11.12/1.98      inference(global_propositional_subsumption,
% 11.12/1.98                [status(thm)],
% 11.12/1.98                [c_3263,c_22,c_21,c_27,c_30,c_1193,c_1195,c_4601]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_4782,plain,
% 11.12/1.98      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK3)
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 11.12/1.98      inference(renaming,[status(thm)],[c_4781]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_20,plain,
% 11.12/1.98      ( X0 = X1 | k5_enumset1(X1,X1,X1,X1,X1,X1,X0) != k1_tarski(X2) ),
% 11.12/1.98      inference(cnf_transformation,[],[f77]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_4794,plain,
% 11.12/1.98      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 11.12/1.98      | k1_tarski(X0) != k1_tarski(sK3)
% 11.12/1.98      | sK2 = sK1 ),
% 11.12/1.98      inference(superposition,[status(thm)],[c_4782,c_20]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_5511,plain,
% 11.12/1.98      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 11.12/1.98      | k1_tarski(X0) != k1_tarski(sK3)
% 11.12/1.98      | sK2 = sK1 ),
% 11.12/1.98      inference(forward_subsumption_resolution,[status(thm)],[c_4794,c_20]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_5513,plain,
% 11.12/1.98      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 | sK2 = sK1 ),
% 11.12/1.98      inference(equality_resolution,[status(thm)],[c_5511]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_1046,plain,
% 11.12/1.98      ( r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 11.12/1.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_3,plain,
% 11.12/1.98      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.12/1.98      inference(cnf_transformation,[],[f60]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_1056,plain,
% 11.12/1.98      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 11.12/1.98      | r1_tarski(X0,X1) != iProver_top ),
% 11.12/1.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_2235,plain,
% 11.12/1.98      ( k5_xboole_0(k1_tarski(X0),k3_xboole_0(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
% 11.12/1.98      inference(superposition,[status(thm)],[c_1046,c_1056]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_4788,plain,
% 11.12/1.98      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 11.12/1.98      | k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK3))) = k1_xboole_0 ),
% 11.12/1.98      inference(superposition,[status(thm)],[c_4782,c_2235]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_19,plain,
% 11.12/1.98      ( X0 = X1 | k5_enumset1(X0,X0,X0,X0,X0,X0,X2) != k1_tarski(X1) ),
% 11.12/1.98      inference(cnf_transformation,[],[f76]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_4797,plain,
% 11.12/1.98      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 11.12/1.98      | k1_tarski(X0) != k1_tarski(sK3)
% 11.12/1.98      | sK1 = X0 ),
% 11.12/1.98      inference(superposition,[status(thm)],[c_4782,c_19]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_5823,plain,
% 11.12/1.98      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 11.12/1.98      | sK3 = sK1 ),
% 11.12/1.98      inference(equality_resolution,[status(thm)],[c_4797]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_6172,plain,
% 11.12/1.98      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4) ),
% 11.12/1.98      inference(global_propositional_subsumption,
% 11.12/1.98                [status(thm)],
% 11.12/1.98                [c_4788,c_22,c_27,c_30,c_1195,c_5823]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_6173,plain,
% 11.12/1.98      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_tarski(sK4)
% 11.12/1.98      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 11.12/1.98      inference(renaming,[status(thm)],[c_6172]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_6189,plain,
% 11.12/1.98      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0
% 11.12/1.98      | k1_tarski(X0) != k1_tarski(sK4)
% 11.12/1.98      | sK1 = X0 ),
% 11.12/1.98      inference(superposition,[status(thm)],[c_6173,c_19]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_6581,plain,
% 11.12/1.98      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 | sK4 = sK1 ),
% 11.12/1.98      inference(equality_resolution,[status(thm)],[c_6189]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_6730,plain,
% 11.12/1.98      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k1_xboole_0 ),
% 11.12/1.98      inference(global_propositional_subsumption,
% 11.12/1.98                [status(thm)],
% 11.12/1.98                [c_5513,c_21,c_27,c_30,c_1193,c_6581]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_6752,plain,
% 11.12/1.98      ( r1_tarski(k1_tarski(sK1),k1_xboole_0) = iProver_top ),
% 11.12/1.98      inference(superposition,[status(thm)],[c_6730,c_1046]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_5,plain,
% 11.12/1.98      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 11.12/1.98      inference(cnf_transformation,[],[f62]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_4,plain,
% 11.12/1.98      ( r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 11.12/1.98      inference(cnf_transformation,[],[f61]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_1055,plain,
% 11.12/1.98      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 11.12/1.98      | r1_tarski(X0,X1) = iProver_top ),
% 11.12/1.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_2117,plain,
% 11.12/1.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.12/1.98      inference(superposition,[status(thm)],[c_5,c_1055]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_0,plain,
% 11.12/1.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.12/1.98      inference(cnf_transformation,[],[f34]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_1058,plain,
% 11.12/1.98      ( X0 = X1
% 11.12/1.98      | r1_tarski(X0,X1) != iProver_top
% 11.12/1.98      | r1_tarski(X1,X0) != iProver_top ),
% 11.12/1.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_2869,plain,
% 11.12/1.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.12/1.98      inference(superposition,[status(thm)],[c_2117,c_1058]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_9177,plain,
% 11.12/1.98      ( k1_tarski(sK1) = k1_xboole_0 ),
% 11.12/1.98      inference(superposition,[status(thm)],[c_6752,c_2869]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_11679,plain,
% 11.12/1.98      ( sK1 = X0
% 11.12/1.98      | sK1 = X1
% 11.12/1.98      | r1_tarski(k1_xboole_0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
% 11.12/1.98      inference(superposition,[status(thm)],[c_9177,c_1043]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_15,plain,
% 11.12/1.98      ( r1_tarski(k1_xboole_0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 11.12/1.98      inference(cnf_transformation,[],[f89]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_11758,plain,
% 11.12/1.98      ( ~ r1_tarski(k1_xboole_0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1))
% 11.12/1.98      | sK1 = X0
% 11.12/1.98      | sK1 = X1 ),
% 11.12/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_11679]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_12741,plain,
% 11.12/1.98      ( sK1 = X1 | sK1 = X0 ),
% 11.12/1.98      inference(global_propositional_subsumption,
% 11.12/1.98                [status(thm)],
% 11.12/1.98                [c_11679,c_15,c_11758]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_12742,plain,
% 11.12/1.98      ( sK1 = X0 | sK1 = X1 ),
% 11.12/1.98      inference(renaming,[status(thm)],[c_12741]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_12900,plain,
% 11.12/1.98      ( sK1 = X0 | sK1 != sK1 ),
% 11.12/1.98      inference(equality_factoring,[status(thm)],[c_12742]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_12903,plain,
% 11.12/1.98      ( sK1 = X0 ),
% 11.12/1.98      inference(equality_resolution_simp,[status(thm)],[c_12900]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_27254,plain,
% 11.12/1.98      ( X0 != sK3 ),
% 11.12/1.98      inference(global_propositional_subsumption,
% 11.12/1.98                [status(thm)],
% 11.12/1.98                [c_27223,c_22,c_1194,c_1556,c_1557,c_2287,c_12903]) ).
% 11.12/1.98  
% 11.12/1.98  cnf(c_35172,plain,
% 11.12/1.98      ( $false ),
% 11.12/1.98      inference(resolution,[status(thm)],[c_27254,c_622]) ).
% 11.12/1.98  
% 11.12/1.98  
% 11.12/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.12/1.98  
% 11.12/1.98  ------                               Statistics
% 11.12/1.98  
% 11.12/1.98  ------ Selected
% 11.12/1.98  
% 11.12/1.98  total_time:                             1.387
% 11.12/1.98  
%------------------------------------------------------------------------------
