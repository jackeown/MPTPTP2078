%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:18 EST 2020

% Result     : Theorem 7.95s
% Output     : CNFRefutation 7.95s
% Verified   : 
% Statistics : Number of formulae       :  143 (2474 expanded)
%              Number of clauses        :   79 ( 581 expanded)
%              Number of leaves         :   19 ( 665 expanded)
%              Depth                    :   30
%              Number of atoms          :  378 (6293 expanded)
%              Number of equality atoms :  271 (4712 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f47,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK3 != sK6
      & sK3 != sK5
      & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( sK3 != sK6
    & sK3 != sK5
    & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f35,f47])).

fof(f82,plain,(
    r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f48])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f105,plain,(
    r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) ),
    inference(definition_unfolding,[],[f82,f86,f86])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X1,X1,X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f77,f86,f86])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f58,f55,f55])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    sK3 != sK5 ),
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,(
    sK3 != sK6 ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f62,f86])).

fof(f110,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f98])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f64,f86])).

fof(f106,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f96])).

fof(f107,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f106])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f63,f86])).

fof(f108,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f97])).

fof(f109,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f108])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f90,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f69,f86])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f51,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f36])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_680,plain,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k1_tarski(X2) = X0
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_681,plain,
    ( k2_enumset1(X0,X0,X0,X1) = X2
    | k1_tarski(X1) = X2
    | k1_tarski(X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1290,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK5)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_680,c_681])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_692,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4571,plain,
    ( k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) = k2_enumset1(sK3,sK3,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_680,c_692])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1295,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_5462,plain,
    ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)))) = k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_4571,c_1295])).

cnf(c_6060,plain,
    ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)))) = k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) ),
    inference(superposition,[status(thm)],[c_5462,c_0])).

cnf(c_6175,plain,
    ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)))) = k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) ),
    inference(superposition,[status(thm)],[c_4,c_6060])).

cnf(c_6194,plain,
    ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) = k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) ),
    inference(light_normalisation,[status(thm)],[c_6175,c_4571])).

cnf(c_6202,plain,
    ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))) = k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) ),
    inference(superposition,[status(thm)],[c_4,c_6194])).

cnf(c_6214,plain,
    ( k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_6202,c_4571])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_693,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6347,plain,
    ( r1_tarski(X0,k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top
    | r1_tarski(X0,k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6214,c_693])).

cnf(c_6619,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK5)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | r1_tarski(X0,k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top
    | r1_tarski(X0,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_6347])).

cnf(c_27,negated_conjecture,
    ( sK3 != sK5 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_26,negated_conjecture,
    ( sK3 != sK6 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_721,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK5,sK5,sK5,X0))
    | sK3 = X0
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_763,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK5,sK5,sK5,sK3))
    | sK3 = sK5
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_792,plain,
    ( r2_hidden(sK3,k2_enumset1(sK5,sK5,sK5,sK3)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_396,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_848,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_1079,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_848])).

cnf(c_3159,plain,
    ( sK6 != sK3
    | sK3 = sK6
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_3160,plain,
    ( sK5 != sK3
    | sK3 = sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_687,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_686,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5282,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK5)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = X0
    | sK6 = X0
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_686])).

cnf(c_6068,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK5)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = sK3
    | sK6 = sK3 ),
    inference(superposition,[status(thm)],[c_687,c_5282])).

cnf(c_6647,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK5)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6619,c_27,c_26,c_763,c_792,c_3159,c_3160,c_6068])).

cnf(c_688,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6658,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | r2_hidden(sK4,k1_tarski(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6647,c_688])).

cnf(c_6654,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | r2_hidden(sK3,k1_tarski(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6647,c_687])).

cnf(c_1,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5277,plain,
    ( X0 = X1
    | r2_hidden(X1,k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_686])).

cnf(c_8156,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = sK3 ),
    inference(superposition,[status(thm)],[c_6654,c_5277])).

cnf(c_8819,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6658,c_27,c_763,c_792,c_3160,c_8156])).

cnf(c_8820,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8819])).

cnf(c_8858,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k1_tarski(sK6))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_8820,c_6214])).

cnf(c_1298,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_0])).

cnf(c_9463,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k1_tarski(sK6))))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)))) ),
    inference(superposition,[status(thm)],[c_8858,c_1298])).

cnf(c_6319,plain,
    ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) = k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_6214,c_5462])).

cnf(c_9478,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k1_tarski(sK6))))) = k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_9463,c_6214,c_6319])).

cnf(c_6415,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1298,c_0])).

cnf(c_8615,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_6415,c_0])).

cnf(c_10238,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k1_tarski(sK6)))))))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))))) ),
    inference(superposition,[status(thm)],[c_9478,c_8615])).

cnf(c_6221,plain,
    ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_6214,c_6194])).

cnf(c_6413,plain,
    ( k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)))) ),
    inference(superposition,[status(thm)],[c_6214,c_1298])).

cnf(c_6417,plain,
    ( k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) = k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_6413,c_6214,c_6319])).

cnf(c_10281,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k1_tarski(sK6)))))))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_10238,c_6221,c_6417])).

cnf(c_10282,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k1_tarski(sK6))))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_10281,c_0])).

cnf(c_714,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK6,sK6,sK6,X0))
    | sK3 = X0
    | sK3 = sK6 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_728,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK6,sK6,sK6,sK6))
    | sK3 = sK6 ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_6484,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) = k1_tarski(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_8826,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | r2_hidden(sK3,k1_tarski(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8820,c_687])).

cnf(c_8870,plain,
    ( r2_hidden(sK3,k1_tarski(sK6))
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8826])).

cnf(c_400,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_741,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK3,k2_enumset1(sK6,sK6,sK6,sK6))
    | k2_enumset1(sK6,sK6,sK6,sK6) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_843,plain,
    ( ~ r2_hidden(sK3,X0)
    | r2_hidden(sK3,k2_enumset1(sK6,sK6,sK6,sK6))
    | k2_enumset1(sK6,sK6,sK6,sK6) != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_741])).

cnf(c_14108,plain,
    ( r2_hidden(sK3,k2_enumset1(sK6,sK6,sK6,sK6))
    | ~ r2_hidden(sK3,k1_tarski(sK6))
    | k2_enumset1(sK6,sK6,sK6,sK6) != k1_tarski(sK6)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_14382,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10282,c_27,c_26,c_728,c_763,c_792,c_6484,c_8870,c_14108])).

cnf(c_14430,plain,
    ( r2_hidden(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14382,c_687])).

cnf(c_5,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_244,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_245,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_678,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_1110,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_678])).

cnf(c_18433,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_14430,c_1110])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:50:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.95/1.44  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.95/1.44  
% 7.95/1.44  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.95/1.44  
% 7.95/1.44  ------  iProver source info
% 7.95/1.44  
% 7.95/1.44  git: date: 2020-06-30 10:37:57 +0100
% 7.95/1.44  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.95/1.44  git: non_committed_changes: false
% 7.95/1.44  git: last_make_outside_of_git: false
% 7.95/1.44  
% 7.95/1.44  ------ 
% 7.95/1.44  
% 7.95/1.44  ------ Input Options
% 7.95/1.44  
% 7.95/1.44  --out_options                           all
% 7.95/1.44  --tptp_safe_out                         true
% 7.95/1.44  --problem_path                          ""
% 7.95/1.44  --include_path                          ""
% 7.95/1.44  --clausifier                            res/vclausify_rel
% 7.95/1.44  --clausifier_options                    ""
% 7.95/1.44  --stdin                                 false
% 7.95/1.44  --stats_out                             all
% 7.95/1.44  
% 7.95/1.44  ------ General Options
% 7.95/1.44  
% 7.95/1.44  --fof                                   false
% 7.95/1.44  --time_out_real                         305.
% 7.95/1.44  --time_out_virtual                      -1.
% 7.95/1.44  --symbol_type_check                     false
% 7.95/1.44  --clausify_out                          false
% 7.95/1.44  --sig_cnt_out                           false
% 7.95/1.44  --trig_cnt_out                          false
% 7.95/1.44  --trig_cnt_out_tolerance                1.
% 7.95/1.44  --trig_cnt_out_sk_spl                   false
% 7.95/1.44  --abstr_cl_out                          false
% 7.95/1.44  
% 7.95/1.44  ------ Global Options
% 7.95/1.44  
% 7.95/1.44  --schedule                              default
% 7.95/1.44  --add_important_lit                     false
% 7.95/1.44  --prop_solver_per_cl                    1000
% 7.95/1.44  --min_unsat_core                        false
% 7.95/1.44  --soft_assumptions                      false
% 7.95/1.44  --soft_lemma_size                       3
% 7.95/1.44  --prop_impl_unit_size                   0
% 7.95/1.44  --prop_impl_unit                        []
% 7.95/1.44  --share_sel_clauses                     true
% 7.95/1.44  --reset_solvers                         false
% 7.95/1.44  --bc_imp_inh                            [conj_cone]
% 7.95/1.44  --conj_cone_tolerance                   3.
% 7.95/1.44  --extra_neg_conj                        none
% 7.95/1.44  --large_theory_mode                     true
% 7.95/1.44  --prolific_symb_bound                   200
% 7.95/1.44  --lt_threshold                          2000
% 7.95/1.44  --clause_weak_htbl                      true
% 7.95/1.44  --gc_record_bc_elim                     false
% 7.95/1.44  
% 7.95/1.44  ------ Preprocessing Options
% 7.95/1.44  
% 7.95/1.44  --preprocessing_flag                    true
% 7.95/1.44  --time_out_prep_mult                    0.1
% 7.95/1.44  --splitting_mode                        input
% 7.95/1.44  --splitting_grd                         true
% 7.95/1.44  --splitting_cvd                         false
% 7.95/1.44  --splitting_cvd_svl                     false
% 7.95/1.44  --splitting_nvd                         32
% 7.95/1.44  --sub_typing                            true
% 7.95/1.44  --prep_gs_sim                           true
% 7.95/1.44  --prep_unflatten                        true
% 7.95/1.44  --prep_res_sim                          true
% 7.95/1.44  --prep_upred                            true
% 7.95/1.44  --prep_sem_filter                       exhaustive
% 7.95/1.44  --prep_sem_filter_out                   false
% 7.95/1.44  --pred_elim                             true
% 7.95/1.44  --res_sim_input                         true
% 7.95/1.44  --eq_ax_congr_red                       true
% 7.95/1.44  --pure_diseq_elim                       true
% 7.95/1.44  --brand_transform                       false
% 7.95/1.44  --non_eq_to_eq                          false
% 7.95/1.44  --prep_def_merge                        true
% 7.95/1.44  --prep_def_merge_prop_impl              false
% 7.95/1.44  --prep_def_merge_mbd                    true
% 7.95/1.44  --prep_def_merge_tr_red                 false
% 7.95/1.44  --prep_def_merge_tr_cl                  false
% 7.95/1.44  --smt_preprocessing                     true
% 7.95/1.44  --smt_ac_axioms                         fast
% 7.95/1.44  --preprocessed_out                      false
% 7.95/1.44  --preprocessed_stats                    false
% 7.95/1.44  
% 7.95/1.44  ------ Abstraction refinement Options
% 7.95/1.44  
% 7.95/1.44  --abstr_ref                             []
% 7.95/1.44  --abstr_ref_prep                        false
% 7.95/1.44  --abstr_ref_until_sat                   false
% 7.95/1.44  --abstr_ref_sig_restrict                funpre
% 7.95/1.44  --abstr_ref_af_restrict_to_split_sk     false
% 7.95/1.44  --abstr_ref_under                       []
% 7.95/1.44  
% 7.95/1.44  ------ SAT Options
% 7.95/1.44  
% 7.95/1.44  --sat_mode                              false
% 7.95/1.44  --sat_fm_restart_options                ""
% 7.95/1.44  --sat_gr_def                            false
% 7.95/1.44  --sat_epr_types                         true
% 7.95/1.44  --sat_non_cyclic_types                  false
% 7.95/1.44  --sat_finite_models                     false
% 7.95/1.44  --sat_fm_lemmas                         false
% 7.95/1.44  --sat_fm_prep                           false
% 7.95/1.44  --sat_fm_uc_incr                        true
% 7.95/1.44  --sat_out_model                         small
% 7.95/1.44  --sat_out_clauses                       false
% 7.95/1.44  
% 7.95/1.44  ------ QBF Options
% 7.95/1.44  
% 7.95/1.44  --qbf_mode                              false
% 7.95/1.44  --qbf_elim_univ                         false
% 7.95/1.44  --qbf_dom_inst                          none
% 7.95/1.44  --qbf_dom_pre_inst                      false
% 7.95/1.44  --qbf_sk_in                             false
% 7.95/1.44  --qbf_pred_elim                         true
% 7.95/1.44  --qbf_split                             512
% 7.95/1.44  
% 7.95/1.44  ------ BMC1 Options
% 7.95/1.44  
% 7.95/1.44  --bmc1_incremental                      false
% 7.95/1.44  --bmc1_axioms                           reachable_all
% 7.95/1.44  --bmc1_min_bound                        0
% 7.95/1.44  --bmc1_max_bound                        -1
% 7.95/1.44  --bmc1_max_bound_default                -1
% 7.95/1.44  --bmc1_symbol_reachability              true
% 7.95/1.44  --bmc1_property_lemmas                  false
% 7.95/1.44  --bmc1_k_induction                      false
% 7.95/1.44  --bmc1_non_equiv_states                 false
% 7.95/1.44  --bmc1_deadlock                         false
% 7.95/1.44  --bmc1_ucm                              false
% 7.95/1.44  --bmc1_add_unsat_core                   none
% 7.95/1.44  --bmc1_unsat_core_children              false
% 7.95/1.44  --bmc1_unsat_core_extrapolate_axioms    false
% 7.95/1.44  --bmc1_out_stat                         full
% 7.95/1.44  --bmc1_ground_init                      false
% 7.95/1.44  --bmc1_pre_inst_next_state              false
% 7.95/1.44  --bmc1_pre_inst_state                   false
% 7.95/1.44  --bmc1_pre_inst_reach_state             false
% 7.95/1.44  --bmc1_out_unsat_core                   false
% 7.95/1.44  --bmc1_aig_witness_out                  false
% 7.95/1.44  --bmc1_verbose                          false
% 7.95/1.44  --bmc1_dump_clauses_tptp                false
% 7.95/1.44  --bmc1_dump_unsat_core_tptp             false
% 7.95/1.44  --bmc1_dump_file                        -
% 7.95/1.44  --bmc1_ucm_expand_uc_limit              128
% 7.95/1.44  --bmc1_ucm_n_expand_iterations          6
% 7.95/1.44  --bmc1_ucm_extend_mode                  1
% 7.95/1.44  --bmc1_ucm_init_mode                    2
% 7.95/1.44  --bmc1_ucm_cone_mode                    none
% 7.95/1.44  --bmc1_ucm_reduced_relation_type        0
% 7.95/1.44  --bmc1_ucm_relax_model                  4
% 7.95/1.44  --bmc1_ucm_full_tr_after_sat            true
% 7.95/1.44  --bmc1_ucm_expand_neg_assumptions       false
% 7.95/1.44  --bmc1_ucm_layered_model                none
% 7.95/1.44  --bmc1_ucm_max_lemma_size               10
% 7.95/1.44  
% 7.95/1.44  ------ AIG Options
% 7.95/1.44  
% 7.95/1.44  --aig_mode                              false
% 7.95/1.44  
% 7.95/1.44  ------ Instantiation Options
% 7.95/1.44  
% 7.95/1.44  --instantiation_flag                    true
% 7.95/1.44  --inst_sos_flag                         true
% 7.95/1.44  --inst_sos_phase                        true
% 7.95/1.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.95/1.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.95/1.44  --inst_lit_sel_side                     num_symb
% 7.95/1.44  --inst_solver_per_active                1400
% 7.95/1.44  --inst_solver_calls_frac                1.
% 7.95/1.44  --inst_passive_queue_type               priority_queues
% 7.95/1.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.95/1.44  --inst_passive_queues_freq              [25;2]
% 7.95/1.44  --inst_dismatching                      true
% 7.95/1.44  --inst_eager_unprocessed_to_passive     true
% 7.95/1.44  --inst_prop_sim_given                   true
% 7.95/1.44  --inst_prop_sim_new                     false
% 7.95/1.44  --inst_subs_new                         false
% 7.95/1.44  --inst_eq_res_simp                      false
% 7.95/1.44  --inst_subs_given                       false
% 7.95/1.44  --inst_orphan_elimination               true
% 7.95/1.44  --inst_learning_loop_flag               true
% 7.95/1.44  --inst_learning_start                   3000
% 7.95/1.44  --inst_learning_factor                  2
% 7.95/1.44  --inst_start_prop_sim_after_learn       3
% 7.95/1.44  --inst_sel_renew                        solver
% 7.95/1.44  --inst_lit_activity_flag                true
% 7.95/1.44  --inst_restr_to_given                   false
% 7.95/1.44  --inst_activity_threshold               500
% 7.95/1.44  --inst_out_proof                        true
% 7.95/1.44  
% 7.95/1.44  ------ Resolution Options
% 7.95/1.44  
% 7.95/1.44  --resolution_flag                       true
% 7.95/1.44  --res_lit_sel                           adaptive
% 7.95/1.44  --res_lit_sel_side                      none
% 7.95/1.44  --res_ordering                          kbo
% 7.95/1.44  --res_to_prop_solver                    active
% 7.95/1.44  --res_prop_simpl_new                    false
% 7.95/1.44  --res_prop_simpl_given                  true
% 7.95/1.44  --res_passive_queue_type                priority_queues
% 7.95/1.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.95/1.44  --res_passive_queues_freq               [15;5]
% 7.95/1.44  --res_forward_subs                      full
% 7.95/1.44  --res_backward_subs                     full
% 7.95/1.44  --res_forward_subs_resolution           true
% 7.95/1.44  --res_backward_subs_resolution          true
% 7.95/1.44  --res_orphan_elimination                true
% 7.95/1.44  --res_time_limit                        2.
% 7.95/1.44  --res_out_proof                         true
% 7.95/1.44  
% 7.95/1.44  ------ Superposition Options
% 7.95/1.44  
% 7.95/1.44  --superposition_flag                    true
% 7.95/1.44  --sup_passive_queue_type                priority_queues
% 7.95/1.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.95/1.44  --sup_passive_queues_freq               [8;1;4]
% 7.95/1.44  --demod_completeness_check              fast
% 7.95/1.44  --demod_use_ground                      true
% 7.95/1.44  --sup_to_prop_solver                    passive
% 7.95/1.44  --sup_prop_simpl_new                    true
% 7.95/1.44  --sup_prop_simpl_given                  true
% 7.95/1.44  --sup_fun_splitting                     true
% 7.95/1.44  --sup_smt_interval                      50000
% 7.95/1.44  
% 7.95/1.44  ------ Superposition Simplification Setup
% 7.95/1.44  
% 7.95/1.44  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.95/1.44  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.95/1.44  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.95/1.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.95/1.44  --sup_full_triv                         [TrivRules;PropSubs]
% 7.95/1.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.95/1.44  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.95/1.44  --sup_immed_triv                        [TrivRules]
% 7.95/1.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.44  --sup_immed_bw_main                     []
% 7.95/1.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.95/1.44  --sup_input_triv                        [Unflattening;TrivRules]
% 7.95/1.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.44  --sup_input_bw                          []
% 7.95/1.44  
% 7.95/1.44  ------ Combination Options
% 7.95/1.44  
% 7.95/1.44  --comb_res_mult                         3
% 7.95/1.44  --comb_sup_mult                         2
% 7.95/1.44  --comb_inst_mult                        10
% 7.95/1.44  
% 7.95/1.44  ------ Debug Options
% 7.95/1.44  
% 7.95/1.44  --dbg_backtrace                         false
% 7.95/1.44  --dbg_dump_prop_clauses                 false
% 7.95/1.44  --dbg_dump_prop_clauses_file            -
% 7.95/1.44  --dbg_out_stat                          false
% 7.95/1.44  ------ Parsing...
% 7.95/1.44  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.95/1.44  
% 7.95/1.44  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.95/1.44  
% 7.95/1.44  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.95/1.44  
% 7.95/1.44  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.95/1.44  ------ Proving...
% 7.95/1.44  ------ Problem Properties 
% 7.95/1.44  
% 7.95/1.44  
% 7.95/1.44  clauses                                 28
% 7.95/1.44  conjectures                             3
% 7.95/1.44  EPR                                     2
% 7.95/1.44  Horn                                    24
% 7.95/1.44  unary                                   18
% 7.95/1.44  binary                                  5
% 7.95/1.44  lits                                    46
% 7.95/1.44  lits eq                                 25
% 7.95/1.44  fd_pure                                 0
% 7.95/1.44  fd_pseudo                               0
% 7.95/1.44  fd_cond                                 1
% 7.95/1.44  fd_pseudo_cond                          4
% 7.95/1.44  AC symbols                              0
% 7.95/1.44  
% 7.95/1.44  ------ Schedule dynamic 5 is on 
% 7.95/1.44  
% 7.95/1.44  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.95/1.44  
% 7.95/1.44  
% 7.95/1.44  ------ 
% 7.95/1.44  Current options:
% 7.95/1.44  ------ 
% 7.95/1.44  
% 7.95/1.44  ------ Input Options
% 7.95/1.44  
% 7.95/1.44  --out_options                           all
% 7.95/1.44  --tptp_safe_out                         true
% 7.95/1.44  --problem_path                          ""
% 7.95/1.44  --include_path                          ""
% 7.95/1.44  --clausifier                            res/vclausify_rel
% 7.95/1.44  --clausifier_options                    ""
% 7.95/1.44  --stdin                                 false
% 7.95/1.44  --stats_out                             all
% 7.95/1.44  
% 7.95/1.44  ------ General Options
% 7.95/1.44  
% 7.95/1.44  --fof                                   false
% 7.95/1.44  --time_out_real                         305.
% 7.95/1.44  --time_out_virtual                      -1.
% 7.95/1.44  --symbol_type_check                     false
% 7.95/1.44  --clausify_out                          false
% 7.95/1.44  --sig_cnt_out                           false
% 7.95/1.44  --trig_cnt_out                          false
% 7.95/1.44  --trig_cnt_out_tolerance                1.
% 7.95/1.44  --trig_cnt_out_sk_spl                   false
% 7.95/1.44  --abstr_cl_out                          false
% 7.95/1.44  
% 7.95/1.44  ------ Global Options
% 7.95/1.44  
% 7.95/1.44  --schedule                              default
% 7.95/1.44  --add_important_lit                     false
% 7.95/1.44  --prop_solver_per_cl                    1000
% 7.95/1.44  --min_unsat_core                        false
% 7.95/1.44  --soft_assumptions                      false
% 7.95/1.44  --soft_lemma_size                       3
% 7.95/1.44  --prop_impl_unit_size                   0
% 7.95/1.44  --prop_impl_unit                        []
% 7.95/1.44  --share_sel_clauses                     true
% 7.95/1.44  --reset_solvers                         false
% 7.95/1.44  --bc_imp_inh                            [conj_cone]
% 7.95/1.44  --conj_cone_tolerance                   3.
% 7.95/1.44  --extra_neg_conj                        none
% 7.95/1.44  --large_theory_mode                     true
% 7.95/1.44  --prolific_symb_bound                   200
% 7.95/1.44  --lt_threshold                          2000
% 7.95/1.44  --clause_weak_htbl                      true
% 7.95/1.44  --gc_record_bc_elim                     false
% 7.95/1.44  
% 7.95/1.44  ------ Preprocessing Options
% 7.95/1.44  
% 7.95/1.44  --preprocessing_flag                    true
% 7.95/1.44  --time_out_prep_mult                    0.1
% 7.95/1.44  --splitting_mode                        input
% 7.95/1.44  --splitting_grd                         true
% 7.95/1.44  --splitting_cvd                         false
% 7.95/1.44  --splitting_cvd_svl                     false
% 7.95/1.44  --splitting_nvd                         32
% 7.95/1.44  --sub_typing                            true
% 7.95/1.44  --prep_gs_sim                           true
% 7.95/1.44  --prep_unflatten                        true
% 7.95/1.44  --prep_res_sim                          true
% 7.95/1.44  --prep_upred                            true
% 7.95/1.44  --prep_sem_filter                       exhaustive
% 7.95/1.44  --prep_sem_filter_out                   false
% 7.95/1.44  --pred_elim                             true
% 7.95/1.44  --res_sim_input                         true
% 7.95/1.44  --eq_ax_congr_red                       true
% 7.95/1.44  --pure_diseq_elim                       true
% 7.95/1.44  --brand_transform                       false
% 7.95/1.44  --non_eq_to_eq                          false
% 7.95/1.44  --prep_def_merge                        true
% 7.95/1.44  --prep_def_merge_prop_impl              false
% 7.95/1.44  --prep_def_merge_mbd                    true
% 7.95/1.44  --prep_def_merge_tr_red                 false
% 7.95/1.44  --prep_def_merge_tr_cl                  false
% 7.95/1.44  --smt_preprocessing                     true
% 7.95/1.44  --smt_ac_axioms                         fast
% 7.95/1.44  --preprocessed_out                      false
% 7.95/1.44  --preprocessed_stats                    false
% 7.95/1.44  
% 7.95/1.44  ------ Abstraction refinement Options
% 7.95/1.44  
% 7.95/1.44  --abstr_ref                             []
% 7.95/1.44  --abstr_ref_prep                        false
% 7.95/1.44  --abstr_ref_until_sat                   false
% 7.95/1.44  --abstr_ref_sig_restrict                funpre
% 7.95/1.44  --abstr_ref_af_restrict_to_split_sk     false
% 7.95/1.44  --abstr_ref_under                       []
% 7.95/1.44  
% 7.95/1.44  ------ SAT Options
% 7.95/1.44  
% 7.95/1.44  --sat_mode                              false
% 7.95/1.44  --sat_fm_restart_options                ""
% 7.95/1.44  --sat_gr_def                            false
% 7.95/1.44  --sat_epr_types                         true
% 7.95/1.44  --sat_non_cyclic_types                  false
% 7.95/1.44  --sat_finite_models                     false
% 7.95/1.44  --sat_fm_lemmas                         false
% 7.95/1.44  --sat_fm_prep                           false
% 7.95/1.44  --sat_fm_uc_incr                        true
% 7.95/1.44  --sat_out_model                         small
% 7.95/1.44  --sat_out_clauses                       false
% 7.95/1.44  
% 7.95/1.44  ------ QBF Options
% 7.95/1.44  
% 7.95/1.44  --qbf_mode                              false
% 7.95/1.44  --qbf_elim_univ                         false
% 7.95/1.44  --qbf_dom_inst                          none
% 7.95/1.44  --qbf_dom_pre_inst                      false
% 7.95/1.44  --qbf_sk_in                             false
% 7.95/1.44  --qbf_pred_elim                         true
% 7.95/1.44  --qbf_split                             512
% 7.95/1.44  
% 7.95/1.44  ------ BMC1 Options
% 7.95/1.44  
% 7.95/1.44  --bmc1_incremental                      false
% 7.95/1.44  --bmc1_axioms                           reachable_all
% 7.95/1.44  --bmc1_min_bound                        0
% 7.95/1.44  --bmc1_max_bound                        -1
% 7.95/1.44  --bmc1_max_bound_default                -1
% 7.95/1.44  --bmc1_symbol_reachability              true
% 7.95/1.44  --bmc1_property_lemmas                  false
% 7.95/1.44  --bmc1_k_induction                      false
% 7.95/1.44  --bmc1_non_equiv_states                 false
% 7.95/1.44  --bmc1_deadlock                         false
% 7.95/1.44  --bmc1_ucm                              false
% 7.95/1.44  --bmc1_add_unsat_core                   none
% 7.95/1.44  --bmc1_unsat_core_children              false
% 7.95/1.44  --bmc1_unsat_core_extrapolate_axioms    false
% 7.95/1.44  --bmc1_out_stat                         full
% 7.95/1.44  --bmc1_ground_init                      false
% 7.95/1.44  --bmc1_pre_inst_next_state              false
% 7.95/1.44  --bmc1_pre_inst_state                   false
% 7.95/1.44  --bmc1_pre_inst_reach_state             false
% 7.95/1.44  --bmc1_out_unsat_core                   false
% 7.95/1.44  --bmc1_aig_witness_out                  false
% 7.95/1.44  --bmc1_verbose                          false
% 7.95/1.44  --bmc1_dump_clauses_tptp                false
% 7.95/1.44  --bmc1_dump_unsat_core_tptp             false
% 7.95/1.44  --bmc1_dump_file                        -
% 7.95/1.44  --bmc1_ucm_expand_uc_limit              128
% 7.95/1.44  --bmc1_ucm_n_expand_iterations          6
% 7.95/1.44  --bmc1_ucm_extend_mode                  1
% 7.95/1.44  --bmc1_ucm_init_mode                    2
% 7.95/1.44  --bmc1_ucm_cone_mode                    none
% 7.95/1.44  --bmc1_ucm_reduced_relation_type        0
% 7.95/1.44  --bmc1_ucm_relax_model                  4
% 7.95/1.44  --bmc1_ucm_full_tr_after_sat            true
% 7.95/1.44  --bmc1_ucm_expand_neg_assumptions       false
% 7.95/1.44  --bmc1_ucm_layered_model                none
% 7.95/1.44  --bmc1_ucm_max_lemma_size               10
% 7.95/1.44  
% 7.95/1.44  ------ AIG Options
% 7.95/1.44  
% 7.95/1.44  --aig_mode                              false
% 7.95/1.44  
% 7.95/1.44  ------ Instantiation Options
% 7.95/1.44  
% 7.95/1.44  --instantiation_flag                    true
% 7.95/1.44  --inst_sos_flag                         true
% 7.95/1.44  --inst_sos_phase                        true
% 7.95/1.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.95/1.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.95/1.44  --inst_lit_sel_side                     none
% 7.95/1.44  --inst_solver_per_active                1400
% 7.95/1.44  --inst_solver_calls_frac                1.
% 7.95/1.44  --inst_passive_queue_type               priority_queues
% 7.95/1.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.95/1.44  --inst_passive_queues_freq              [25;2]
% 7.95/1.44  --inst_dismatching                      true
% 7.95/1.44  --inst_eager_unprocessed_to_passive     true
% 7.95/1.44  --inst_prop_sim_given                   true
% 7.95/1.44  --inst_prop_sim_new                     false
% 7.95/1.44  --inst_subs_new                         false
% 7.95/1.44  --inst_eq_res_simp                      false
% 7.95/1.44  --inst_subs_given                       false
% 7.95/1.44  --inst_orphan_elimination               true
% 7.95/1.44  --inst_learning_loop_flag               true
% 7.95/1.44  --inst_learning_start                   3000
% 7.95/1.44  --inst_learning_factor                  2
% 7.95/1.44  --inst_start_prop_sim_after_learn       3
% 7.95/1.44  --inst_sel_renew                        solver
% 7.95/1.44  --inst_lit_activity_flag                true
% 7.95/1.44  --inst_restr_to_given                   false
% 7.95/1.44  --inst_activity_threshold               500
% 7.95/1.44  --inst_out_proof                        true
% 7.95/1.44  
% 7.95/1.44  ------ Resolution Options
% 7.95/1.44  
% 7.95/1.44  --resolution_flag                       false
% 7.95/1.44  --res_lit_sel                           adaptive
% 7.95/1.44  --res_lit_sel_side                      none
% 7.95/1.44  --res_ordering                          kbo
% 7.95/1.44  --res_to_prop_solver                    active
% 7.95/1.44  --res_prop_simpl_new                    false
% 7.95/1.44  --res_prop_simpl_given                  true
% 7.95/1.44  --res_passive_queue_type                priority_queues
% 7.95/1.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.95/1.44  --res_passive_queues_freq               [15;5]
% 7.95/1.44  --res_forward_subs                      full
% 7.95/1.44  --res_backward_subs                     full
% 7.95/1.44  --res_forward_subs_resolution           true
% 7.95/1.44  --res_backward_subs_resolution          true
% 7.95/1.44  --res_orphan_elimination                true
% 7.95/1.44  --res_time_limit                        2.
% 7.95/1.44  --res_out_proof                         true
% 7.95/1.44  
% 7.95/1.44  ------ Superposition Options
% 7.95/1.44  
% 7.95/1.44  --superposition_flag                    true
% 7.95/1.44  --sup_passive_queue_type                priority_queues
% 7.95/1.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.95/1.44  --sup_passive_queues_freq               [8;1;4]
% 7.95/1.44  --demod_completeness_check              fast
% 7.95/1.44  --demod_use_ground                      true
% 7.95/1.44  --sup_to_prop_solver                    passive
% 7.95/1.44  --sup_prop_simpl_new                    true
% 7.95/1.44  --sup_prop_simpl_given                  true
% 7.95/1.44  --sup_fun_splitting                     true
% 7.95/1.44  --sup_smt_interval                      50000
% 7.95/1.44  
% 7.95/1.44  ------ Superposition Simplification Setup
% 7.95/1.44  
% 7.95/1.44  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.95/1.44  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.95/1.44  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.95/1.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.95/1.44  --sup_full_triv                         [TrivRules;PropSubs]
% 7.95/1.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.95/1.44  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.95/1.44  --sup_immed_triv                        [TrivRules]
% 7.95/1.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.44  --sup_immed_bw_main                     []
% 7.95/1.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.95/1.44  --sup_input_triv                        [Unflattening;TrivRules]
% 7.95/1.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.44  --sup_input_bw                          []
% 7.95/1.44  
% 7.95/1.44  ------ Combination Options
% 7.95/1.44  
% 7.95/1.44  --comb_res_mult                         3
% 7.95/1.44  --comb_sup_mult                         2
% 7.95/1.44  --comb_inst_mult                        10
% 7.95/1.44  
% 7.95/1.44  ------ Debug Options
% 7.95/1.44  
% 7.95/1.44  --dbg_backtrace                         false
% 7.95/1.44  --dbg_dump_prop_clauses                 false
% 7.95/1.44  --dbg_dump_prop_clauses_file            -
% 7.95/1.44  --dbg_out_stat                          false
% 7.95/1.44  
% 7.95/1.44  
% 7.95/1.44  
% 7.95/1.44  
% 7.95/1.44  ------ Proving...
% 7.95/1.44  
% 7.95/1.44  
% 7.95/1.44  % SZS status Theorem for theBenchmark.p
% 7.95/1.44  
% 7.95/1.44   Resolution empty clause
% 7.95/1.44  
% 7.95/1.44  % SZS output start CNFRefutation for theBenchmark.p
% 7.95/1.44  
% 7.95/1.44  fof(f25,conjecture,(
% 7.95/1.44    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.95/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.44  
% 7.95/1.44  fof(f26,negated_conjecture,(
% 7.95/1.44    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.95/1.44    inference(negated_conjecture,[],[f25])).
% 7.95/1.44  
% 7.95/1.44  fof(f35,plain,(
% 7.95/1.44    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.95/1.44    inference(ennf_transformation,[],[f26])).
% 7.95/1.44  
% 7.95/1.44  fof(f47,plain,(
% 7.95/1.44    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK3 != sK6 & sK3 != sK5 & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))),
% 7.95/1.44    introduced(choice_axiom,[])).
% 7.95/1.44  
% 7.95/1.44  fof(f48,plain,(
% 7.95/1.44    sK3 != sK6 & sK3 != sK5 & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))),
% 7.95/1.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f35,f47])).
% 7.95/1.44  
% 7.95/1.44  fof(f82,plain,(
% 7.95/1.44    r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))),
% 7.95/1.44    inference(cnf_transformation,[],[f48])).
% 7.95/1.44  
% 7.95/1.44  fof(f17,axiom,(
% 7.95/1.44    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.95/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.44  
% 7.95/1.44  fof(f70,plain,(
% 7.95/1.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.95/1.44    inference(cnf_transformation,[],[f17])).
% 7.95/1.44  
% 7.95/1.44  fof(f18,axiom,(
% 7.95/1.44    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.95/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.44  
% 7.95/1.44  fof(f71,plain,(
% 7.95/1.44    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.95/1.44    inference(cnf_transformation,[],[f18])).
% 7.95/1.44  
% 7.95/1.44  fof(f86,plain,(
% 7.95/1.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.95/1.44    inference(definition_unfolding,[],[f70,f71])).
% 7.95/1.44  
% 7.95/1.44  fof(f105,plain,(
% 7.95/1.44    r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))),
% 7.95/1.44    inference(definition_unfolding,[],[f82,f86,f86])).
% 7.95/1.44  
% 7.95/1.44  fof(f24,axiom,(
% 7.95/1.44    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 7.95/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.44  
% 7.95/1.44  fof(f34,plain,(
% 7.95/1.44    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.95/1.44    inference(ennf_transformation,[],[f24])).
% 7.95/1.44  
% 7.95/1.44  fof(f45,plain,(
% 7.95/1.44    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.95/1.44    inference(nnf_transformation,[],[f34])).
% 7.95/1.44  
% 7.95/1.44  fof(f46,plain,(
% 7.95/1.44    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.95/1.44    inference(flattening,[],[f45])).
% 7.95/1.44  
% 7.95/1.44  fof(f77,plain,(
% 7.95/1.44    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 7.95/1.44    inference(cnf_transformation,[],[f46])).
% 7.95/1.44  
% 7.95/1.44  fof(f104,plain,(
% 7.95/1.44    ( ! [X2,X0,X1] : (k2_enumset1(X1,X1,X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 7.95/1.44    inference(definition_unfolding,[],[f77,f86,f86])).
% 7.95/1.44  
% 7.95/1.44  fof(f2,axiom,(
% 7.95/1.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.95/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.44  
% 7.95/1.44  fof(f50,plain,(
% 7.95/1.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.95/1.44    inference(cnf_transformation,[],[f2])).
% 7.95/1.44  
% 7.95/1.44  fof(f9,axiom,(
% 7.95/1.44    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.95/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.44  
% 7.95/1.44  fof(f32,plain,(
% 7.95/1.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.95/1.44    inference(ennf_transformation,[],[f9])).
% 7.95/1.44  
% 7.95/1.44  fof(f57,plain,(
% 7.95/1.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.95/1.44    inference(cnf_transformation,[],[f32])).
% 7.95/1.44  
% 7.95/1.44  fof(f10,axiom,(
% 7.95/1.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.95/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.44  
% 7.95/1.44  fof(f58,plain,(
% 7.95/1.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.95/1.44    inference(cnf_transformation,[],[f10])).
% 7.95/1.44  
% 7.95/1.44  fof(f7,axiom,(
% 7.95/1.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.95/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.44  
% 7.95/1.44  fof(f55,plain,(
% 7.95/1.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.95/1.44    inference(cnf_transformation,[],[f7])).
% 7.95/1.44  
% 7.95/1.44  fof(f89,plain,(
% 7.95/1.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 7.95/1.44    inference(definition_unfolding,[],[f58,f55,f55])).
% 7.95/1.44  
% 7.95/1.44  fof(f8,axiom,(
% 7.95/1.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 7.95/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.44  
% 7.95/1.44  fof(f31,plain,(
% 7.95/1.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 7.95/1.44    inference(ennf_transformation,[],[f8])).
% 7.95/1.44  
% 7.95/1.44  fof(f56,plain,(
% 7.95/1.44    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 7.95/1.44    inference(cnf_transformation,[],[f31])).
% 7.95/1.44  
% 7.95/1.44  fof(f83,plain,(
% 7.95/1.44    sK3 != sK5),
% 7.95/1.44    inference(cnf_transformation,[],[f48])).
% 7.95/1.44  
% 7.95/1.44  fof(f84,plain,(
% 7.95/1.44    sK3 != sK6),
% 7.95/1.44    inference(cnf_transformation,[],[f48])).
% 7.95/1.44  
% 7.95/1.44  fof(f14,axiom,(
% 7.95/1.44    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.95/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.44  
% 7.95/1.44  fof(f40,plain,(
% 7.95/1.44    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.95/1.44    inference(nnf_transformation,[],[f14])).
% 7.95/1.44  
% 7.95/1.44  fof(f41,plain,(
% 7.95/1.44    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.95/1.44    inference(flattening,[],[f40])).
% 7.95/1.44  
% 7.95/1.44  fof(f42,plain,(
% 7.95/1.44    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.95/1.44    inference(rectify,[],[f41])).
% 7.95/1.44  
% 7.95/1.44  fof(f43,plain,(
% 7.95/1.44    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.95/1.44    introduced(choice_axiom,[])).
% 7.95/1.44  
% 7.95/1.44  fof(f44,plain,(
% 7.95/1.44    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.95/1.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 7.95/1.44  
% 7.95/1.44  fof(f62,plain,(
% 7.95/1.44    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.95/1.44    inference(cnf_transformation,[],[f44])).
% 7.95/1.44  
% 7.95/1.44  fof(f98,plain,(
% 7.95/1.44    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.95/1.44    inference(definition_unfolding,[],[f62,f86])).
% 7.95/1.44  
% 7.95/1.44  fof(f110,plain,(
% 7.95/1.44    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 7.95/1.44    inference(equality_resolution,[],[f98])).
% 7.95/1.44  
% 7.95/1.44  fof(f64,plain,(
% 7.95/1.44    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.95/1.44    inference(cnf_transformation,[],[f44])).
% 7.95/1.44  
% 7.95/1.44  fof(f96,plain,(
% 7.95/1.44    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.95/1.44    inference(definition_unfolding,[],[f64,f86])).
% 7.95/1.44  
% 7.95/1.44  fof(f106,plain,(
% 7.95/1.44    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 7.95/1.44    inference(equality_resolution,[],[f96])).
% 7.95/1.44  
% 7.95/1.44  fof(f107,plain,(
% 7.95/1.44    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 7.95/1.44    inference(equality_resolution,[],[f106])).
% 7.95/1.44  
% 7.95/1.44  fof(f63,plain,(
% 7.95/1.44    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.95/1.44    inference(cnf_transformation,[],[f44])).
% 7.95/1.44  
% 7.95/1.44  fof(f97,plain,(
% 7.95/1.44    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.95/1.44    inference(definition_unfolding,[],[f63,f86])).
% 7.95/1.44  
% 7.95/1.44  fof(f108,plain,(
% 7.95/1.44    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 7.95/1.44    inference(equality_resolution,[],[f97])).
% 7.95/1.44  
% 7.95/1.44  fof(f109,plain,(
% 7.95/1.44    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 7.95/1.44    inference(equality_resolution,[],[f108])).
% 7.95/1.44  
% 7.95/1.44  fof(f16,axiom,(
% 7.95/1.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.95/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.44  
% 7.95/1.44  fof(f69,plain,(
% 7.95/1.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.95/1.44    inference(cnf_transformation,[],[f16])).
% 7.95/1.44  
% 7.95/1.44  fof(f90,plain,(
% 7.95/1.44    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 7.95/1.44    inference(definition_unfolding,[],[f69,f86])).
% 7.95/1.44  
% 7.95/1.44  fof(f4,axiom,(
% 7.95/1.44    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.95/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.44  
% 7.95/1.44  fof(f27,plain,(
% 7.95/1.44    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.95/1.44    inference(rectify,[],[f4])).
% 7.95/1.44  
% 7.95/1.44  fof(f51,plain,(
% 7.95/1.44    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.95/1.44    inference(cnf_transformation,[],[f27])).
% 7.95/1.44  
% 7.95/1.44  fof(f5,axiom,(
% 7.95/1.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.95/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.44  
% 7.95/1.44  fof(f28,plain,(
% 7.95/1.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.95/1.44    inference(rectify,[],[f5])).
% 7.95/1.44  
% 7.95/1.44  fof(f29,plain,(
% 7.95/1.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.95/1.44    inference(ennf_transformation,[],[f28])).
% 7.95/1.44  
% 7.95/1.44  fof(f36,plain,(
% 7.95/1.44    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 7.95/1.44    introduced(choice_axiom,[])).
% 7.95/1.44  
% 7.95/1.44  fof(f37,plain,(
% 7.95/1.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.95/1.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f36])).
% 7.95/1.44  
% 7.95/1.44  fof(f53,plain,(
% 7.95/1.44    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.95/1.44    inference(cnf_transformation,[],[f37])).
% 7.95/1.44  
% 7.95/1.44  fof(f12,axiom,(
% 7.95/1.44    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.95/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.44  
% 7.95/1.44  fof(f60,plain,(
% 7.95/1.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.95/1.44    inference(cnf_transformation,[],[f12])).
% 7.95/1.44  
% 7.95/1.44  cnf(c_28,negated_conjecture,
% 7.95/1.44      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) ),
% 7.95/1.44      inference(cnf_transformation,[],[f105]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_680,plain,
% 7.95/1.44      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top ),
% 7.95/1.44      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_25,plain,
% 7.95/1.44      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
% 7.95/1.44      | k2_enumset1(X1,X1,X1,X2) = X0
% 7.95/1.44      | k1_tarski(X2) = X0
% 7.95/1.44      | k1_tarski(X1) = X0
% 7.95/1.44      | k1_xboole_0 = X0 ),
% 7.95/1.44      inference(cnf_transformation,[],[f104]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_681,plain,
% 7.95/1.44      ( k2_enumset1(X0,X0,X0,X1) = X2
% 7.95/1.44      | k1_tarski(X1) = X2
% 7.95/1.44      | k1_tarski(X0) = X2
% 7.95/1.44      | k1_xboole_0 = X2
% 7.95/1.44      | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 7.95/1.44      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_1290,plain,
% 7.95/1.44      ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.95/1.44      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK5)
% 7.95/1.44      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
% 7.95/1.44      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_680,c_681]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_4,plain,
% 7.95/1.44      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.95/1.44      inference(cnf_transformation,[],[f50]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_10,plain,
% 7.95/1.44      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.95/1.44      inference(cnf_transformation,[],[f57]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_692,plain,
% 7.95/1.44      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.95/1.44      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_4571,plain,
% 7.95/1.44      ( k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) = k2_enumset1(sK3,sK3,sK3,sK4) ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_680,c_692]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_0,plain,
% 7.95/1.44      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 7.95/1.44      inference(cnf_transformation,[],[f89]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_1295,plain,
% 7.95/1.44      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_5462,plain,
% 7.95/1.44      ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)))) = k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_4571,c_1295]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6060,plain,
% 7.95/1.44      ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)))) = k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_5462,c_0]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6175,plain,
% 7.95/1.44      ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)))) = k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_4,c_6060]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6194,plain,
% 7.95/1.44      ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) = k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) ),
% 7.95/1.44      inference(light_normalisation,[status(thm)],[c_6175,c_4571]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6202,plain,
% 7.95/1.44      ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))) = k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_4,c_6194]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6214,plain,
% 7.95/1.44      ( k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 7.95/1.44      inference(light_normalisation,[status(thm)],[c_6202,c_4571]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_9,plain,
% 7.95/1.44      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 7.95/1.44      inference(cnf_transformation,[],[f56]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_693,plain,
% 7.95/1.44      ( r1_tarski(X0,X1) = iProver_top
% 7.95/1.44      | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 7.95/1.44      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6347,plain,
% 7.95/1.44      ( r1_tarski(X0,k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top
% 7.95/1.44      | r1_tarski(X0,k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) != iProver_top ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_6214,c_693]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6619,plain,
% 7.95/1.44      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK5)
% 7.95/1.44      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
% 7.95/1.44      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.95/1.44      | r1_tarski(X0,k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top
% 7.95/1.44      | r1_tarski(X0,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK4))) != iProver_top ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_1290,c_6347]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_27,negated_conjecture,
% 7.95/1.44      ( sK3 != sK5 ),
% 7.95/1.44      inference(cnf_transformation,[],[f83]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_26,negated_conjecture,
% 7.95/1.44      ( sK3 != sK6 ),
% 7.95/1.44      inference(cnf_transformation,[],[f84]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_18,plain,
% 7.95/1.44      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 7.95/1.44      inference(cnf_transformation,[],[f110]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_721,plain,
% 7.95/1.44      ( ~ r2_hidden(sK3,k2_enumset1(sK5,sK5,sK5,X0)) | sK3 = X0 | sK3 = sK5 ),
% 7.95/1.44      inference(instantiation,[status(thm)],[c_18]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_763,plain,
% 7.95/1.44      ( ~ r2_hidden(sK3,k2_enumset1(sK5,sK5,sK5,sK3)) | sK3 = sK5 | sK3 = sK3 ),
% 7.95/1.44      inference(instantiation,[status(thm)],[c_721]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_16,plain,
% 7.95/1.44      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 7.95/1.44      inference(cnf_transformation,[],[f107]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_792,plain,
% 7.95/1.44      ( r2_hidden(sK3,k2_enumset1(sK5,sK5,sK5,sK3)) ),
% 7.95/1.44      inference(instantiation,[status(thm)],[c_16]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_396,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_848,plain,
% 7.95/1.44      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 7.95/1.44      inference(instantiation,[status(thm)],[c_396]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_1079,plain,
% 7.95/1.44      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 7.95/1.44      inference(instantiation,[status(thm)],[c_848]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_3159,plain,
% 7.95/1.44      ( sK6 != sK3 | sK3 = sK6 | sK3 != sK3 ),
% 7.95/1.44      inference(instantiation,[status(thm)],[c_1079]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_3160,plain,
% 7.95/1.44      ( sK5 != sK3 | sK3 = sK5 | sK3 != sK3 ),
% 7.95/1.44      inference(instantiation,[status(thm)],[c_1079]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_17,plain,
% 7.95/1.44      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 7.95/1.44      inference(cnf_transformation,[],[f109]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_687,plain,
% 7.95/1.44      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 7.95/1.44      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_686,plain,
% 7.95/1.44      ( X0 = X1
% 7.95/1.44      | X0 = X2
% 7.95/1.44      | r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top ),
% 7.95/1.44      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_5282,plain,
% 7.95/1.44      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK5)
% 7.95/1.44      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
% 7.95/1.44      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.95/1.44      | sK5 = X0
% 7.95/1.44      | sK6 = X0
% 7.95/1.44      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_1290,c_686]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6068,plain,
% 7.95/1.44      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK5)
% 7.95/1.44      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
% 7.95/1.44      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.95/1.44      | sK5 = sK3
% 7.95/1.44      | sK6 = sK3 ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_687,c_5282]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6647,plain,
% 7.95/1.44      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK5)
% 7.95/1.44      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
% 7.95/1.44      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.95/1.44      inference(global_propositional_subsumption,
% 7.95/1.44                [status(thm)],
% 7.95/1.44                [c_6619,c_27,c_26,c_763,c_792,c_3159,c_3160,c_6068]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_688,plain,
% 7.95/1.44      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 7.95/1.44      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6658,plain,
% 7.95/1.44      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
% 7.95/1.44      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.95/1.44      | r2_hidden(sK4,k1_tarski(sK5)) = iProver_top ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_6647,c_688]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6654,plain,
% 7.95/1.44      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
% 7.95/1.44      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.95/1.44      | r2_hidden(sK3,k1_tarski(sK5)) = iProver_top ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_6647,c_687]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_1,plain,
% 7.95/1.44      ( k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
% 7.95/1.44      inference(cnf_transformation,[],[f90]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_5277,plain,
% 7.95/1.44      ( X0 = X1 | r2_hidden(X1,k1_tarski(X0)) != iProver_top ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_1,c_686]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_8156,plain,
% 7.95/1.44      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
% 7.95/1.44      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.95/1.44      | sK5 = sK3 ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_6654,c_5277]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_8819,plain,
% 7.95/1.44      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.95/1.44      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6) ),
% 7.95/1.44      inference(global_propositional_subsumption,
% 7.95/1.44                [status(thm)],
% 7.95/1.44                [c_6658,c_27,c_763,c_792,c_3160,c_8156]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_8820,plain,
% 7.95/1.44      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_tarski(sK6)
% 7.95/1.44      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.95/1.44      inference(renaming,[status(thm)],[c_8819]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_8858,plain,
% 7.95/1.44      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.95/1.44      | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k1_tarski(sK6))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_8820,c_6214]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_1298,plain,
% 7.95/1.44      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_0,c_0]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_9463,plain,
% 7.95/1.44      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.95/1.44      | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k1_tarski(sK6))))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)))) ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_8858,c_1298]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6319,plain,
% 7.95/1.44      ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) = k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 7.95/1.44      inference(demodulation,[status(thm)],[c_6214,c_5462]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_9478,plain,
% 7.95/1.44      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.95/1.44      | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k1_tarski(sK6))))) = k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 7.95/1.44      inference(light_normalisation,[status(thm)],[c_9463,c_6214,c_6319]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6415,plain,
% 7.95/1.44      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_1298,c_0]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_8615,plain,
% 7.95/1.44      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_6415,c_0]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_10238,plain,
% 7.95/1.44      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.95/1.44      | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k1_tarski(sK6)))))))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))))) ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_9478,c_8615]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6221,plain,
% 7.95/1.44      ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 7.95/1.44      inference(demodulation,[status(thm)],[c_6214,c_6194]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6413,plain,
% 7.95/1.44      ( k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)))) ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_6214,c_1298]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6417,plain,
% 7.95/1.44      ( k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4))) = k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 7.95/1.44      inference(light_normalisation,[status(thm)],[c_6413,c_6214,c_6319]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_10281,plain,
% 7.95/1.44      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.95/1.44      | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k1_tarski(sK6)))))))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 7.95/1.44      inference(light_normalisation,[status(thm)],[c_10238,c_6221,c_6417]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_10282,plain,
% 7.95/1.44      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.95/1.44      | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k1_tarski(sK6))))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK6),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 7.95/1.44      inference(demodulation,[status(thm)],[c_10281,c_0]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_714,plain,
% 7.95/1.44      ( ~ r2_hidden(sK3,k2_enumset1(sK6,sK6,sK6,X0)) | sK3 = X0 | sK3 = sK6 ),
% 7.95/1.44      inference(instantiation,[status(thm)],[c_18]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_728,plain,
% 7.95/1.44      ( ~ r2_hidden(sK3,k2_enumset1(sK6,sK6,sK6,sK6)) | sK3 = sK6 ),
% 7.95/1.44      inference(instantiation,[status(thm)],[c_714]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6484,plain,
% 7.95/1.44      ( k2_enumset1(sK6,sK6,sK6,sK6) = k1_tarski(sK6) ),
% 7.95/1.44      inference(instantiation,[status(thm)],[c_1]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_8826,plain,
% 7.95/1.44      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.95/1.44      | r2_hidden(sK3,k1_tarski(sK6)) = iProver_top ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_8820,c_687]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_8870,plain,
% 7.95/1.44      ( r2_hidden(sK3,k1_tarski(sK6))
% 7.95/1.44      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.95/1.44      inference(predicate_to_equality_rev,[status(thm)],[c_8826]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_400,plain,
% 7.95/1.44      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.95/1.44      theory(equality) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_741,plain,
% 7.95/1.44      ( ~ r2_hidden(X0,X1)
% 7.95/1.44      | r2_hidden(sK3,k2_enumset1(sK6,sK6,sK6,sK6))
% 7.95/1.44      | k2_enumset1(sK6,sK6,sK6,sK6) != X1
% 7.95/1.44      | sK3 != X0 ),
% 7.95/1.44      inference(instantiation,[status(thm)],[c_400]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_843,plain,
% 7.95/1.44      ( ~ r2_hidden(sK3,X0)
% 7.95/1.44      | r2_hidden(sK3,k2_enumset1(sK6,sK6,sK6,sK6))
% 7.95/1.44      | k2_enumset1(sK6,sK6,sK6,sK6) != X0
% 7.95/1.44      | sK3 != sK3 ),
% 7.95/1.44      inference(instantiation,[status(thm)],[c_741]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_14108,plain,
% 7.95/1.44      ( r2_hidden(sK3,k2_enumset1(sK6,sK6,sK6,sK6))
% 7.95/1.44      | ~ r2_hidden(sK3,k1_tarski(sK6))
% 7.95/1.44      | k2_enumset1(sK6,sK6,sK6,sK6) != k1_tarski(sK6)
% 7.95/1.44      | sK3 != sK3 ),
% 7.95/1.44      inference(instantiation,[status(thm)],[c_843]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_14382,plain,
% 7.95/1.44      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.95/1.44      inference(global_propositional_subsumption,
% 7.95/1.44                [status(thm)],
% 7.95/1.44                [c_10282,c_27,c_26,c_728,c_763,c_792,c_6484,c_8870,c_14108]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_14430,plain,
% 7.95/1.44      ( r2_hidden(sK3,k1_xboole_0) = iProver_top ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_14382,c_687]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_5,plain,
% 7.95/1.44      ( k3_xboole_0(X0,X0) = X0 ),
% 7.95/1.44      inference(cnf_transformation,[],[f51]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_6,plain,
% 7.95/1.44      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 7.95/1.44      inference(cnf_transformation,[],[f53]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_12,plain,
% 7.95/1.44      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.95/1.44      inference(cnf_transformation,[],[f60]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_244,plain,
% 7.95/1.44      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | X3 != X1 | k1_xboole_0 != X2 ),
% 7.95/1.44      inference(resolution_lifted,[status(thm)],[c_6,c_12]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_245,plain,
% 7.95/1.44      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 7.95/1.44      inference(unflattening,[status(thm)],[c_244]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_678,plain,
% 7.95/1.44      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 7.95/1.44      inference(predicate_to_equality,[status(thm)],[c_245]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_1110,plain,
% 7.95/1.44      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_5,c_678]) ).
% 7.95/1.44  
% 7.95/1.44  cnf(c_18433,plain,
% 7.95/1.44      ( $false ),
% 7.95/1.44      inference(superposition,[status(thm)],[c_14430,c_1110]) ).
% 7.95/1.44  
% 7.95/1.44  
% 7.95/1.44  % SZS output end CNFRefutation for theBenchmark.p
% 7.95/1.44  
% 7.95/1.44  ------                               Statistics
% 7.95/1.44  
% 7.95/1.44  ------ General
% 7.95/1.44  
% 7.95/1.44  abstr_ref_over_cycles:                  0
% 7.95/1.44  abstr_ref_under_cycles:                 0
% 7.95/1.44  gc_basic_clause_elim:                   0
% 7.95/1.44  forced_gc_time:                         0
% 7.95/1.44  parsing_time:                           0.012
% 7.95/1.44  unif_index_cands_time:                  0.
% 7.95/1.44  unif_index_add_time:                    0.
% 7.95/1.44  orderings_time:                         0.
% 7.95/1.44  out_proof_time:                         0.019
% 7.95/1.44  total_time:                             0.917
% 7.95/1.44  num_of_symbols:                         47
% 7.95/1.44  num_of_terms:                           20107
% 7.95/1.44  
% 7.95/1.44  ------ Preprocessing
% 7.95/1.44  
% 7.95/1.44  num_of_splits:                          0
% 7.95/1.44  num_of_split_atoms:                     0
% 7.95/1.44  num_of_reused_defs:                     0
% 7.95/1.44  num_eq_ax_congr_red:                    45
% 7.95/1.44  num_of_sem_filtered_clauses:            1
% 7.95/1.44  num_of_subtypes:                        0
% 7.95/1.44  monotx_restored_types:                  0
% 7.95/1.44  sat_num_of_epr_types:                   0
% 7.95/1.44  sat_num_of_non_cyclic_types:            0
% 7.95/1.44  sat_guarded_non_collapsed_types:        0
% 7.95/1.44  num_pure_diseq_elim:                    0
% 7.95/1.44  simp_replaced_by:                       0
% 7.95/1.44  res_preprocessed:                       128
% 7.95/1.44  prep_upred:                             0
% 7.95/1.44  prep_unflattend:                        6
% 7.95/1.44  smt_new_axioms:                         0
% 7.95/1.44  pred_elim_cands:                        2
% 7.95/1.44  pred_elim:                              1
% 7.95/1.44  pred_elim_cl:                           1
% 7.95/1.44  pred_elim_cycles:                       3
% 7.95/1.44  merged_defs:                            0
% 7.95/1.44  merged_defs_ncl:                        0
% 7.95/1.44  bin_hyper_res:                          0
% 7.95/1.44  prep_cycles:                            4
% 7.95/1.44  pred_elim_time:                         0.002
% 7.95/1.44  splitting_time:                         0.
% 7.95/1.44  sem_filter_time:                        0.
% 7.95/1.44  monotx_time:                            0.001
% 7.95/1.44  subtype_inf_time:                       0.
% 7.95/1.44  
% 7.95/1.44  ------ Problem properties
% 7.95/1.44  
% 7.95/1.44  clauses:                                28
% 7.95/1.44  conjectures:                            3
% 7.95/1.44  epr:                                    2
% 7.95/1.44  horn:                                   24
% 7.95/1.44  ground:                                 3
% 7.95/1.44  unary:                                  18
% 7.95/1.44  binary:                                 5
% 7.95/1.44  lits:                                   46
% 7.95/1.44  lits_eq:                                25
% 7.95/1.44  fd_pure:                                0
% 7.95/1.44  fd_pseudo:                              0
% 7.95/1.44  fd_cond:                                1
% 7.95/1.44  fd_pseudo_cond:                         4
% 7.95/1.44  ac_symbols:                             0
% 7.95/1.44  
% 7.95/1.44  ------ Propositional Solver
% 7.95/1.44  
% 7.95/1.44  prop_solver_calls:                      30
% 7.95/1.44  prop_fast_solver_calls:                 1086
% 7.95/1.44  smt_solver_calls:                       0
% 7.95/1.44  smt_fast_solver_calls:                  0
% 7.95/1.44  prop_num_of_clauses:                    7019
% 7.95/1.44  prop_preprocess_simplified:             14863
% 7.95/1.44  prop_fo_subsumed:                       157
% 7.95/1.44  prop_solver_time:                       0.
% 7.95/1.44  smt_solver_time:                        0.
% 7.95/1.44  smt_fast_solver_time:                   0.
% 7.95/1.44  prop_fast_solver_time:                  0.
% 7.95/1.44  prop_unsat_core_time:                   0.
% 7.95/1.44  
% 7.95/1.44  ------ QBF
% 7.95/1.44  
% 7.95/1.44  qbf_q_res:                              0
% 7.95/1.44  qbf_num_tautologies:                    0
% 7.95/1.44  qbf_prep_cycles:                        0
% 7.95/1.44  
% 7.95/1.44  ------ BMC1
% 7.95/1.44  
% 7.95/1.44  bmc1_current_bound:                     -1
% 7.95/1.44  bmc1_last_solved_bound:                 -1
% 7.95/1.44  bmc1_unsat_core_size:                   -1
% 7.95/1.44  bmc1_unsat_core_parents_size:           -1
% 7.95/1.44  bmc1_merge_next_fun:                    0
% 7.95/1.44  bmc1_unsat_core_clauses_time:           0.
% 7.95/1.44  
% 7.95/1.44  ------ Instantiation
% 7.95/1.44  
% 7.95/1.44  inst_num_of_clauses:                    1908
% 7.95/1.44  inst_num_in_passive:                    888
% 7.95/1.44  inst_num_in_active:                     598
% 7.95/1.44  inst_num_in_unprocessed:                422
% 7.95/1.44  inst_num_of_loops:                      790
% 7.95/1.44  inst_num_of_learning_restarts:          0
% 7.95/1.44  inst_num_moves_active_passive:          191
% 7.95/1.44  inst_lit_activity:                      0
% 7.95/1.44  inst_lit_activity_moves:                0
% 7.95/1.44  inst_num_tautologies:                   0
% 7.95/1.44  inst_num_prop_implied:                  0
% 7.95/1.44  inst_num_existing_simplified:           0
% 7.95/1.44  inst_num_eq_res_simplified:             0
% 7.95/1.44  inst_num_child_elim:                    0
% 7.95/1.44  inst_num_of_dismatching_blockings:      1360
% 7.95/1.44  inst_num_of_non_proper_insts:           2364
% 7.95/1.44  inst_num_of_duplicates:                 0
% 7.95/1.44  inst_inst_num_from_inst_to_res:         0
% 7.95/1.44  inst_dismatching_checking_time:         0.
% 7.95/1.44  
% 7.95/1.44  ------ Resolution
% 7.95/1.44  
% 7.95/1.44  res_num_of_clauses:                     0
% 7.95/1.44  res_num_in_passive:                     0
% 7.95/1.44  res_num_in_active:                      0
% 7.95/1.44  res_num_of_loops:                       132
% 7.95/1.44  res_forward_subset_subsumed:            352
% 7.95/1.44  res_backward_subset_subsumed:           0
% 7.95/1.44  res_forward_subsumed:                   0
% 7.95/1.44  res_backward_subsumed:                  0
% 7.95/1.44  res_forward_subsumption_resolution:     0
% 7.95/1.44  res_backward_subsumption_resolution:    0
% 7.95/1.44  res_clause_to_clause_subsumption:       3571
% 7.95/1.44  res_orphan_elimination:                 0
% 7.95/1.44  res_tautology_del:                      120
% 7.95/1.44  res_num_eq_res_simplified:              0
% 7.95/1.44  res_num_sel_changes:                    0
% 7.95/1.44  res_moves_from_active_to_pass:          0
% 7.95/1.44  
% 7.95/1.44  ------ Superposition
% 7.95/1.44  
% 7.95/1.44  sup_time_total:                         0.
% 7.95/1.44  sup_time_generating:                    0.
% 7.95/1.44  sup_time_sim_full:                      0.
% 7.95/1.44  sup_time_sim_immed:                     0.
% 7.95/1.44  
% 7.95/1.44  sup_num_of_clauses:                     368
% 7.95/1.44  sup_num_in_active:                      83
% 7.95/1.44  sup_num_in_passive:                     285
% 7.95/1.44  sup_num_of_loops:                       156
% 7.95/1.44  sup_fw_superposition:                   1415
% 7.95/1.44  sup_bw_superposition:                   1211
% 7.95/1.44  sup_immediate_simplified:               1269
% 7.95/1.44  sup_given_eliminated:                   4
% 7.95/1.44  comparisons_done:                       0
% 7.95/1.44  comparisons_avoided:                    147
% 7.95/1.44  
% 7.95/1.44  ------ Simplifications
% 7.95/1.44  
% 7.95/1.44  
% 7.95/1.44  sim_fw_subset_subsumed:                 33
% 7.95/1.44  sim_bw_subset_subsumed:                 226
% 7.95/1.44  sim_fw_subsumed:                        66
% 7.95/1.44  sim_bw_subsumed:                        18
% 7.95/1.44  sim_fw_subsumption_res:                 0
% 7.95/1.44  sim_bw_subsumption_res:                 0
% 7.95/1.44  sim_tautology_del:                      20
% 7.95/1.44  sim_eq_tautology_del:                   537
% 7.95/1.44  sim_eq_res_simp:                        0
% 7.95/1.44  sim_fw_demodulated:                     900
% 7.95/1.44  sim_bw_demodulated:                     62
% 7.95/1.44  sim_light_normalised:                   613
% 7.95/1.44  sim_joinable_taut:                      0
% 7.95/1.44  sim_joinable_simp:                      0
% 7.95/1.44  sim_ac_normalised:                      0
% 7.95/1.44  sim_smt_subsumption:                    0
% 7.95/1.44  
%------------------------------------------------------------------------------
