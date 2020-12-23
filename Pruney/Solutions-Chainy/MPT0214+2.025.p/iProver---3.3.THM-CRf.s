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
% DateTime   : Thu Dec  3 11:28:46 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 481 expanded)
%              Number of clauses        :   37 (  86 expanded)
%              Number of leaves         :   17 ( 127 expanded)
%              Depth                    :   18
%              Number of atoms          :  300 (1418 expanded)
%              Number of equality atoms :  196 (1001 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f24])).

fof(f33,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f49,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK4 != sK5
      & r1_tarski(k1_tarski(sK4),k1_tarski(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( sK4 != sK5
    & r1_tarski(k1_tarski(sK4),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f49])).

fof(f87,plain,(
    r1_tarski(k1_tarski(sK4),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f50])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f77,f89])).

fof(f113,plain,(
    r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f87,f90,f90])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f47])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f84,f90,f90])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f65,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f103,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f65,f79])).

fof(f118,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f103])).

fof(f119,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f118])).

fof(f88,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f108,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f72,f90])).

fof(f123,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f108])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f73,f90])).

fof(f121,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f107])).

fof(f122,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f121])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f51,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f34])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f94,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f60,f55])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f96,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f62,f55])).

cnf(c_30,negated_conjecture,
    ( r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_608,plain,
    ( r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_28,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_609,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1028,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k2_enumset1(sK4,sK4,sK4,sK4)
    | k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_608,c_609])).

cnf(c_19,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_617,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1478,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0
    | r2_hidden(sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_617])).

cnf(c_29,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_43,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_23,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_46,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_231,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_813,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_814,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_922,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(X0,X0,X0,X0))
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_923,plain,
    ( sK5 = X0
    | r2_hidden(sK5,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_922])).

cnf(c_925,plain,
    ( sK5 = sK4
    | r2_hidden(sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_923])).

cnf(c_1656,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1478,c_29,c_43,c_46,c_814,c_925])).

cnf(c_1662,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1656,c_617])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_631,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10535,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_631])).

cnf(c_10881,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_10535])).

cnf(c_9,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_626,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3223,plain,
    ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_626])).

cnf(c_1665,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1656,c_609])).

cnf(c_1668,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1665,c_1656])).

cnf(c_3246,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3223,c_1668])).

cnf(c_11,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_625,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2305,plain,
    ( r1_xboole_0(k5_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_625])).

cnf(c_3496,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3246,c_2305])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10881,c_3496])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:01:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.72/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/0.98  
% 3.72/0.98  ------  iProver source info
% 3.72/0.98  
% 3.72/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.72/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/0.98  git: non_committed_changes: false
% 3.72/0.98  git: last_make_outside_of_git: false
% 3.72/0.98  
% 3.72/0.98  ------ 
% 3.72/0.98  ------ Parsing...
% 3.72/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/0.98  ------ Proving...
% 3.72/0.98  ------ Problem Properties 
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  clauses                                 31
% 3.72/0.98  conjectures                             2
% 3.72/0.98  EPR                                     1
% 3.72/0.98  Horn                                    25
% 3.72/0.98  unary                                   17
% 3.72/0.98  binary                                  6
% 3.72/0.98  lits                                    56
% 3.72/0.98  lits eq                                 29
% 3.72/0.98  fd_pure                                 0
% 3.72/0.99  fd_pseudo                               0
% 3.72/0.99  fd_cond                                 1
% 3.72/0.99  fd_pseudo_cond                          7
% 3.72/0.99  AC symbols                              0
% 3.72/0.99  
% 3.72/0.99  ------ Input Options Time Limit: Unbounded
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ 
% 3.72/0.99  Current options:
% 3.72/0.99  ------ 
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  ------ Proving...
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  % SZS status Theorem for theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  fof(f24,conjecture,(
% 3.72/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f25,negated_conjecture,(
% 3.72/0.99    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.72/0.99    inference(negated_conjecture,[],[f24])).
% 3.72/0.99  
% 3.72/0.99  fof(f33,plain,(
% 3.72/0.99    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 3.72/0.99    inference(ennf_transformation,[],[f25])).
% 3.72/0.99  
% 3.72/0.99  fof(f49,plain,(
% 3.72/0.99    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK4 != sK5 & r1_tarski(k1_tarski(sK4),k1_tarski(sK5)))),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f50,plain,(
% 3.72/0.99    sK4 != sK5 & r1_tarski(k1_tarski(sK4),k1_tarski(sK5))),
% 3.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f49])).
% 3.72/0.99  
% 3.72/0.99  fof(f87,plain,(
% 3.72/0.99    r1_tarski(k1_tarski(sK4),k1_tarski(sK5))),
% 3.72/0.99    inference(cnf_transformation,[],[f50])).
% 3.72/0.99  
% 3.72/0.99  fof(f16,axiom,(
% 3.72/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f77,plain,(
% 3.72/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f16])).
% 3.72/0.99  
% 3.72/0.99  fof(f17,axiom,(
% 3.72/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f78,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f17])).
% 3.72/0.99  
% 3.72/0.99  fof(f18,axiom,(
% 3.72/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f79,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f18])).
% 3.72/0.99  
% 3.72/0.99  fof(f89,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f78,f79])).
% 3.72/0.99  
% 3.72/0.99  fof(f90,plain,(
% 3.72/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f77,f89])).
% 3.72/0.99  
% 3.72/0.99  fof(f113,plain,(
% 3.72/0.99    r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5))),
% 3.72/0.99    inference(definition_unfolding,[],[f87,f90,f90])).
% 3.72/0.99  
% 3.72/0.99  fof(f23,axiom,(
% 3.72/0.99    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f47,plain,(
% 3.72/0.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.72/0.99    inference(nnf_transformation,[],[f23])).
% 3.72/0.99  
% 3.72/0.99  fof(f48,plain,(
% 3.72/0.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.72/0.99    inference(flattening,[],[f47])).
% 3.72/0.99  
% 3.72/0.99  fof(f84,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.72/0.99    inference(cnf_transformation,[],[f48])).
% 3.72/0.99  
% 3.72/0.99  fof(f112,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 3.72/0.99    inference(definition_unfolding,[],[f84,f90,f90])).
% 3.72/0.99  
% 3.72/0.99  fof(f13,axiom,(
% 3.72/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f32,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.72/0.99    inference(ennf_transformation,[],[f13])).
% 3.72/0.99  
% 3.72/0.99  fof(f38,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.72/0.99    inference(nnf_transformation,[],[f32])).
% 3.72/0.99  
% 3.72/0.99  fof(f39,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.72/0.99    inference(flattening,[],[f38])).
% 3.72/0.99  
% 3.72/0.99  fof(f40,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.72/0.99    inference(rectify,[],[f39])).
% 3.72/0.99  
% 3.72/0.99  fof(f41,plain,(
% 3.72/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f42,plain,(
% 3.72/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 3.72/0.99  
% 3.72/0.99  fof(f65,plain,(
% 3.72/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.72/0.99    inference(cnf_transformation,[],[f42])).
% 3.72/0.99  
% 3.72/0.99  fof(f103,plain,(
% 3.72/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.72/0.99    inference(definition_unfolding,[],[f65,f79])).
% 3.72/0.99  
% 3.72/0.99  fof(f118,plain,(
% 3.72/0.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 3.72/0.99    inference(equality_resolution,[],[f103])).
% 3.72/0.99  
% 3.72/0.99  fof(f119,plain,(
% 3.72/0.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 3.72/0.99    inference(equality_resolution,[],[f118])).
% 3.72/0.99  
% 3.72/0.99  fof(f88,plain,(
% 3.72/0.99    sK4 != sK5),
% 3.72/0.99    inference(cnf_transformation,[],[f50])).
% 3.72/0.99  
% 3.72/0.99  fof(f14,axiom,(
% 3.72/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f43,plain,(
% 3.72/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.72/0.99    inference(nnf_transformation,[],[f14])).
% 3.72/0.99  
% 3.72/0.99  fof(f44,plain,(
% 3.72/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.72/0.99    inference(rectify,[],[f43])).
% 3.72/0.99  
% 3.72/0.99  fof(f45,plain,(
% 3.72/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f46,plain,(
% 3.72/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).
% 3.72/0.99  
% 3.72/0.99  fof(f72,plain,(
% 3.72/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.72/0.99    inference(cnf_transformation,[],[f46])).
% 3.72/0.99  
% 3.72/0.99  fof(f108,plain,(
% 3.72/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.72/0.99    inference(definition_unfolding,[],[f72,f90])).
% 3.72/0.99  
% 3.72/0.99  fof(f123,plain,(
% 3.72/0.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 3.72/0.99    inference(equality_resolution,[],[f108])).
% 3.72/0.99  
% 3.72/0.99  fof(f73,plain,(
% 3.72/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.72/0.99    inference(cnf_transformation,[],[f46])).
% 3.72/0.99  
% 3.72/0.99  fof(f107,plain,(
% 3.72/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.72/0.99    inference(definition_unfolding,[],[f73,f90])).
% 3.72/0.99  
% 3.72/0.99  fof(f121,plain,(
% 3.72/0.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 3.72/0.99    inference(equality_resolution,[],[f107])).
% 3.72/0.99  
% 3.72/0.99  fof(f122,plain,(
% 3.72/0.99    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 3.72/0.99    inference(equality_resolution,[],[f121])).
% 3.72/0.99  
% 3.72/0.99  fof(f1,axiom,(
% 3.72/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f26,plain,(
% 3.72/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.72/0.99    inference(rectify,[],[f1])).
% 3.72/0.99  
% 3.72/0.99  fof(f51,plain,(
% 3.72/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.72/0.99    inference(cnf_transformation,[],[f26])).
% 3.72/0.99  
% 3.72/0.99  fof(f2,axiom,(
% 3.72/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f27,plain,(
% 3.72/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.72/0.99    inference(rectify,[],[f2])).
% 3.72/0.99  
% 3.72/0.99  fof(f28,plain,(
% 3.72/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.72/0.99    inference(ennf_transformation,[],[f27])).
% 3.72/0.99  
% 3.72/0.99  fof(f34,plain,(
% 3.72/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.72/0.99    introduced(choice_axiom,[])).
% 3.72/0.99  
% 3.72/0.99  fof(f35,plain,(
% 3.72/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f34])).
% 3.72/0.99  
% 3.72/0.99  fof(f53,plain,(
% 3.72/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.72/0.99    inference(cnf_transformation,[],[f35])).
% 3.72/0.99  
% 3.72/0.99  fof(f9,axiom,(
% 3.72/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f60,plain,(
% 3.72/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f9])).
% 3.72/0.99  
% 3.72/0.99  fof(f4,axiom,(
% 3.72/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f55,plain,(
% 3.72/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.72/0.99    inference(cnf_transformation,[],[f4])).
% 3.72/0.99  
% 3.72/0.99  fof(f94,plain,(
% 3.72/0.99    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f60,f55])).
% 3.72/0.99  
% 3.72/0.99  fof(f11,axiom,(
% 3.72/0.99    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.72/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.99  
% 3.72/0.99  fof(f62,plain,(
% 3.72/0.99    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.72/0.99    inference(cnf_transformation,[],[f11])).
% 3.72/0.99  
% 3.72/0.99  fof(f96,plain,(
% 3.72/0.99    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 3.72/0.99    inference(definition_unfolding,[],[f62,f55])).
% 3.72/0.99  
% 3.72/0.99  cnf(c_30,negated_conjecture,
% 3.72/0.99      ( r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 3.72/0.99      inference(cnf_transformation,[],[f113]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_608,plain,
% 3.72/0.99      ( r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_28,plain,
% 3.72/0.99      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 3.72/0.99      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.72/0.99      | k1_xboole_0 = X0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f112]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_609,plain,
% 3.72/0.99      ( k2_enumset1(X0,X0,X0,X0) = X1
% 3.72/0.99      | k1_xboole_0 = X1
% 3.72/0.99      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1028,plain,
% 3.72/0.99      ( k2_enumset1(sK5,sK5,sK5,sK5) = k2_enumset1(sK4,sK4,sK4,sK4)
% 3.72/0.99      | k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0 ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_608,c_609]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_19,plain,
% 3.72/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 3.72/0.99      inference(cnf_transformation,[],[f119]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_617,plain,
% 3.72/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1478,plain,
% 3.72/0.99      ( k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0
% 3.72/0.99      | r2_hidden(sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1028,c_617]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_29,negated_conjecture,
% 3.72/0.99      ( sK4 != sK5 ),
% 3.72/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_24,plain,
% 3.72/0.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 3.72/0.99      inference(cnf_transformation,[],[f123]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_43,plain,
% 3.72/0.99      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | sK4 = sK4 ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_24]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_23,plain,
% 3.72/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 3.72/0.99      inference(cnf_transformation,[],[f122]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_46,plain,
% 3.72/0.99      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_231,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_813,plain,
% 3.72/0.99      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_231]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_814,plain,
% 3.72/0.99      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_813]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_922,plain,
% 3.72/0.99      ( ~ r2_hidden(sK5,k2_enumset1(X0,X0,X0,X0)) | sK5 = X0 ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_24]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_923,plain,
% 3.72/0.99      ( sK5 = X0
% 3.72/0.99      | r2_hidden(sK5,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_922]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_925,plain,
% 3.72/0.99      ( sK5 = sK4
% 3.72/0.99      | r2_hidden(sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
% 3.72/0.99      inference(instantiation,[status(thm)],[c_923]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1656,plain,
% 3.72/0.99      ( k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0 ),
% 3.72/0.99      inference(global_propositional_subsumption,
% 3.72/0.99                [status(thm)],
% 3.72/0.99                [c_1478,c_29,c_43,c_46,c_814,c_925]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1662,plain,
% 3.72/0.99      ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1656,c_617]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1,plain,
% 3.72/0.99      ( k3_xboole_0(X0,X0) = X0 ),
% 3.72/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2,plain,
% 3.72/0.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.72/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_631,plain,
% 3.72/0.99      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 3.72/0.99      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_10535,plain,
% 3.72/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.72/0.99      | r1_xboole_0(X1,X1) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1,c_631]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_10881,plain,
% 3.72/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1662,c_10535]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_9,plain,
% 3.72/0.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 3.72/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_626,plain,
% 3.72/0.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3223,plain,
% 3.72/0.99      ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1,c_626]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1665,plain,
% 3.72/0.99      ( k2_enumset1(sK4,sK4,sK4,sK4) = X0
% 3.72/0.99      | k1_xboole_0 = X0
% 3.72/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1656,c_609]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_1668,plain,
% 3.72/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.72/0.99      inference(demodulation,[status(thm)],[c_1665,c_1656]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3246,plain,
% 3.72/0.99      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3223,c_1668]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_11,plain,
% 3.72/0.99      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 3.72/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_625,plain,
% 3.72/0.99      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 3.72/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_2305,plain,
% 3.72/0.99      ( r1_xboole_0(k5_xboole_0(X0,X0),X0) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_1,c_625]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(c_3496,plain,
% 3.72/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.72/0.99      inference(superposition,[status(thm)],[c_3246,c_2305]) ).
% 3.72/0.99  
% 3.72/0.99  cnf(contradiction,plain,
% 3.72/0.99      ( $false ),
% 3.72/0.99      inference(minisat,[status(thm)],[c_10881,c_3496]) ).
% 3.72/0.99  
% 3.72/0.99  
% 3.72/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.72/0.99  
% 3.72/0.99  ------                               Statistics
% 3.72/0.99  
% 3.72/0.99  ------ Selected
% 3.72/0.99  
% 3.72/0.99  total_time:                             0.318
% 3.72/0.99  
%------------------------------------------------------------------------------
