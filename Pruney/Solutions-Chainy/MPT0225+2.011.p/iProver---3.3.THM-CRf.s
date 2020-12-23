%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:06 EST 2020

% Result     : Theorem 7.15s
% Output     : CNFRefutation 7.15s
% Verified   : 
% Statistics : Number of formulae       :  123 (1144 expanded)
%              Number of clauses        :   67 ( 206 expanded)
%              Number of leaves         :   20 ( 357 expanded)
%              Depth                    :   15
%              Number of atoms          :  348 (1912 expanded)
%              Number of equality atoms :  214 (1593 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f31,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f22])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f46,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) )
        & ( X0 != X1
          | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) )
   => ( ( sK4 = sK5
        | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) != k1_tarski(sK4) )
      & ( sK4 != sK5
        | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( sK4 = sK5
      | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) != k1_tarski(sK4) )
    & ( sK4 != sK5
      | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f46])).

fof(f77,plain,
    ( sK4 != sK5
    | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f80])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f70,f81])).

fof(f96,plain,
    ( sK4 != sK5
    | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f77,f82,f82,f82])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f94,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f76,f82,f82])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f43])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f75,f82,f82])).

fof(f100,plain,(
    ! [X1] : r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f91])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,
    ( sK4 = sK5
    | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) != k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,
    ( sK4 = sK5
    | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f78,f82,f82,f82])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f73,f82,f82])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f32])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f66,f82])).

fof(f97,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f89])).

fof(f98,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f97])).

cnf(c_261,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_255,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2968,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_261,c_255])).

cnf(c_256,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1716,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_256,c_255])).

cnf(c_24,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK4 != sK5 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_10236,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | sK4 != sK5 ),
    inference(resolution,[status(thm)],[c_1716,c_24])).

cnf(c_22,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_26,plain,
    ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_35,plain,
    ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_262,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
    theory(equality)).

cnf(c_267,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_922,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_923,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_922])).

cnf(c_1122,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != X0 ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_1749,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1122])).

cnf(c_1714,plain,
    ( X0 != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = X0
    | sK4 != sK5 ),
    inference(resolution,[status(thm)],[c_256,c_24])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1725,plain,
    ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | sK4 != sK5
    | k1_xboole_0 != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(resolution,[status(thm)],[c_1714,c_8])).

cnf(c_7074,plain,
    ( sK5 = sK4
    | sK4 != sK5
    | k1_xboole_0 != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(resolution,[status(thm)],[c_22,c_1725])).

cnf(c_23,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK4 = sK5 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_920,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
    | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != X0
    | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_1038,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_920])).

cnf(c_1039,plain,
    ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_1050,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1052,plain,
    ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | sK5 = sK4 ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1116,plain,
    ( ~ r1_tarski(k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k1_xboole_0 = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1117,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k1_xboole_0 = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | r1_tarski(k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1116])).

cnf(c_1056,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_1176,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_1178,plain,
    ( sK5 != sK5
    | sK5 = sK4
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_1176])).

cnf(c_1177,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_11,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1603,plain,
    ( r1_tarski(k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1604,plain,
    ( r1_tarski(k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1603])).

cnf(c_1040,plain,
    ( X0 != X1
    | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != X1
    | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = X0 ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_1133,plain,
    ( X0 != k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = X0
    | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_2196,plain,
    ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_1133])).

cnf(c_2401,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2403,plain,
    ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2401])).

cnf(c_9521,plain,
    ( sK5 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7074,c_23,c_1038,c_1039,c_1052,c_1117,c_1178,c_1177,c_1604,c_2196,c_2403])).

cnf(c_11005,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10236,c_24,c_23,c_26,c_35,c_267,c_923,c_1038,c_1039,c_1052,c_1117,c_1178,c_1177,c_1604,c_1749,c_2196,c_2403])).

cnf(c_11849,plain,
    ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(resolution,[status(thm)],[c_11005,c_1716])).

cnf(c_15528,plain,
    ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0)
    | r1_tarski(k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0) ),
    inference(resolution,[status(thm)],[c_2968,c_11849])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1223,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k4_xboole_0(X3,X1)) ),
    inference(resolution,[status(thm)],[c_1,c_13])).

cnf(c_259,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2916,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(X1,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | X1 != X0
    | sK4 != sK5 ),
    inference(resolution,[status(thm)],[c_259,c_24])).

cnf(c_3393,plain,
    ( X1 != X0
    | r2_hidden(X1,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | ~ r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2916,c_23,c_26,c_35,c_923,c_1038,c_1039,c_1052,c_1117,c_1178,c_1177,c_1604,c_2196,c_2403])).

cnf(c_3394,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(X1,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | X1 != X0 ),
    inference(renaming,[status(thm)],[c_3393])).

cnf(c_17,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3427,plain,
    ( r2_hidden(X0,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | X0 != sK4 ),
    inference(resolution,[status(thm)],[c_3394,c_17])).

cnf(c_22408,plain,
    ( ~ r1_tarski(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ r2_hidden(X1,X0)
    | X1 != sK4 ),
    inference(resolution,[status(thm)],[c_1223,c_3427])).

cnf(c_24919,plain,
    ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ r2_hidden(X0,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | X0 != sK4 ),
    inference(resolution,[status(thm)],[c_15528,c_22408])).

cnf(c_24921,plain,
    ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_24919])).

cnf(c_946,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k4_xboole_0(X2,X3),X2)
    | X1 != X2
    | X0 != k4_xboole_0(X2,X3) ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_1252,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r1_tarski(k4_xboole_0(X2,X3),X2)
    | X1 != X2
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k4_xboole_0(X2,X3) ),
    inference(instantiation,[status(thm)],[c_946])).

cnf(c_3989,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k4_xboole_0(X1,X2)
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != X1 ),
    inference(instantiation,[status(thm)],[c_1252])).

cnf(c_4689,plain,
    ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ r1_tarski(k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_3989])).

cnf(c_3396,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3394])).

cnf(c_1171,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
    | sK5 != X0
    | sK5 != X1
    | sK5 != X2
    | sK5 != X3
    | sK5 != X4
    | sK5 != X5
    | sK5 != X6
    | sK5 != X7 ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_1173,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK5 != sK4 ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_41,plain,
    ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24921,c_9521,c_4689,c_3396,c_1749,c_1603,c_1173,c_923,c_267,c_41,c_35,c_26,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:51:04 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.33  % Running in FOF mode
% 7.15/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.15/1.48  
% 7.15/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.15/1.48  
% 7.15/1.48  ------  iProver source info
% 7.15/1.48  
% 7.15/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.15/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.15/1.48  git: non_committed_changes: false
% 7.15/1.48  git: last_make_outside_of_git: false
% 7.15/1.48  
% 7.15/1.48  ------ 
% 7.15/1.48  ------ Parsing...
% 7.15/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.15/1.48  
% 7.15/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.15/1.48  
% 7.15/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.15/1.48  
% 7.15/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.15/1.48  ------ Proving...
% 7.15/1.48  ------ Problem Properties 
% 7.15/1.48  
% 7.15/1.48  
% 7.15/1.48  clauses                                 25
% 7.15/1.48  conjectures                             2
% 7.15/1.48  EPR                                     2
% 7.15/1.48  Horn                                    19
% 7.15/1.48  unary                                   8
% 7.15/1.48  binary                                  13
% 7.15/1.48  lits                                    46
% 7.15/1.48  lits eq                                 20
% 7.15/1.48  fd_pure                                 0
% 7.15/1.48  fd_pseudo                               0
% 7.15/1.48  fd_cond                                 2
% 7.15/1.48  fd_pseudo_cond                          4
% 7.15/1.48  AC symbols                              1
% 7.15/1.48  
% 7.15/1.48  ------ Input Options Time Limit: Unbounded
% 7.15/1.48  
% 7.15/1.48  
% 7.15/1.48  ------ 
% 7.15/1.48  Current options:
% 7.15/1.48  ------ 
% 7.15/1.48  
% 7.15/1.48  
% 7.15/1.48  
% 7.15/1.48  
% 7.15/1.48  ------ Proving...
% 7.15/1.48  
% 7.15/1.48  
% 7.15/1.48  % SZS status Theorem for theBenchmark.p
% 7.15/1.48  
% 7.15/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.15/1.48  
% 7.15/1.48  fof(f21,conjecture,(
% 7.15/1.48    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 7.15/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.48  
% 7.15/1.48  fof(f22,negated_conjecture,(
% 7.15/1.48    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 7.15/1.48    inference(negated_conjecture,[],[f21])).
% 7.15/1.48  
% 7.15/1.48  fof(f31,plain,(
% 7.15/1.48    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <~> X0 != X1)),
% 7.15/1.48    inference(ennf_transformation,[],[f22])).
% 7.15/1.48  
% 7.15/1.48  fof(f45,plain,(
% 7.15/1.48    ? [X0,X1] : ((X0 = X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)))),
% 7.15/1.48    inference(nnf_transformation,[],[f31])).
% 7.15/1.48  
% 7.15/1.48  fof(f46,plain,(
% 7.15/1.48    ? [X0,X1] : ((X0 = X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))) => ((sK4 = sK5 | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) != k1_tarski(sK4)) & (sK4 != sK5 | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)))),
% 7.15/1.48    introduced(choice_axiom,[])).
% 7.15/1.48  
% 7.15/1.48  fof(f47,plain,(
% 7.15/1.48    (sK4 = sK5 | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) != k1_tarski(sK4)) & (sK4 != sK5 | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4))),
% 7.15/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f46])).
% 7.15/1.48  
% 7.15/1.48  fof(f77,plain,(
% 7.15/1.48    sK4 != sK5 | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 7.15/1.48    inference(cnf_transformation,[],[f47])).
% 7.15/1.48  
% 7.15/1.48  fof(f16,axiom,(
% 7.15/1.48    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0)),
% 7.15/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.48  
% 7.15/1.48  fof(f70,plain,(
% 7.15/1.48    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 7.15/1.48    inference(cnf_transformation,[],[f16])).
% 7.15/1.48  
% 7.15/1.48  fof(f15,axiom,(
% 7.15/1.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.15/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.48  
% 7.15/1.48  fof(f69,plain,(
% 7.15/1.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.15/1.48    inference(cnf_transformation,[],[f15])).
% 7.15/1.48  
% 7.15/1.48  fof(f17,axiom,(
% 7.15/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)),
% 7.15/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.48  
% 7.15/1.48  fof(f71,plain,(
% 7.15/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 7.15/1.48    inference(cnf_transformation,[],[f17])).
% 7.15/1.48  
% 7.15/1.48  fof(f18,axiom,(
% 7.15/1.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)),
% 7.15/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.48  
% 7.15/1.48  fof(f72,plain,(
% 7.15/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.15/1.48    inference(cnf_transformation,[],[f18])).
% 7.15/1.48  
% 7.15/1.48  fof(f80,plain,(
% 7.15/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.15/1.48    inference(definition_unfolding,[],[f71,f72])).
% 7.15/1.48  
% 7.15/1.48  fof(f81,plain,(
% 7.15/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.15/1.48    inference(definition_unfolding,[],[f69,f80])).
% 7.15/1.48  
% 7.15/1.48  fof(f82,plain,(
% 7.15/1.48    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.15/1.48    inference(definition_unfolding,[],[f70,f81])).
% 7.15/1.48  
% 7.15/1.48  fof(f96,plain,(
% 7.15/1.48    sK4 != sK5 | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 7.15/1.48    inference(definition_unfolding,[],[f77,f82,f82,f82])).
% 7.15/1.48  
% 7.15/1.48  fof(f20,axiom,(
% 7.15/1.48    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 7.15/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.48  
% 7.15/1.48  fof(f30,plain,(
% 7.15/1.48    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 7.15/1.48    inference(ennf_transformation,[],[f20])).
% 7.15/1.48  
% 7.15/1.48  fof(f76,plain,(
% 7.15/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1))) )),
% 7.15/1.48    inference(cnf_transformation,[],[f30])).
% 7.15/1.48  
% 7.15/1.48  fof(f94,plain,(
% 7.15/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 7.15/1.48    inference(definition_unfolding,[],[f76,f82,f82])).
% 7.15/1.48  
% 7.15/1.48  fof(f19,axiom,(
% 7.15/1.48    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.15/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.48  
% 7.15/1.48  fof(f43,plain,(
% 7.15/1.48    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.15/1.48    inference(nnf_transformation,[],[f19])).
% 7.15/1.48  
% 7.15/1.48  fof(f44,plain,(
% 7.15/1.48    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.15/1.48    inference(flattening,[],[f43])).
% 7.15/1.48  
% 7.15/1.48  fof(f75,plain,(
% 7.15/1.48    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) != X0) )),
% 7.15/1.48    inference(cnf_transformation,[],[f44])).
% 7.15/1.48  
% 7.15/1.48  fof(f91,plain,(
% 7.15/1.48    ( ! [X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0) )),
% 7.15/1.48    inference(definition_unfolding,[],[f75,f82,f82])).
% 7.15/1.48  
% 7.15/1.48  fof(f100,plain,(
% 7.15/1.48    ( ! [X1] : (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 7.15/1.48    inference(equality_resolution,[],[f91])).
% 7.15/1.48  
% 7.15/1.48  fof(f5,axiom,(
% 7.15/1.48    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 7.15/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.48  
% 7.15/1.48  fof(f38,plain,(
% 7.15/1.48    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 7.15/1.48    inference(nnf_transformation,[],[f5])).
% 7.15/1.48  
% 7.15/1.48  fof(f55,plain,(
% 7.15/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 7.15/1.48    inference(cnf_transformation,[],[f38])).
% 7.15/1.48  
% 7.15/1.48  fof(f78,plain,(
% 7.15/1.48    sK4 = sK5 | k4_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) != k1_tarski(sK4)),
% 7.15/1.48    inference(cnf_transformation,[],[f47])).
% 7.15/1.48  
% 7.15/1.48  fof(f95,plain,(
% 7.15/1.48    sK4 = sK5 | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 7.15/1.48    inference(definition_unfolding,[],[f78,f82,f82,f82])).
% 7.15/1.48  
% 7.15/1.48  fof(f73,plain,(
% 7.15/1.48    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 7.15/1.48    inference(cnf_transformation,[],[f44])).
% 7.15/1.48  
% 7.15/1.48  fof(f93,plain,(
% 7.15/1.48    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 7.15/1.48    inference(definition_unfolding,[],[f73,f82,f82])).
% 7.15/1.48  
% 7.15/1.48  fof(f8,axiom,(
% 7.15/1.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.15/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.48  
% 7.15/1.48  fof(f59,plain,(
% 7.15/1.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.15/1.48    inference(cnf_transformation,[],[f8])).
% 7.15/1.48  
% 7.15/1.48  fof(f2,axiom,(
% 7.15/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.15/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.48  
% 7.15/1.48  fof(f23,plain,(
% 7.15/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.15/1.48    inference(rectify,[],[f2])).
% 7.15/1.48  
% 7.15/1.48  fof(f25,plain,(
% 7.15/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.15/1.48    inference(ennf_transformation,[],[f23])).
% 7.15/1.48  
% 7.15/1.48  fof(f32,plain,(
% 7.15/1.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.15/1.48    introduced(choice_axiom,[])).
% 7.15/1.48  
% 7.15/1.48  fof(f33,plain,(
% 7.15/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.15/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f32])).
% 7.15/1.48  
% 7.15/1.48  fof(f51,plain,(
% 7.15/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.15/1.48    inference(cnf_transformation,[],[f33])).
% 7.15/1.48  
% 7.15/1.48  fof(f10,axiom,(
% 7.15/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 7.15/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.48  
% 7.15/1.48  fof(f29,plain,(
% 7.15/1.48    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.15/1.48    inference(ennf_transformation,[],[f10])).
% 7.15/1.48  
% 7.15/1.48  fof(f61,plain,(
% 7.15/1.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.15/1.48    inference(cnf_transformation,[],[f29])).
% 7.15/1.48  
% 7.15/1.48  fof(f14,axiom,(
% 7.15/1.48    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.15/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.48  
% 7.15/1.48  fof(f39,plain,(
% 7.15/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.15/1.48    inference(nnf_transformation,[],[f14])).
% 7.15/1.48  
% 7.15/1.48  fof(f40,plain,(
% 7.15/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.15/1.48    inference(rectify,[],[f39])).
% 7.15/1.48  
% 7.15/1.48  fof(f41,plain,(
% 7.15/1.48    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 7.15/1.48    introduced(choice_axiom,[])).
% 7.15/1.48  
% 7.15/1.48  fof(f42,plain,(
% 7.15/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.15/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 7.15/1.48  
% 7.15/1.48  fof(f66,plain,(
% 7.15/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.15/1.48    inference(cnf_transformation,[],[f42])).
% 7.15/1.48  
% 7.15/1.48  fof(f89,plain,(
% 7.15/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.15/1.48    inference(definition_unfolding,[],[f66,f82])).
% 7.15/1.48  
% 7.15/1.48  fof(f97,plain,(
% 7.15/1.48    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 7.15/1.48    inference(equality_resolution,[],[f89])).
% 7.15/1.48  
% 7.15/1.48  fof(f98,plain,(
% 7.15/1.48    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 7.15/1.48    inference(equality_resolution,[],[f97])).
% 7.15/1.48  
% 7.15/1.48  cnf(c_261,plain,
% 7.15/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.15/1.48      theory(equality) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_255,plain,( X0 = X0 ),theory(equality) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_2968,plain,
% 7.15/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.15/1.48      inference(resolution,[status(thm)],[c_261,c_255]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_256,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1716,plain,
% 7.15/1.48      ( X0 != X1 | X1 = X0 ),
% 7.15/1.48      inference(resolution,[status(thm)],[c_256,c_255]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_24,negated_conjecture,
% 7.15/1.48      ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 7.15/1.48      | sK4 != sK5 ),
% 7.15/1.48      inference(cnf_transformation,[],[f96]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_10236,plain,
% 7.15/1.48      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | sK4 != sK5 ),
% 7.15/1.48      inference(resolution,[status(thm)],[c_1716,c_24]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_22,plain,
% 7.15/1.48      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 7.15/1.48      | X1 = X0 ),
% 7.15/1.48      inference(cnf_transformation,[],[f94]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_26,plain,
% 7.15/1.48      ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 7.15/1.48      | sK4 = sK4 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_19,plain,
% 7.15/1.48      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 7.15/1.48      inference(cnf_transformation,[],[f100]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_35,plain,
% 7.15/1.48      ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_19]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_262,plain,
% 7.15/1.48      ( X0 != X1
% 7.15/1.48      | X2 != X3
% 7.15/1.48      | X4 != X5
% 7.15/1.48      | X6 != X7
% 7.15/1.48      | X8 != X9
% 7.15/1.48      | X10 != X11
% 7.15/1.48      | X12 != X13
% 7.15/1.48      | X14 != X15
% 7.15/1.48      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 7.15/1.48      theory(equality) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_267,plain,
% 7.15/1.48      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 7.15/1.48      | sK4 != sK4 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_262]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_922,plain,
% 7.15/1.48      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_256]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_923,plain,
% 7.15/1.48      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_922]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1122,plain,
% 7.15/1.48      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
% 7.15/1.48      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != X0 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_256]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1749,plain,
% 7.15/1.48      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 7.15/1.48      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_1122]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1714,plain,
% 7.15/1.48      ( X0 != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 7.15/1.48      | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = X0
% 7.15/1.48      | sK4 != sK5 ),
% 7.15/1.48      inference(resolution,[status(thm)],[c_256,c_24]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_8,plain,
% 7.15/1.48      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.15/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1725,plain,
% 7.15/1.48      ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | sK4 != sK5
% 7.15/1.48      | k1_xboole_0 != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 7.15/1.48      inference(resolution,[status(thm)],[c_1714,c_8]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_7074,plain,
% 7.15/1.48      ( sK5 = sK4
% 7.15/1.48      | sK4 != sK5
% 7.15/1.48      | k1_xboole_0 != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 7.15/1.48      inference(resolution,[status(thm)],[c_22,c_1725]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_23,negated_conjecture,
% 7.15/1.48      ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 7.15/1.48      | sK4 = sK5 ),
% 7.15/1.48      inference(cnf_transformation,[],[f95]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_920,plain,
% 7.15/1.48      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
% 7.15/1.48      | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != X0
% 7.15/1.48      | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_256]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1038,plain,
% 7.15/1.48      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 7.15/1.48      | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_920]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1039,plain,
% 7.15/1.48      ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_255]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1050,plain,
% 7.15/1.48      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | sK5 = X0 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1052,plain,
% 7.15/1.48      ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | sK5 = sK4 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_1050]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_21,plain,
% 7.15/1.48      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 7.15/1.48      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 7.15/1.48      | k1_xboole_0 = X0 ),
% 7.15/1.48      inference(cnf_transformation,[],[f93]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1116,plain,
% 7.15/1.48      ( ~ r1_tarski(k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 7.15/1.48      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | k1_xboole_0 = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_21]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1117,plain,
% 7.15/1.48      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | k1_xboole_0 = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | r1_tarski(k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 7.15/1.48      inference(predicate_to_equality,[status(thm)],[c_1116]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1056,plain,
% 7.15/1.48      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_256]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1176,plain,
% 7.15/1.48      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_1056]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1178,plain,
% 7.15/1.48      ( sK5 != sK5 | sK5 = sK4 | sK4 != sK5 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_1176]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1177,plain,
% 7.15/1.48      ( sK5 = sK5 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_255]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_11,plain,
% 7.15/1.48      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.15/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1603,plain,
% 7.15/1.48      ( r1_tarski(k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_11]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1604,plain,
% 7.15/1.48      ( r1_tarski(k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.15/1.48      inference(predicate_to_equality,[status(thm)],[c_1603]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1040,plain,
% 7.15/1.48      ( X0 != X1
% 7.15/1.48      | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != X1
% 7.15/1.48      | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = X0 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_256]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1133,plain,
% 7.15/1.48      ( X0 != k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = X0
% 7.15/1.48      | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_1040]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_2196,plain,
% 7.15/1.48      ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k1_xboole_0
% 7.15/1.48      | k1_xboole_0 != k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_1133]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_2401,plain,
% 7.15/1.48      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k1_xboole_0 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_2403,plain,
% 7.15/1.48      ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != k1_xboole_0 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_2401]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_9521,plain,
% 7.15/1.48      ( sK5 = sK4 ),
% 7.15/1.48      inference(global_propositional_subsumption,
% 7.15/1.48                [status(thm)],
% 7.15/1.48                [c_7074,c_23,c_1038,c_1039,c_1052,c_1117,c_1178,c_1177,
% 7.15/1.48                 c_1604,c_2196,c_2403]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_11005,plain,
% 7.15/1.48      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 7.15/1.48      inference(global_propositional_subsumption,
% 7.15/1.48                [status(thm)],
% 7.15/1.48                [c_10236,c_24,c_23,c_26,c_35,c_267,c_923,c_1038,c_1039,
% 7.15/1.48                 c_1052,c_1117,c_1178,c_1177,c_1604,c_1749,c_2196,c_2403]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_11849,plain,
% 7.15/1.48      ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 7.15/1.48      inference(resolution,[status(thm)],[c_11005,c_1716]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_15528,plain,
% 7.15/1.48      ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0)
% 7.15/1.48      | r1_tarski(k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0) ),
% 7.15/1.48      inference(resolution,[status(thm)],[c_2968,c_11849]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1,plain,
% 7.15/1.48      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 7.15/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_13,plain,
% 7.15/1.48      ( ~ r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 7.15/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1223,plain,
% 7.15/1.48      ( ~ r1_tarski(X0,X1)
% 7.15/1.48      | ~ r2_hidden(X2,X0)
% 7.15/1.48      | ~ r2_hidden(X2,k4_xboole_0(X3,X1)) ),
% 7.15/1.48      inference(resolution,[status(thm)],[c_1,c_13]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_259,plain,
% 7.15/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.15/1.48      theory(equality) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_2916,plain,
% 7.15/1.48      ( ~ r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 7.15/1.48      | r2_hidden(X1,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 7.15/1.48      | X1 != X0
% 7.15/1.48      | sK4 != sK5 ),
% 7.15/1.48      inference(resolution,[status(thm)],[c_259,c_24]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_3393,plain,
% 7.15/1.48      ( X1 != X0
% 7.15/1.48      | r2_hidden(X1,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 7.15/1.48      | ~ r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 7.15/1.48      inference(global_propositional_subsumption,
% 7.15/1.48                [status(thm)],
% 7.15/1.48                [c_2916,c_23,c_26,c_35,c_923,c_1038,c_1039,c_1052,c_1117,
% 7.15/1.48                 c_1178,c_1177,c_1604,c_2196,c_2403]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_3394,plain,
% 7.15/1.48      ( ~ r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 7.15/1.48      | r2_hidden(X1,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 7.15/1.48      | X1 != X0 ),
% 7.15/1.48      inference(renaming,[status(thm)],[c_3393]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_17,plain,
% 7.15/1.48      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 7.15/1.48      inference(cnf_transformation,[],[f98]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_3427,plain,
% 7.15/1.48      ( r2_hidden(X0,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 7.15/1.48      | X0 != sK4 ),
% 7.15/1.48      inference(resolution,[status(thm)],[c_3394,c_17]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_22408,plain,
% 7.15/1.48      ( ~ r1_tarski(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | ~ r2_hidden(X1,X0)
% 7.15/1.48      | X1 != sK4 ),
% 7.15/1.48      inference(resolution,[status(thm)],[c_1223,c_3427]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_24919,plain,
% 7.15/1.48      ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | ~ r2_hidden(X0,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 7.15/1.48      | X0 != sK4 ),
% 7.15/1.48      inference(resolution,[status(thm)],[c_15528,c_22408]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_24921,plain,
% 7.15/1.48      ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | ~ r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 7.15/1.48      | sK4 != sK4 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_24919]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_946,plain,
% 7.15/1.48      ( r1_tarski(X0,X1)
% 7.15/1.48      | ~ r1_tarski(k4_xboole_0(X2,X3),X2)
% 7.15/1.48      | X1 != X2
% 7.15/1.48      | X0 != k4_xboole_0(X2,X3) ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_261]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1252,plain,
% 7.15/1.48      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 7.15/1.48      | ~ r1_tarski(k4_xboole_0(X2,X3),X2)
% 7.15/1.48      | X1 != X2
% 7.15/1.48      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k4_xboole_0(X2,X3) ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_946]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_3989,plain,
% 7.15/1.48      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | ~ r1_tarski(k4_xboole_0(X1,X2),X1)
% 7.15/1.48      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k4_xboole_0(X1,X2)
% 7.15/1.48      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != X1 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_1252]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_4689,plain,
% 7.15/1.48      ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.15/1.48      | ~ r1_tarski(k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 7.15/1.48      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 7.15/1.48      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_3989]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_3396,plain,
% 7.15/1.48      ( ~ r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 7.15/1.48      | r2_hidden(sK4,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 7.15/1.48      | sK4 != sK4 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_3394]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1171,plain,
% 7.15/1.48      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
% 7.15/1.48      | sK5 != X0
% 7.15/1.48      | sK5 != X1
% 7.15/1.48      | sK5 != X2
% 7.15/1.48      | sK5 != X3
% 7.15/1.48      | sK5 != X4
% 7.15/1.48      | sK5 != X5
% 7.15/1.48      | sK5 != X6
% 7.15/1.48      | sK5 != X7 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_262]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_1173,plain,
% 7.15/1.48      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 7.15/1.48      | sK5 != sK4 ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_1171]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(c_41,plain,
% 7.15/1.48      ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 7.15/1.48      inference(instantiation,[status(thm)],[c_17]) ).
% 7.15/1.48  
% 7.15/1.48  cnf(contradiction,plain,
% 7.15/1.48      ( $false ),
% 7.15/1.48      inference(minisat,
% 7.15/1.48                [status(thm)],
% 7.15/1.48                [c_24921,c_9521,c_4689,c_3396,c_1749,c_1603,c_1173,c_923,
% 7.15/1.48                 c_267,c_41,c_35,c_26,c_24]) ).
% 7.15/1.48  
% 7.15/1.48  
% 7.15/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.15/1.48  
% 7.15/1.48  ------                               Statistics
% 7.15/1.48  
% 7.15/1.48  ------ Selected
% 7.15/1.48  
% 7.15/1.48  total_time:                             0.585
% 7.15/1.48  
%------------------------------------------------------------------------------
