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
% DateTime   : Thu Dec  3 11:38:33 EST 2020

% Result     : Theorem 8.16s
% Output     : CNFRefutation 8.16s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 286 expanded)
%              Number of clauses        :   52 (  59 expanded)
%              Number of leaves         :   14 (  75 expanded)
%              Depth                    :   13
%              Number of atoms          :  323 (1005 expanded)
%              Number of equality atoms :   84 ( 288 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK2,sK4) != k1_tarski(sK5)
      & r2_hidden(sK5,sK2)
      & k3_xboole_0(sK3,sK4) = k1_tarski(sK5)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k3_xboole_0(sK2,sK4) != k1_tarski(sK5)
    & r2_hidden(sK5,sK2)
    & k3_xboole_0(sK3,sK4) = k1_tarski(sK5)
    & r1_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f23])).

fof(f41,plain,(
    k3_xboole_0(sK3,sK4) = k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f55,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(definition_unfolding,[],[f41,f34,f45])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f43,plain,(
    k3_xboole_0(sK2,sK4) != k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(definition_unfolding,[],[f43,f34,f45])).

fof(f42,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f38,f45])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f50])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f40,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_156,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_964,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(X2,X3,X4),X4)
    | X4 != X1
    | sK1(X2,X3,X4) != X0 ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_2678,plain,
    ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),X0)
    | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | k2_enumset1(sK5,sK5,sK5,sK5) != X0
    | sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_964])).

cnf(c_8367,plain,
    ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | k2_enumset1(sK5,sK5,sK5,sK5) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_2678])).

cnf(c_32645,plain,
    ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))
    | k2_enumset1(sK5,sK5,sK5,sK5) != k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))
    | sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_8367])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1506,plain,
    ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),X0)
    | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k4_xboole_0(X0,k4_xboole_0(X0,sK4)))
    | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4528,plain,
    ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))
    | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK3)
    | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_154,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_153,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_913,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_154,c_153])).

cnf(c_13,negated_conjecture,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3307,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_913,c_13])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_11,negated_conjecture,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2183,plain,
    ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2) ),
    inference(resolution,[status(thm)],[c_5,c_11])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_591,plain,
    ( ~ r2_hidden(sK5,sK2)
    | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_843,plain,
    ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),X0)
    | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
    | ~ r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1476,plain,
    ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
    | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),sK2) ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_1480,plain,
    ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
    | ~ r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK2) ),
    inference(instantiation,[status(thm)],[c_1476])).

cnf(c_2463,plain,
    ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2183,c_12,c_591,c_1480])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2129,plain,
    ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) ),
    inference(resolution,[status(thm)],[c_4,c_11])).

cnf(c_838,plain,
    ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),X0)
    | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4)
    | ~ r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1228,plain,
    ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4)
    | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),sK4) ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_1232,plain,
    ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4)
    | ~ r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_1228])).

cnf(c_1230,plain,
    ( ~ r2_hidden(X0,sK4)
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1236,plain,
    ( ~ r2_hidden(sK5,sK4)
    | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_1230])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_470,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_471,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_789,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_470,c_471])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_461,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_725,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_461])).

cnf(c_1586,plain,
    ( r2_hidden(sK5,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_789,c_725])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_464,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1782,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1586,c_464])).

cnf(c_1788,plain,
    ( r2_hidden(sK5,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1782])).

cnf(c_2351,plain,
    ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2129,c_1232,c_1236,c_1788])).

cnf(c_669,plain,
    ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),X0)
    | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
    | ~ r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2051,plain,
    ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK3)
    | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
    | ~ r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_1619,plain,
    ( sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) = sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_776,plain,
    ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4)
    | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32645,c_4528,c_3307,c_2463,c_2351,c_2051,c_1619,c_776,c_11,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n017.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 11:48:01 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 8.16/1.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.16/1.47  
% 8.16/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.16/1.47  
% 8.16/1.47  ------  iProver source info
% 8.16/1.47  
% 8.16/1.47  git: date: 2020-06-30 10:37:57 +0100
% 8.16/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.16/1.47  git: non_committed_changes: false
% 8.16/1.47  git: last_make_outside_of_git: false
% 8.16/1.47  
% 8.16/1.47  ------ 
% 8.16/1.47  
% 8.16/1.47  ------ Input Options
% 8.16/1.47  
% 8.16/1.47  --out_options                           all
% 8.16/1.47  --tptp_safe_out                         true
% 8.16/1.47  --problem_path                          ""
% 8.16/1.47  --include_path                          ""
% 8.16/1.47  --clausifier                            res/vclausify_rel
% 8.16/1.47  --clausifier_options                    --mode clausify
% 8.16/1.47  --stdin                                 false
% 8.16/1.47  --stats_out                             sel
% 8.16/1.47  
% 8.16/1.47  ------ General Options
% 8.16/1.47  
% 8.16/1.47  --fof                                   false
% 8.16/1.47  --time_out_real                         604.99
% 8.16/1.47  --time_out_virtual                      -1.
% 8.16/1.47  --symbol_type_check                     false
% 8.16/1.47  --clausify_out                          false
% 8.16/1.47  --sig_cnt_out                           false
% 8.16/1.47  --trig_cnt_out                          false
% 8.16/1.47  --trig_cnt_out_tolerance                1.
% 8.16/1.47  --trig_cnt_out_sk_spl                   false
% 8.16/1.47  --abstr_cl_out                          false
% 8.16/1.47  
% 8.16/1.47  ------ Global Options
% 8.16/1.47  
% 8.16/1.47  --schedule                              none
% 8.16/1.47  --add_important_lit                     false
% 8.16/1.47  --prop_solver_per_cl                    1000
% 8.16/1.47  --min_unsat_core                        false
% 8.16/1.47  --soft_assumptions                      false
% 8.16/1.47  --soft_lemma_size                       3
% 8.16/1.47  --prop_impl_unit_size                   0
% 8.16/1.47  --prop_impl_unit                        []
% 8.16/1.47  --share_sel_clauses                     true
% 8.16/1.47  --reset_solvers                         false
% 8.16/1.47  --bc_imp_inh                            [conj_cone]
% 8.16/1.47  --conj_cone_tolerance                   3.
% 8.16/1.47  --extra_neg_conj                        none
% 8.16/1.47  --large_theory_mode                     true
% 8.16/1.47  --prolific_symb_bound                   200
% 8.16/1.47  --lt_threshold                          2000
% 8.16/1.47  --clause_weak_htbl                      true
% 8.16/1.47  --gc_record_bc_elim                     false
% 8.16/1.47  
% 8.16/1.47  ------ Preprocessing Options
% 8.16/1.47  
% 8.16/1.47  --preprocessing_flag                    true
% 8.16/1.47  --time_out_prep_mult                    0.1
% 8.16/1.47  --splitting_mode                        input
% 8.16/1.47  --splitting_grd                         true
% 8.16/1.47  --splitting_cvd                         false
% 8.16/1.47  --splitting_cvd_svl                     false
% 8.16/1.47  --splitting_nvd                         32
% 8.16/1.47  --sub_typing                            true
% 8.16/1.47  --prep_gs_sim                           false
% 8.16/1.47  --prep_unflatten                        true
% 8.16/1.47  --prep_res_sim                          true
% 8.16/1.47  --prep_upred                            true
% 8.16/1.47  --prep_sem_filter                       exhaustive
% 8.16/1.47  --prep_sem_filter_out                   false
% 8.16/1.47  --pred_elim                             false
% 8.16/1.47  --res_sim_input                         true
% 8.16/1.47  --eq_ax_congr_red                       true
% 8.16/1.47  --pure_diseq_elim                       true
% 8.16/1.47  --brand_transform                       false
% 8.16/1.47  --non_eq_to_eq                          false
% 8.16/1.47  --prep_def_merge                        true
% 8.16/1.47  --prep_def_merge_prop_impl              false
% 8.16/1.47  --prep_def_merge_mbd                    true
% 8.16/1.47  --prep_def_merge_tr_red                 false
% 8.16/1.47  --prep_def_merge_tr_cl                  false
% 8.16/1.47  --smt_preprocessing                     true
% 8.16/1.47  --smt_ac_axioms                         fast
% 8.16/1.47  --preprocessed_out                      false
% 8.16/1.47  --preprocessed_stats                    false
% 8.16/1.47  
% 8.16/1.47  ------ Abstraction refinement Options
% 8.16/1.47  
% 8.16/1.47  --abstr_ref                             []
% 8.16/1.47  --abstr_ref_prep                        false
% 8.16/1.47  --abstr_ref_until_sat                   false
% 8.16/1.47  --abstr_ref_sig_restrict                funpre
% 8.16/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 8.16/1.47  --abstr_ref_under                       []
% 8.16/1.47  
% 8.16/1.47  ------ SAT Options
% 8.16/1.47  
% 8.16/1.47  --sat_mode                              false
% 8.16/1.47  --sat_fm_restart_options                ""
% 8.16/1.47  --sat_gr_def                            false
% 8.16/1.47  --sat_epr_types                         true
% 8.16/1.47  --sat_non_cyclic_types                  false
% 8.16/1.47  --sat_finite_models                     false
% 8.16/1.47  --sat_fm_lemmas                         false
% 8.16/1.47  --sat_fm_prep                           false
% 8.16/1.47  --sat_fm_uc_incr                        true
% 8.16/1.47  --sat_out_model                         small
% 8.16/1.47  --sat_out_clauses                       false
% 8.16/1.47  
% 8.16/1.47  ------ QBF Options
% 8.16/1.47  
% 8.16/1.47  --qbf_mode                              false
% 8.16/1.47  --qbf_elim_univ                         false
% 8.16/1.47  --qbf_dom_inst                          none
% 8.16/1.47  --qbf_dom_pre_inst                      false
% 8.16/1.47  --qbf_sk_in                             false
% 8.16/1.47  --qbf_pred_elim                         true
% 8.16/1.47  --qbf_split                             512
% 8.16/1.47  
% 8.16/1.47  ------ BMC1 Options
% 8.16/1.47  
% 8.16/1.47  --bmc1_incremental                      false
% 8.16/1.47  --bmc1_axioms                           reachable_all
% 8.16/1.47  --bmc1_min_bound                        0
% 8.16/1.47  --bmc1_max_bound                        -1
% 8.16/1.47  --bmc1_max_bound_default                -1
% 8.16/1.47  --bmc1_symbol_reachability              true
% 8.16/1.47  --bmc1_property_lemmas                  false
% 8.16/1.47  --bmc1_k_induction                      false
% 8.16/1.47  --bmc1_non_equiv_states                 false
% 8.16/1.47  --bmc1_deadlock                         false
% 8.16/1.47  --bmc1_ucm                              false
% 8.16/1.47  --bmc1_add_unsat_core                   none
% 8.16/1.47  --bmc1_unsat_core_children              false
% 8.16/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 8.16/1.47  --bmc1_out_stat                         full
% 8.16/1.47  --bmc1_ground_init                      false
% 8.16/1.47  --bmc1_pre_inst_next_state              false
% 8.16/1.47  --bmc1_pre_inst_state                   false
% 8.16/1.47  --bmc1_pre_inst_reach_state             false
% 8.16/1.47  --bmc1_out_unsat_core                   false
% 8.16/1.47  --bmc1_aig_witness_out                  false
% 8.16/1.47  --bmc1_verbose                          false
% 8.16/1.47  --bmc1_dump_clauses_tptp                false
% 8.16/1.47  --bmc1_dump_unsat_core_tptp             false
% 8.16/1.47  --bmc1_dump_file                        -
% 8.16/1.47  --bmc1_ucm_expand_uc_limit              128
% 8.16/1.47  --bmc1_ucm_n_expand_iterations          6
% 8.16/1.47  --bmc1_ucm_extend_mode                  1
% 8.16/1.47  --bmc1_ucm_init_mode                    2
% 8.16/1.47  --bmc1_ucm_cone_mode                    none
% 8.16/1.47  --bmc1_ucm_reduced_relation_type        0
% 8.16/1.47  --bmc1_ucm_relax_model                  4
% 8.16/1.47  --bmc1_ucm_full_tr_after_sat            true
% 8.16/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 8.16/1.47  --bmc1_ucm_layered_model                none
% 8.16/1.47  --bmc1_ucm_max_lemma_size               10
% 8.16/1.47  
% 8.16/1.47  ------ AIG Options
% 8.16/1.47  
% 8.16/1.47  --aig_mode                              false
% 8.16/1.47  
% 8.16/1.47  ------ Instantiation Options
% 8.16/1.47  
% 8.16/1.47  --instantiation_flag                    true
% 8.16/1.47  --inst_sos_flag                         false
% 8.16/1.47  --inst_sos_phase                        true
% 8.16/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.16/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.16/1.47  --inst_lit_sel_side                     num_symb
% 8.16/1.47  --inst_solver_per_active                1400
% 8.16/1.47  --inst_solver_calls_frac                1.
% 8.16/1.47  --inst_passive_queue_type               priority_queues
% 8.16/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.16/1.47  --inst_passive_queues_freq              [25;2]
% 8.16/1.47  --inst_dismatching                      true
% 8.16/1.47  --inst_eager_unprocessed_to_passive     true
% 8.16/1.47  --inst_prop_sim_given                   true
% 8.16/1.47  --inst_prop_sim_new                     false
% 8.16/1.47  --inst_subs_new                         false
% 8.16/1.47  --inst_eq_res_simp                      false
% 8.16/1.47  --inst_subs_given                       false
% 8.16/1.47  --inst_orphan_elimination               true
% 8.16/1.47  --inst_learning_loop_flag               true
% 8.16/1.47  --inst_learning_start                   3000
% 8.16/1.47  --inst_learning_factor                  2
% 8.16/1.47  --inst_start_prop_sim_after_learn       3
% 8.16/1.47  --inst_sel_renew                        solver
% 8.16/1.47  --inst_lit_activity_flag                true
% 8.16/1.47  --inst_restr_to_given                   false
% 8.16/1.47  --inst_activity_threshold               500
% 8.16/1.47  --inst_out_proof                        true
% 8.16/1.47  
% 8.16/1.47  ------ Resolution Options
% 8.16/1.47  
% 8.16/1.47  --resolution_flag                       true
% 8.16/1.47  --res_lit_sel                           adaptive
% 8.16/1.47  --res_lit_sel_side                      none
% 8.16/1.47  --res_ordering                          kbo
% 8.16/1.47  --res_to_prop_solver                    active
% 8.16/1.47  --res_prop_simpl_new                    false
% 8.16/1.47  --res_prop_simpl_given                  true
% 8.16/1.47  --res_passive_queue_type                priority_queues
% 8.16/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.16/1.47  --res_passive_queues_freq               [15;5]
% 8.16/1.47  --res_forward_subs                      full
% 8.16/1.47  --res_backward_subs                     full
% 8.16/1.47  --res_forward_subs_resolution           true
% 8.16/1.47  --res_backward_subs_resolution          true
% 8.16/1.47  --res_orphan_elimination                true
% 8.16/1.47  --res_time_limit                        2.
% 8.16/1.47  --res_out_proof                         true
% 8.16/1.47  
% 8.16/1.47  ------ Superposition Options
% 8.16/1.47  
% 8.16/1.47  --superposition_flag                    true
% 8.16/1.47  --sup_passive_queue_type                priority_queues
% 8.16/1.47  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.16/1.47  --sup_passive_queues_freq               [1;4]
% 8.16/1.47  --demod_completeness_check              fast
% 8.16/1.47  --demod_use_ground                      true
% 8.16/1.47  --sup_to_prop_solver                    passive
% 8.16/1.47  --sup_prop_simpl_new                    true
% 8.16/1.47  --sup_prop_simpl_given                  true
% 8.16/1.47  --sup_fun_splitting                     false
% 8.16/1.47  --sup_smt_interval                      50000
% 8.16/1.47  
% 8.16/1.47  ------ Superposition Simplification Setup
% 8.16/1.47  
% 8.16/1.47  --sup_indices_passive                   []
% 8.16/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.16/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.16/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.16/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 8.16/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.16/1.47  --sup_full_bw                           [BwDemod]
% 8.16/1.47  --sup_immed_triv                        [TrivRules]
% 8.16/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.16/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.16/1.47  --sup_immed_bw_main                     []
% 8.16/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.16/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 8.16/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.16/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.16/1.47  
% 8.16/1.47  ------ Combination Options
% 8.16/1.47  
% 8.16/1.47  --comb_res_mult                         3
% 8.16/1.47  --comb_sup_mult                         2
% 8.16/1.47  --comb_inst_mult                        10
% 8.16/1.47  
% 8.16/1.47  ------ Debug Options
% 8.16/1.47  
% 8.16/1.47  --dbg_backtrace                         false
% 8.16/1.47  --dbg_dump_prop_clauses                 false
% 8.16/1.47  --dbg_dump_prop_clauses_file            -
% 8.16/1.47  --dbg_out_stat                          false
% 8.16/1.47  ------ Parsing...
% 8.16/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.16/1.47  
% 8.16/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 8.16/1.47  
% 8.16/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.16/1.47  
% 8.16/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.16/1.47  ------ Proving...
% 8.16/1.47  ------ Problem Properties 
% 8.16/1.47  
% 8.16/1.47  
% 8.16/1.47  clauses                                 15
% 8.16/1.47  conjectures                             4
% 8.16/1.47  EPR                                     3
% 8.16/1.47  Horn                                    12
% 8.16/1.47  unary                                   4
% 8.16/1.47  binary                                  6
% 8.16/1.47  lits                                    32
% 8.16/1.47  lits eq                                 5
% 8.16/1.47  fd_pure                                 0
% 8.16/1.47  fd_pseudo                               0
% 8.16/1.47  fd_cond                                 0
% 8.16/1.47  fd_pseudo_cond                          3
% 8.16/1.47  AC symbols                              0
% 8.16/1.47  
% 8.16/1.47  ------ Input Options Time Limit: Unbounded
% 8.16/1.47  
% 8.16/1.47  
% 8.16/1.47  ------ 
% 8.16/1.47  Current options:
% 8.16/1.47  ------ 
% 8.16/1.47  
% 8.16/1.47  ------ Input Options
% 8.16/1.47  
% 8.16/1.47  --out_options                           all
% 8.16/1.47  --tptp_safe_out                         true
% 8.16/1.47  --problem_path                          ""
% 8.16/1.47  --include_path                          ""
% 8.16/1.47  --clausifier                            res/vclausify_rel
% 8.16/1.47  --clausifier_options                    --mode clausify
% 8.16/1.47  --stdin                                 false
% 8.16/1.47  --stats_out                             sel
% 8.16/1.47  
% 8.16/1.47  ------ General Options
% 8.16/1.47  
% 8.16/1.47  --fof                                   false
% 8.16/1.47  --time_out_real                         604.99
% 8.16/1.47  --time_out_virtual                      -1.
% 8.16/1.47  --symbol_type_check                     false
% 8.16/1.47  --clausify_out                          false
% 8.16/1.47  --sig_cnt_out                           false
% 8.16/1.47  --trig_cnt_out                          false
% 8.16/1.47  --trig_cnt_out_tolerance                1.
% 8.16/1.47  --trig_cnt_out_sk_spl                   false
% 8.16/1.47  --abstr_cl_out                          false
% 8.16/1.47  
% 8.16/1.47  ------ Global Options
% 8.16/1.47  
% 8.16/1.47  --schedule                              none
% 8.16/1.47  --add_important_lit                     false
% 8.16/1.47  --prop_solver_per_cl                    1000
% 8.16/1.47  --min_unsat_core                        false
% 8.16/1.47  --soft_assumptions                      false
% 8.16/1.47  --soft_lemma_size                       3
% 8.16/1.47  --prop_impl_unit_size                   0
% 8.16/1.47  --prop_impl_unit                        []
% 8.16/1.47  --share_sel_clauses                     true
% 8.16/1.47  --reset_solvers                         false
% 8.16/1.47  --bc_imp_inh                            [conj_cone]
% 8.16/1.47  --conj_cone_tolerance                   3.
% 8.16/1.47  --extra_neg_conj                        none
% 8.16/1.47  --large_theory_mode                     true
% 8.16/1.47  --prolific_symb_bound                   200
% 8.16/1.47  --lt_threshold                          2000
% 8.16/1.47  --clause_weak_htbl                      true
% 8.16/1.47  --gc_record_bc_elim                     false
% 8.16/1.47  
% 8.16/1.47  ------ Preprocessing Options
% 8.16/1.47  
% 8.16/1.47  --preprocessing_flag                    true
% 8.16/1.47  --time_out_prep_mult                    0.1
% 8.16/1.47  --splitting_mode                        input
% 8.16/1.47  --splitting_grd                         true
% 8.16/1.47  --splitting_cvd                         false
% 8.16/1.47  --splitting_cvd_svl                     false
% 8.16/1.47  --splitting_nvd                         32
% 8.16/1.47  --sub_typing                            true
% 8.16/1.47  --prep_gs_sim                           false
% 8.16/1.47  --prep_unflatten                        true
% 8.16/1.47  --prep_res_sim                          true
% 8.16/1.47  --prep_upred                            true
% 8.16/1.47  --prep_sem_filter                       exhaustive
% 8.16/1.47  --prep_sem_filter_out                   false
% 8.16/1.47  --pred_elim                             false
% 8.16/1.47  --res_sim_input                         true
% 8.16/1.47  --eq_ax_congr_red                       true
% 8.16/1.47  --pure_diseq_elim                       true
% 8.16/1.47  --brand_transform                       false
% 8.16/1.47  --non_eq_to_eq                          false
% 8.16/1.47  --prep_def_merge                        true
% 8.16/1.47  --prep_def_merge_prop_impl              false
% 8.16/1.47  --prep_def_merge_mbd                    true
% 8.16/1.47  --prep_def_merge_tr_red                 false
% 8.16/1.47  --prep_def_merge_tr_cl                  false
% 8.16/1.47  --smt_preprocessing                     true
% 8.16/1.47  --smt_ac_axioms                         fast
% 8.16/1.47  --preprocessed_out                      false
% 8.16/1.47  --preprocessed_stats                    false
% 8.16/1.47  
% 8.16/1.47  ------ Abstraction refinement Options
% 8.16/1.47  
% 8.16/1.47  --abstr_ref                             []
% 8.16/1.47  --abstr_ref_prep                        false
% 8.16/1.47  --abstr_ref_until_sat                   false
% 8.16/1.47  --abstr_ref_sig_restrict                funpre
% 8.16/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 8.16/1.47  --abstr_ref_under                       []
% 8.16/1.47  
% 8.16/1.47  ------ SAT Options
% 8.16/1.47  
% 8.16/1.47  --sat_mode                              false
% 8.16/1.47  --sat_fm_restart_options                ""
% 8.16/1.47  --sat_gr_def                            false
% 8.16/1.47  --sat_epr_types                         true
% 8.16/1.47  --sat_non_cyclic_types                  false
% 8.16/1.47  --sat_finite_models                     false
% 8.16/1.47  --sat_fm_lemmas                         false
% 8.16/1.47  --sat_fm_prep                           false
% 8.16/1.47  --sat_fm_uc_incr                        true
% 8.16/1.47  --sat_out_model                         small
% 8.16/1.47  --sat_out_clauses                       false
% 8.16/1.47  
% 8.16/1.47  ------ QBF Options
% 8.16/1.47  
% 8.16/1.47  --qbf_mode                              false
% 8.16/1.47  --qbf_elim_univ                         false
% 8.16/1.47  --qbf_dom_inst                          none
% 8.16/1.47  --qbf_dom_pre_inst                      false
% 8.16/1.47  --qbf_sk_in                             false
% 8.16/1.47  --qbf_pred_elim                         true
% 8.16/1.47  --qbf_split                             512
% 8.16/1.47  
% 8.16/1.47  ------ BMC1 Options
% 8.16/1.47  
% 8.16/1.47  --bmc1_incremental                      false
% 8.16/1.47  --bmc1_axioms                           reachable_all
% 8.16/1.47  --bmc1_min_bound                        0
% 8.16/1.47  --bmc1_max_bound                        -1
% 8.16/1.47  --bmc1_max_bound_default                -1
% 8.16/1.47  --bmc1_symbol_reachability              true
% 8.16/1.47  --bmc1_property_lemmas                  false
% 8.16/1.47  --bmc1_k_induction                      false
% 8.16/1.47  --bmc1_non_equiv_states                 false
% 8.16/1.47  --bmc1_deadlock                         false
% 8.16/1.47  --bmc1_ucm                              false
% 8.16/1.47  --bmc1_add_unsat_core                   none
% 8.16/1.47  --bmc1_unsat_core_children              false
% 8.16/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 8.16/1.47  --bmc1_out_stat                         full
% 8.16/1.47  --bmc1_ground_init                      false
% 8.16/1.47  --bmc1_pre_inst_next_state              false
% 8.16/1.47  --bmc1_pre_inst_state                   false
% 8.16/1.47  --bmc1_pre_inst_reach_state             false
% 8.16/1.47  --bmc1_out_unsat_core                   false
% 8.16/1.47  --bmc1_aig_witness_out                  false
% 8.16/1.47  --bmc1_verbose                          false
% 8.16/1.47  --bmc1_dump_clauses_tptp                false
% 8.16/1.47  --bmc1_dump_unsat_core_tptp             false
% 8.16/1.47  --bmc1_dump_file                        -
% 8.16/1.47  --bmc1_ucm_expand_uc_limit              128
% 8.16/1.47  --bmc1_ucm_n_expand_iterations          6
% 8.16/1.47  --bmc1_ucm_extend_mode                  1
% 8.16/1.47  --bmc1_ucm_init_mode                    2
% 8.16/1.47  --bmc1_ucm_cone_mode                    none
% 8.16/1.47  --bmc1_ucm_reduced_relation_type        0
% 8.16/1.47  --bmc1_ucm_relax_model                  4
% 8.16/1.47  --bmc1_ucm_full_tr_after_sat            true
% 8.16/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 8.16/1.47  --bmc1_ucm_layered_model                none
% 8.16/1.47  --bmc1_ucm_max_lemma_size               10
% 8.16/1.47  
% 8.16/1.47  ------ AIG Options
% 8.16/1.47  
% 8.16/1.47  --aig_mode                              false
% 8.16/1.47  
% 8.16/1.47  ------ Instantiation Options
% 8.16/1.47  
% 8.16/1.47  --instantiation_flag                    true
% 8.16/1.47  --inst_sos_flag                         false
% 8.16/1.47  --inst_sos_phase                        true
% 8.16/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.16/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.16/1.47  --inst_lit_sel_side                     num_symb
% 8.16/1.47  --inst_solver_per_active                1400
% 8.16/1.47  --inst_solver_calls_frac                1.
% 8.16/1.47  --inst_passive_queue_type               priority_queues
% 8.16/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.16/1.47  --inst_passive_queues_freq              [25;2]
% 8.16/1.47  --inst_dismatching                      true
% 8.16/1.47  --inst_eager_unprocessed_to_passive     true
% 8.16/1.47  --inst_prop_sim_given                   true
% 8.16/1.47  --inst_prop_sim_new                     false
% 8.16/1.47  --inst_subs_new                         false
% 8.16/1.47  --inst_eq_res_simp                      false
% 8.16/1.47  --inst_subs_given                       false
% 8.16/1.47  --inst_orphan_elimination               true
% 8.16/1.47  --inst_learning_loop_flag               true
% 8.16/1.47  --inst_learning_start                   3000
% 8.16/1.47  --inst_learning_factor                  2
% 8.16/1.47  --inst_start_prop_sim_after_learn       3
% 8.16/1.47  --inst_sel_renew                        solver
% 8.16/1.47  --inst_lit_activity_flag                true
% 8.16/1.47  --inst_restr_to_given                   false
% 8.16/1.47  --inst_activity_threshold               500
% 8.16/1.47  --inst_out_proof                        true
% 8.16/1.47  
% 8.16/1.47  ------ Resolution Options
% 8.16/1.47  
% 8.16/1.47  --resolution_flag                       true
% 8.16/1.47  --res_lit_sel                           adaptive
% 8.16/1.47  --res_lit_sel_side                      none
% 8.16/1.47  --res_ordering                          kbo
% 8.16/1.47  --res_to_prop_solver                    active
% 8.16/1.47  --res_prop_simpl_new                    false
% 8.16/1.47  --res_prop_simpl_given                  true
% 8.16/1.47  --res_passive_queue_type                priority_queues
% 8.16/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.16/1.47  --res_passive_queues_freq               [15;5]
% 8.16/1.47  --res_forward_subs                      full
% 8.16/1.47  --res_backward_subs                     full
% 8.16/1.47  --res_forward_subs_resolution           true
% 8.16/1.47  --res_backward_subs_resolution          true
% 8.16/1.47  --res_orphan_elimination                true
% 8.16/1.47  --res_time_limit                        2.
% 8.16/1.47  --res_out_proof                         true
% 8.16/1.47  
% 8.16/1.47  ------ Superposition Options
% 8.16/1.47  
% 8.16/1.47  --superposition_flag                    true
% 8.16/1.47  --sup_passive_queue_type                priority_queues
% 8.16/1.47  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.16/1.47  --sup_passive_queues_freq               [1;4]
% 8.16/1.47  --demod_completeness_check              fast
% 8.16/1.47  --demod_use_ground                      true
% 8.16/1.47  --sup_to_prop_solver                    passive
% 8.16/1.47  --sup_prop_simpl_new                    true
% 8.16/1.47  --sup_prop_simpl_given                  true
% 8.16/1.47  --sup_fun_splitting                     false
% 8.16/1.47  --sup_smt_interval                      50000
% 8.16/1.47  
% 8.16/1.47  ------ Superposition Simplification Setup
% 8.16/1.47  
% 8.16/1.47  --sup_indices_passive                   []
% 8.16/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.16/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.16/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.16/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 8.16/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.16/1.47  --sup_full_bw                           [BwDemod]
% 8.16/1.47  --sup_immed_triv                        [TrivRules]
% 8.16/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.16/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.16/1.47  --sup_immed_bw_main                     []
% 8.16/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.16/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 8.16/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.16/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.16/1.47  
% 8.16/1.47  ------ Combination Options
% 8.16/1.47  
% 8.16/1.47  --comb_res_mult                         3
% 8.16/1.47  --comb_sup_mult                         2
% 8.16/1.47  --comb_inst_mult                        10
% 8.16/1.47  
% 8.16/1.47  ------ Debug Options
% 8.16/1.47  
% 8.16/1.47  --dbg_backtrace                         false
% 8.16/1.47  --dbg_dump_prop_clauses                 false
% 8.16/1.47  --dbg_dump_prop_clauses_file            -
% 8.16/1.47  --dbg_out_stat                          false
% 8.16/1.47  
% 8.16/1.47  
% 8.16/1.47  
% 8.16/1.47  
% 8.16/1.47  ------ Proving...
% 8.16/1.47  
% 8.16/1.47  
% 8.16/1.47  % SZS status Theorem for theBenchmark.p
% 8.16/1.47  
% 8.16/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 8.16/1.47  
% 8.16/1.47  fof(f2,axiom,(
% 8.16/1.47    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 8.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.16/1.47  
% 8.16/1.47  fof(f17,plain,(
% 8.16/1.47    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 8.16/1.47    inference(nnf_transformation,[],[f2])).
% 8.16/1.47  
% 8.16/1.47  fof(f18,plain,(
% 8.16/1.47    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 8.16/1.47    inference(flattening,[],[f17])).
% 8.16/1.47  
% 8.16/1.47  fof(f19,plain,(
% 8.16/1.47    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 8.16/1.47    inference(rectify,[],[f18])).
% 8.16/1.47  
% 8.16/1.47  fof(f20,plain,(
% 8.16/1.47    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 8.16/1.47    introduced(choice_axiom,[])).
% 8.16/1.47  
% 8.16/1.47  fof(f21,plain,(
% 8.16/1.47    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 8.16/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 8.16/1.47  
% 8.16/1.47  fof(f30,plain,(
% 8.16/1.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 8.16/1.47    inference(cnf_transformation,[],[f21])).
% 8.16/1.47  
% 8.16/1.47  fof(f3,axiom,(
% 8.16/1.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 8.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.16/1.47  
% 8.16/1.47  fof(f34,plain,(
% 8.16/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.16/1.47    inference(cnf_transformation,[],[f3])).
% 8.16/1.47  
% 8.16/1.47  fof(f49,plain,(
% 8.16/1.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 8.16/1.47    inference(definition_unfolding,[],[f30,f34])).
% 8.16/1.47  
% 8.16/1.47  fof(f56,plain,(
% 8.16/1.47    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 8.16/1.47    inference(equality_resolution,[],[f49])).
% 8.16/1.47  
% 8.16/1.47  fof(f8,conjecture,(
% 8.16/1.47    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 8.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.16/1.47  
% 8.16/1.47  fof(f9,negated_conjecture,(
% 8.16/1.47    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 8.16/1.47    inference(negated_conjecture,[],[f8])).
% 8.16/1.47  
% 8.16/1.47  fof(f11,plain,(
% 8.16/1.47    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 8.16/1.47    inference(ennf_transformation,[],[f9])).
% 8.16/1.47  
% 8.16/1.47  fof(f12,plain,(
% 8.16/1.47    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 8.16/1.47    inference(flattening,[],[f11])).
% 8.16/1.47  
% 8.16/1.47  fof(f23,plain,(
% 8.16/1.47    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK2,sK4) != k1_tarski(sK5) & r2_hidden(sK5,sK2) & k3_xboole_0(sK3,sK4) = k1_tarski(sK5) & r1_tarski(sK2,sK3))),
% 8.16/1.47    introduced(choice_axiom,[])).
% 8.16/1.47  
% 8.16/1.47  fof(f24,plain,(
% 8.16/1.47    k3_xboole_0(sK2,sK4) != k1_tarski(sK5) & r2_hidden(sK5,sK2) & k3_xboole_0(sK3,sK4) = k1_tarski(sK5) & r1_tarski(sK2,sK3)),
% 8.16/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f23])).
% 8.16/1.47  
% 8.16/1.47  fof(f41,plain,(
% 8.16/1.47    k3_xboole_0(sK3,sK4) = k1_tarski(sK5)),
% 8.16/1.47    inference(cnf_transformation,[],[f24])).
% 8.16/1.47  
% 8.16/1.47  fof(f4,axiom,(
% 8.16/1.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 8.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.16/1.47  
% 8.16/1.47  fof(f35,plain,(
% 8.16/1.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 8.16/1.47    inference(cnf_transformation,[],[f4])).
% 8.16/1.47  
% 8.16/1.47  fof(f5,axiom,(
% 8.16/1.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 8.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.16/1.47  
% 8.16/1.47  fof(f36,plain,(
% 8.16/1.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 8.16/1.47    inference(cnf_transformation,[],[f5])).
% 8.16/1.47  
% 8.16/1.47  fof(f6,axiom,(
% 8.16/1.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 8.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.16/1.47  
% 8.16/1.47  fof(f37,plain,(
% 8.16/1.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 8.16/1.47    inference(cnf_transformation,[],[f6])).
% 8.16/1.47  
% 8.16/1.47  fof(f44,plain,(
% 8.16/1.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 8.16/1.47    inference(definition_unfolding,[],[f36,f37])).
% 8.16/1.47  
% 8.16/1.47  fof(f45,plain,(
% 8.16/1.47    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 8.16/1.47    inference(definition_unfolding,[],[f35,f44])).
% 8.16/1.47  
% 8.16/1.47  fof(f55,plain,(
% 8.16/1.47    k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5)),
% 8.16/1.47    inference(definition_unfolding,[],[f41,f34,f45])).
% 8.16/1.47  
% 8.16/1.47  fof(f31,plain,(
% 8.16/1.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 8.16/1.47    inference(cnf_transformation,[],[f21])).
% 8.16/1.47  
% 8.16/1.47  fof(f48,plain,(
% 8.16/1.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 8.16/1.47    inference(definition_unfolding,[],[f31,f34])).
% 8.16/1.47  
% 8.16/1.47  fof(f43,plain,(
% 8.16/1.47    k3_xboole_0(sK2,sK4) != k1_tarski(sK5)),
% 8.16/1.47    inference(cnf_transformation,[],[f24])).
% 8.16/1.47  
% 8.16/1.47  fof(f54,plain,(
% 8.16/1.47    k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k2_enumset1(sK5,sK5,sK5,sK5)),
% 8.16/1.47    inference(definition_unfolding,[],[f43,f34,f45])).
% 8.16/1.47  
% 8.16/1.47  fof(f42,plain,(
% 8.16/1.47    r2_hidden(sK5,sK2)),
% 8.16/1.47    inference(cnf_transformation,[],[f24])).
% 8.16/1.47  
% 8.16/1.47  fof(f7,axiom,(
% 8.16/1.47    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 8.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.16/1.47  
% 8.16/1.47  fof(f22,plain,(
% 8.16/1.47    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 8.16/1.47    inference(nnf_transformation,[],[f7])).
% 8.16/1.47  
% 8.16/1.47  fof(f39,plain,(
% 8.16/1.47    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 8.16/1.47    inference(cnf_transformation,[],[f22])).
% 8.16/1.47  
% 8.16/1.47  fof(f52,plain,(
% 8.16/1.47    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 8.16/1.47    inference(definition_unfolding,[],[f39,f45])).
% 8.16/1.47  
% 8.16/1.47  fof(f1,axiom,(
% 8.16/1.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 8.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.16/1.47  
% 8.16/1.47  fof(f10,plain,(
% 8.16/1.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 8.16/1.47    inference(ennf_transformation,[],[f1])).
% 8.16/1.47  
% 8.16/1.47  fof(f13,plain,(
% 8.16/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 8.16/1.48    inference(nnf_transformation,[],[f10])).
% 8.16/1.48  
% 8.16/1.48  fof(f14,plain,(
% 8.16/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.16/1.48    inference(rectify,[],[f13])).
% 8.16/1.48  
% 8.16/1.48  fof(f15,plain,(
% 8.16/1.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 8.16/1.48    introduced(choice_axiom,[])).
% 8.16/1.48  
% 8.16/1.48  fof(f16,plain,(
% 8.16/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.16/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 8.16/1.48  
% 8.16/1.48  fof(f25,plain,(
% 8.16/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 8.16/1.48    inference(cnf_transformation,[],[f16])).
% 8.16/1.48  
% 8.16/1.48  fof(f32,plain,(
% 8.16/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 8.16/1.48    inference(cnf_transformation,[],[f21])).
% 8.16/1.48  
% 8.16/1.48  fof(f47,plain,(
% 8.16/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 8.16/1.48    inference(definition_unfolding,[],[f32,f34])).
% 8.16/1.48  
% 8.16/1.48  fof(f26,plain,(
% 8.16/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 8.16/1.48    inference(cnf_transformation,[],[f16])).
% 8.16/1.48  
% 8.16/1.48  fof(f27,plain,(
% 8.16/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 8.16/1.48    inference(cnf_transformation,[],[f16])).
% 8.16/1.48  
% 8.16/1.48  fof(f38,plain,(
% 8.16/1.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 8.16/1.48    inference(cnf_transformation,[],[f22])).
% 8.16/1.48  
% 8.16/1.48  fof(f53,plain,(
% 8.16/1.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 8.16/1.48    inference(definition_unfolding,[],[f38,f45])).
% 8.16/1.48  
% 8.16/1.48  fof(f29,plain,(
% 8.16/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 8.16/1.48    inference(cnf_transformation,[],[f21])).
% 8.16/1.48  
% 8.16/1.48  fof(f50,plain,(
% 8.16/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 8.16/1.48    inference(definition_unfolding,[],[f29,f34])).
% 8.16/1.48  
% 8.16/1.48  fof(f57,plain,(
% 8.16/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 8.16/1.48    inference(equality_resolution,[],[f50])).
% 8.16/1.48  
% 8.16/1.48  fof(f33,plain,(
% 8.16/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 8.16/1.48    inference(cnf_transformation,[],[f21])).
% 8.16/1.48  
% 8.16/1.48  fof(f46,plain,(
% 8.16/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 8.16/1.48    inference(definition_unfolding,[],[f33,f34])).
% 8.16/1.48  
% 8.16/1.48  fof(f40,plain,(
% 8.16/1.48    r1_tarski(sK2,sK3)),
% 8.16/1.48    inference(cnf_transformation,[],[f24])).
% 8.16/1.48  
% 8.16/1.48  cnf(c_156,plain,
% 8.16/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 8.16/1.48      theory(equality) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_964,plain,
% 8.16/1.48      ( ~ r2_hidden(X0,X1)
% 8.16/1.48      | r2_hidden(sK1(X2,X3,X4),X4)
% 8.16/1.48      | X4 != X1
% 8.16/1.48      | sK1(X2,X3,X4) != X0 ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_156]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_2678,plain,
% 8.16/1.48      ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),X0)
% 8.16/1.48      | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 8.16/1.48      | k2_enumset1(sK5,sK5,sK5,sK5) != X0
% 8.16/1.48      | sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_964]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_8367,plain,
% 8.16/1.48      ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 8.16/1.48      | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 8.16/1.48      | k2_enumset1(sK5,sK5,sK5,sK5) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
% 8.16/1.48      | sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_2678]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_32645,plain,
% 8.16/1.48      ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 8.16/1.48      | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))
% 8.16/1.48      | k2_enumset1(sK5,sK5,sK5,sK5) != k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))
% 8.16/1.48      | sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_8367]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_6,plain,
% 8.16/1.48      ( ~ r2_hidden(X0,X1)
% 8.16/1.48      | ~ r2_hidden(X0,X2)
% 8.16/1.48      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 8.16/1.48      inference(cnf_transformation,[],[f56]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_1506,plain,
% 8.16/1.48      ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),X0)
% 8.16/1.48      | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k4_xboole_0(X0,k4_xboole_0(X0,sK4)))
% 8.16/1.48      | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_4528,plain,
% 8.16/1.48      ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))
% 8.16/1.48      | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK3)
% 8.16/1.48      | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_1506]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_154,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_153,plain,( X0 = X0 ),theory(equality) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_913,plain,
% 8.16/1.48      ( X0 != X1 | X1 = X0 ),
% 8.16/1.48      inference(resolution,[status(thm)],[c_154,c_153]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_13,negated_conjecture,
% 8.16/1.48      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 8.16/1.48      inference(cnf_transformation,[],[f55]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_3307,plain,
% 8.16/1.48      ( k2_enumset1(sK5,sK5,sK5,sK5) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) ),
% 8.16/1.48      inference(resolution,[status(thm)],[c_913,c_13]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_5,plain,
% 8.16/1.48      ( r2_hidden(sK1(X0,X1,X2),X0)
% 8.16/1.48      | r2_hidden(sK1(X0,X1,X2),X2)
% 8.16/1.48      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 8.16/1.48      inference(cnf_transformation,[],[f48]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_11,negated_conjecture,
% 8.16/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k2_enumset1(sK5,sK5,sK5,sK5) ),
% 8.16/1.48      inference(cnf_transformation,[],[f54]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_2183,plain,
% 8.16/1.48      ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 8.16/1.48      | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2) ),
% 8.16/1.48      inference(resolution,[status(thm)],[c_5,c_11]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_12,negated_conjecture,
% 8.16/1.48      ( r2_hidden(sK5,sK2) ),
% 8.16/1.48      inference(cnf_transformation,[],[f42]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_9,plain,
% 8.16/1.48      ( ~ r2_hidden(X0,X1) | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
% 8.16/1.48      inference(cnf_transformation,[],[f52]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_591,plain,
% 8.16/1.48      ( ~ r2_hidden(sK5,sK2)
% 8.16/1.48      | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK2) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_9]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_2,plain,
% 8.16/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 8.16/1.48      inference(cnf_transformation,[],[f25]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_843,plain,
% 8.16/1.48      ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),X0)
% 8.16/1.48      | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
% 8.16/1.48      | ~ r1_tarski(X0,sK2) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_1476,plain,
% 8.16/1.48      ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(X0,X0,X0,X0))
% 8.16/1.48      | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
% 8.16/1.48      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),sK2) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_843]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_1480,plain,
% 8.16/1.48      ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 8.16/1.48      | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
% 8.16/1.48      | ~ r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK2) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_1476]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_2463,plain,
% 8.16/1.48      ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2) ),
% 8.16/1.48      inference(global_propositional_subsumption,
% 8.16/1.48                [status(thm)],
% 8.16/1.48                [c_2183,c_12,c_591,c_1480]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_4,plain,
% 8.16/1.48      ( r2_hidden(sK1(X0,X1,X2),X1)
% 8.16/1.48      | r2_hidden(sK1(X0,X1,X2),X2)
% 8.16/1.48      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 8.16/1.48      inference(cnf_transformation,[],[f47]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_2129,plain,
% 8.16/1.48      ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 8.16/1.48      | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) ),
% 8.16/1.48      inference(resolution,[status(thm)],[c_4,c_11]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_838,plain,
% 8.16/1.48      ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),X0)
% 8.16/1.48      | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4)
% 8.16/1.48      | ~ r1_tarski(X0,sK4) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_1228,plain,
% 8.16/1.48      ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(X0,X0,X0,X0))
% 8.16/1.48      | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4)
% 8.16/1.48      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),sK4) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_838]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_1232,plain,
% 8.16/1.48      ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 8.16/1.48      | r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4)
% 8.16/1.48      | ~ r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_1228]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_1230,plain,
% 8.16/1.48      ( ~ r2_hidden(X0,sK4) | r1_tarski(k2_enumset1(X0,X0,X0,X0),sK4) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_9]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_1236,plain,
% 8.16/1.48      ( ~ r2_hidden(sK5,sK4)
% 8.16/1.48      | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),sK4) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_1230]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_1,plain,
% 8.16/1.48      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 8.16/1.48      inference(cnf_transformation,[],[f26]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_470,plain,
% 8.16/1.48      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 8.16/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 8.16/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_0,plain,
% 8.16/1.48      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 8.16/1.48      inference(cnf_transformation,[],[f27]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_471,plain,
% 8.16/1.48      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 8.16/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 8.16/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_789,plain,
% 8.16/1.48      ( r1_tarski(X0,X0) = iProver_top ),
% 8.16/1.48      inference(superposition,[status(thm)],[c_470,c_471]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_10,plain,
% 8.16/1.48      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
% 8.16/1.48      inference(cnf_transformation,[],[f53]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_461,plain,
% 8.16/1.48      ( r2_hidden(X0,X1) = iProver_top
% 8.16/1.48      | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) != iProver_top ),
% 8.16/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_725,plain,
% 8.16/1.48      ( r2_hidden(sK5,X0) = iProver_top
% 8.16/1.48      | r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)),X0) != iProver_top ),
% 8.16/1.48      inference(superposition,[status(thm)],[c_13,c_461]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_1586,plain,
% 8.16/1.48      ( r2_hidden(sK5,k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) = iProver_top ),
% 8.16/1.48      inference(superposition,[status(thm)],[c_789,c_725]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_7,plain,
% 8.16/1.48      ( r2_hidden(X0,X1)
% 8.16/1.48      | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 8.16/1.48      inference(cnf_transformation,[],[f57]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_464,plain,
% 8.16/1.48      ( r2_hidden(X0,X1) = iProver_top
% 8.16/1.48      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 8.16/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_1782,plain,
% 8.16/1.48      ( r2_hidden(sK5,sK4) = iProver_top ),
% 8.16/1.48      inference(superposition,[status(thm)],[c_1586,c_464]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_1788,plain,
% 8.16/1.48      ( r2_hidden(sK5,sK4) ),
% 8.16/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_1782]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_2351,plain,
% 8.16/1.48      ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4) ),
% 8.16/1.48      inference(global_propositional_subsumption,
% 8.16/1.48                [status(thm)],
% 8.16/1.48                [c_2129,c_1232,c_1236,c_1788]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_669,plain,
% 8.16/1.48      ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),X0)
% 8.16/1.48      | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
% 8.16/1.48      | ~ r1_tarski(sK2,X0) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_2051,plain,
% 8.16/1.48      ( r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK3)
% 8.16/1.48      | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
% 8.16/1.48      | ~ r1_tarski(sK2,sK3) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_669]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_1619,plain,
% 8.16/1.48      ( sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) = sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_153]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_3,plain,
% 8.16/1.48      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 8.16/1.48      | ~ r2_hidden(sK1(X0,X1,X2),X0)
% 8.16/1.48      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 8.16/1.48      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 8.16/1.48      inference(cnf_transformation,[],[f46]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_776,plain,
% 8.16/1.48      ( ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),k2_enumset1(sK5,sK5,sK5,sK5))
% 8.16/1.48      | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK4)
% 8.16/1.48      | ~ r2_hidden(sK1(sK2,sK4,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
% 8.16/1.48      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 8.16/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(c_14,negated_conjecture,
% 8.16/1.48      ( r1_tarski(sK2,sK3) ),
% 8.16/1.48      inference(cnf_transformation,[],[f40]) ).
% 8.16/1.48  
% 8.16/1.48  cnf(contradiction,plain,
% 8.16/1.48      ( $false ),
% 8.16/1.48      inference(minisat,
% 8.16/1.48                [status(thm)],
% 8.16/1.48                [c_32645,c_4528,c_3307,c_2463,c_2351,c_2051,c_1619,c_776,
% 8.16/1.48                 c_11,c_14]) ).
% 8.16/1.48  
% 8.16/1.48  
% 8.16/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 8.16/1.48  
% 8.16/1.48  ------                               Statistics
% 8.16/1.48  
% 8.16/1.48  ------ Selected
% 8.16/1.48  
% 8.16/1.48  total_time:                             0.96
% 8.16/1.48  
%------------------------------------------------------------------------------
