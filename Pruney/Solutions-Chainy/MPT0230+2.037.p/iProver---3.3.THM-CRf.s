%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:46 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 479 expanded)
%              Number of clauses        :   51 (  91 expanded)
%              Number of leaves         :   22 ( 139 expanded)
%              Depth                    :   20
%              Number of atoms          :  274 ( 965 expanded)
%              Number of equality atoms :  218 ( 798 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f45,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f82,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f45,f67])).

fof(f91,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f82])).

fof(f92,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f91])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f84,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f52,f67,f67])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f55,f67])).

fof(f69,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f54,f68])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f53,f43,f59,f69])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK1 != sK3
      & sK1 != sK2
      & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( sK1 != sK3
    & sK1 != sK2
    & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f33])).

fof(f62,plain,(
    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,(
    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f62,f69,f68])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f38,f41])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f35,f41,f41])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f36,f41])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f44,f67])).

fof(f93,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f64,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_14,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_594,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X1,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2020,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X3),k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) = k5_enumset1(X2,X2,X2,X2,X1,X0,X3) ),
    inference(superposition,[status(thm)],[c_16,c_1])).

cnf(c_10128,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X2,X2,X2,X2,X1,X0,X3) ),
    inference(superposition,[status(thm)],[c_2020,c_1])).

cnf(c_10280,plain,
    ( k5_enumset1(X0,X0,X0,X0,X1,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X0,X1) ),
    inference(superposition,[status(thm)],[c_10128,c_16])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_592,plain,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1304,plain,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16,c_592])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_602,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2743,plain,
    ( k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2))) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[status(thm)],[c_1304,c_602])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3020,plain,
    ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_2743,c_0])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_603,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_601,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1723,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_603,c_601])).

cnf(c_1741,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1723,c_0])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1745,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1741,c_7])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1297,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_2114,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1745,c_1297])).

cnf(c_2115,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_2114,c_7,c_1745])).

cnf(c_2185,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2115,c_2])).

cnf(c_2189,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2185,c_1745])).

cnf(c_2190,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2189,c_1745])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1234,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_2370,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2190,c_1234])).

cnf(c_3035,plain,
    ( k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3020,c_2370])).

cnf(c_3450,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2),k1_xboole_0) = k5_enumset1(sK3,sK3,sK3,sK3,sK2,sK2,sK1) ),
    inference(superposition,[status(thm)],[c_3035,c_1])).

cnf(c_3459,plain,
    ( k5_enumset1(sK3,sK3,sK3,sK3,sK2,sK2,sK1) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_3450,c_7])).

cnf(c_10387,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK3,sK2) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_10280,c_3459])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_593,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10998,plain,
    ( sK2 = X0
    | sK3 = X0
    | r2_hidden(X0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10387,c_593])).

cnf(c_13439,plain,
    ( sK2 = sK1
    | sK3 = sK1 ),
    inference(superposition,[status(thm)],[c_594,c_10998])).

cnf(c_395,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_625,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_626,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_620,plain,
    ( sK3 != X0
    | sK1 != X0
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_621,plain,
    ( sK3 != sK1
    | sK1 = sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_29,plain,
    ( r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_26,plain,
    ( ~ r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_19,negated_conjecture,
    ( sK1 != sK3 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_20,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13439,c_626,c_621,c_29,c_26,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:36:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.95/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/0.98  
% 3.95/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.95/0.98  
% 3.95/0.98  ------  iProver source info
% 3.95/0.98  
% 3.95/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.95/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.95/0.98  git: non_committed_changes: false
% 3.95/0.98  git: last_make_outside_of_git: false
% 3.95/0.98  
% 3.95/0.98  ------ 
% 3.95/0.98  
% 3.95/0.98  ------ Input Options
% 3.95/0.98  
% 3.95/0.98  --out_options                           all
% 3.95/0.98  --tptp_safe_out                         true
% 3.95/0.98  --problem_path                          ""
% 3.95/0.98  --include_path                          ""
% 3.95/0.98  --clausifier                            res/vclausify_rel
% 3.95/0.98  --clausifier_options                    ""
% 3.95/0.98  --stdin                                 false
% 3.95/0.98  --stats_out                             all
% 3.95/0.98  
% 3.95/0.98  ------ General Options
% 3.95/0.98  
% 3.95/0.98  --fof                                   false
% 3.95/0.98  --time_out_real                         305.
% 3.95/0.98  --time_out_virtual                      -1.
% 3.95/0.98  --symbol_type_check                     false
% 3.95/0.98  --clausify_out                          false
% 3.95/0.98  --sig_cnt_out                           false
% 3.95/0.98  --trig_cnt_out                          false
% 3.95/0.98  --trig_cnt_out_tolerance                1.
% 3.95/0.98  --trig_cnt_out_sk_spl                   false
% 3.95/0.98  --abstr_cl_out                          false
% 3.95/0.98  
% 3.95/0.98  ------ Global Options
% 3.95/0.98  
% 3.95/0.98  --schedule                              default
% 3.95/0.98  --add_important_lit                     false
% 3.95/0.98  --prop_solver_per_cl                    1000
% 3.95/0.98  --min_unsat_core                        false
% 3.95/0.98  --soft_assumptions                      false
% 3.95/0.98  --soft_lemma_size                       3
% 3.95/0.98  --prop_impl_unit_size                   0
% 3.95/0.98  --prop_impl_unit                        []
% 3.95/0.98  --share_sel_clauses                     true
% 3.95/0.98  --reset_solvers                         false
% 3.95/0.98  --bc_imp_inh                            [conj_cone]
% 3.95/0.98  --conj_cone_tolerance                   3.
% 3.95/0.98  --extra_neg_conj                        none
% 3.95/0.98  --large_theory_mode                     true
% 3.95/0.98  --prolific_symb_bound                   200
% 3.95/0.98  --lt_threshold                          2000
% 3.95/0.98  --clause_weak_htbl                      true
% 3.95/0.98  --gc_record_bc_elim                     false
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing Options
% 3.95/0.98  
% 3.95/0.98  --preprocessing_flag                    true
% 3.95/0.98  --time_out_prep_mult                    0.1
% 3.95/0.98  --splitting_mode                        input
% 3.95/0.98  --splitting_grd                         true
% 3.95/0.98  --splitting_cvd                         false
% 3.95/0.98  --splitting_cvd_svl                     false
% 3.95/0.98  --splitting_nvd                         32
% 3.95/0.98  --sub_typing                            true
% 3.95/0.98  --prep_gs_sim                           true
% 3.95/0.98  --prep_unflatten                        true
% 3.95/0.98  --prep_res_sim                          true
% 3.95/0.98  --prep_upred                            true
% 3.95/0.98  --prep_sem_filter                       exhaustive
% 3.95/0.98  --prep_sem_filter_out                   false
% 3.95/0.98  --pred_elim                             true
% 3.95/0.98  --res_sim_input                         true
% 3.95/0.98  --eq_ax_congr_red                       true
% 3.95/0.98  --pure_diseq_elim                       true
% 3.95/0.98  --brand_transform                       false
% 3.95/0.98  --non_eq_to_eq                          false
% 3.95/0.98  --prep_def_merge                        true
% 3.95/0.98  --prep_def_merge_prop_impl              false
% 3.95/0.98  --prep_def_merge_mbd                    true
% 3.95/0.98  --prep_def_merge_tr_red                 false
% 3.95/0.98  --prep_def_merge_tr_cl                  false
% 3.95/0.98  --smt_preprocessing                     true
% 3.95/0.98  --smt_ac_axioms                         fast
% 3.95/0.98  --preprocessed_out                      false
% 3.95/0.98  --preprocessed_stats                    false
% 3.95/0.98  
% 3.95/0.98  ------ Abstraction refinement Options
% 3.95/0.98  
% 3.95/0.98  --abstr_ref                             []
% 3.95/0.98  --abstr_ref_prep                        false
% 3.95/0.98  --abstr_ref_until_sat                   false
% 3.95/0.98  --abstr_ref_sig_restrict                funpre
% 3.95/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.95/0.98  --abstr_ref_under                       []
% 3.95/0.98  
% 3.95/0.98  ------ SAT Options
% 3.95/0.98  
% 3.95/0.98  --sat_mode                              false
% 3.95/0.98  --sat_fm_restart_options                ""
% 3.95/0.98  --sat_gr_def                            false
% 3.95/0.98  --sat_epr_types                         true
% 3.95/0.98  --sat_non_cyclic_types                  false
% 3.95/0.98  --sat_finite_models                     false
% 3.95/0.98  --sat_fm_lemmas                         false
% 3.95/0.98  --sat_fm_prep                           false
% 3.95/0.98  --sat_fm_uc_incr                        true
% 3.95/0.98  --sat_out_model                         small
% 3.95/0.98  --sat_out_clauses                       false
% 3.95/0.98  
% 3.95/0.98  ------ QBF Options
% 3.95/0.98  
% 3.95/0.98  --qbf_mode                              false
% 3.95/0.98  --qbf_elim_univ                         false
% 3.95/0.98  --qbf_dom_inst                          none
% 3.95/0.98  --qbf_dom_pre_inst                      false
% 3.95/0.98  --qbf_sk_in                             false
% 3.95/0.98  --qbf_pred_elim                         true
% 3.95/0.98  --qbf_split                             512
% 3.95/0.98  
% 3.95/0.98  ------ BMC1 Options
% 3.95/0.98  
% 3.95/0.98  --bmc1_incremental                      false
% 3.95/0.98  --bmc1_axioms                           reachable_all
% 3.95/0.98  --bmc1_min_bound                        0
% 3.95/0.98  --bmc1_max_bound                        -1
% 3.95/0.98  --bmc1_max_bound_default                -1
% 3.95/0.98  --bmc1_symbol_reachability              true
% 3.95/0.98  --bmc1_property_lemmas                  false
% 3.95/0.98  --bmc1_k_induction                      false
% 3.95/0.98  --bmc1_non_equiv_states                 false
% 3.95/0.98  --bmc1_deadlock                         false
% 3.95/0.98  --bmc1_ucm                              false
% 3.95/0.98  --bmc1_add_unsat_core                   none
% 3.95/0.98  --bmc1_unsat_core_children              false
% 3.95/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.95/0.98  --bmc1_out_stat                         full
% 3.95/0.98  --bmc1_ground_init                      false
% 3.95/0.98  --bmc1_pre_inst_next_state              false
% 3.95/0.98  --bmc1_pre_inst_state                   false
% 3.95/0.98  --bmc1_pre_inst_reach_state             false
% 3.95/0.98  --bmc1_out_unsat_core                   false
% 3.95/0.98  --bmc1_aig_witness_out                  false
% 3.95/0.98  --bmc1_verbose                          false
% 3.95/0.98  --bmc1_dump_clauses_tptp                false
% 3.95/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.95/0.98  --bmc1_dump_file                        -
% 3.95/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.95/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.95/0.98  --bmc1_ucm_extend_mode                  1
% 3.95/0.98  --bmc1_ucm_init_mode                    2
% 3.95/0.98  --bmc1_ucm_cone_mode                    none
% 3.95/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.95/0.98  --bmc1_ucm_relax_model                  4
% 3.95/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.95/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.95/0.98  --bmc1_ucm_layered_model                none
% 3.95/0.98  --bmc1_ucm_max_lemma_size               10
% 3.95/0.98  
% 3.95/0.98  ------ AIG Options
% 3.95/0.98  
% 3.95/0.98  --aig_mode                              false
% 3.95/0.98  
% 3.95/0.98  ------ Instantiation Options
% 3.95/0.98  
% 3.95/0.98  --instantiation_flag                    true
% 3.95/0.98  --inst_sos_flag                         true
% 3.95/0.98  --inst_sos_phase                        true
% 3.95/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.95/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.95/0.98  --inst_lit_sel_side                     num_symb
% 3.95/0.98  --inst_solver_per_active                1400
% 3.95/0.98  --inst_solver_calls_frac                1.
% 3.95/0.98  --inst_passive_queue_type               priority_queues
% 3.95/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.95/0.98  --inst_passive_queues_freq              [25;2]
% 3.95/0.98  --inst_dismatching                      true
% 3.95/0.98  --inst_eager_unprocessed_to_passive     true
% 3.95/0.98  --inst_prop_sim_given                   true
% 3.95/0.98  --inst_prop_sim_new                     false
% 3.95/0.98  --inst_subs_new                         false
% 3.95/0.98  --inst_eq_res_simp                      false
% 3.95/0.98  --inst_subs_given                       false
% 3.95/0.98  --inst_orphan_elimination               true
% 3.95/0.98  --inst_learning_loop_flag               true
% 3.95/0.98  --inst_learning_start                   3000
% 3.95/0.98  --inst_learning_factor                  2
% 3.95/0.98  --inst_start_prop_sim_after_learn       3
% 3.95/0.98  --inst_sel_renew                        solver
% 3.95/0.98  --inst_lit_activity_flag                true
% 3.95/0.98  --inst_restr_to_given                   false
% 3.95/0.98  --inst_activity_threshold               500
% 3.95/0.98  --inst_out_proof                        true
% 3.95/0.98  
% 3.95/0.98  ------ Resolution Options
% 3.95/0.98  
% 3.95/0.98  --resolution_flag                       true
% 3.95/0.98  --res_lit_sel                           adaptive
% 3.95/0.98  --res_lit_sel_side                      none
% 3.95/0.98  --res_ordering                          kbo
% 3.95/0.98  --res_to_prop_solver                    active
% 3.95/0.98  --res_prop_simpl_new                    false
% 3.95/0.98  --res_prop_simpl_given                  true
% 3.95/0.98  --res_passive_queue_type                priority_queues
% 3.95/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.95/0.98  --res_passive_queues_freq               [15;5]
% 3.95/0.98  --res_forward_subs                      full
% 3.95/0.98  --res_backward_subs                     full
% 3.95/0.98  --res_forward_subs_resolution           true
% 3.95/0.98  --res_backward_subs_resolution          true
% 3.95/0.98  --res_orphan_elimination                true
% 3.95/0.98  --res_time_limit                        2.
% 3.95/0.98  --res_out_proof                         true
% 3.95/0.98  
% 3.95/0.98  ------ Superposition Options
% 3.95/0.98  
% 3.95/0.98  --superposition_flag                    true
% 3.95/0.98  --sup_passive_queue_type                priority_queues
% 3.95/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.95/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.95/0.98  --demod_completeness_check              fast
% 3.95/0.98  --demod_use_ground                      true
% 3.95/0.98  --sup_to_prop_solver                    passive
% 3.95/0.98  --sup_prop_simpl_new                    true
% 3.95/0.98  --sup_prop_simpl_given                  true
% 3.95/0.98  --sup_fun_splitting                     true
% 3.95/0.98  --sup_smt_interval                      50000
% 3.95/0.98  
% 3.95/0.98  ------ Superposition Simplification Setup
% 3.95/0.98  
% 3.95/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.95/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.95/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.95/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.95/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.95/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.95/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.95/0.98  --sup_immed_triv                        [TrivRules]
% 3.95/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/0.98  --sup_immed_bw_main                     []
% 3.95/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.95/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.95/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/0.98  --sup_input_bw                          []
% 3.95/0.98  
% 3.95/0.98  ------ Combination Options
% 3.95/0.98  
% 3.95/0.98  --comb_res_mult                         3
% 3.95/0.98  --comb_sup_mult                         2
% 3.95/0.98  --comb_inst_mult                        10
% 3.95/0.98  
% 3.95/0.98  ------ Debug Options
% 3.95/0.98  
% 3.95/0.98  --dbg_backtrace                         false
% 3.95/0.98  --dbg_dump_prop_clauses                 false
% 3.95/0.98  --dbg_dump_prop_clauses_file            -
% 3.95/0.98  --dbg_out_stat                          false
% 3.95/0.98  ------ Parsing...
% 3.95/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.95/0.98  ------ Proving...
% 3.95/0.98  ------ Problem Properties 
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  clauses                                 22
% 3.95/0.98  conjectures                             3
% 3.95/0.98  EPR                                     3
% 3.95/0.98  Horn                                    20
% 3.95/0.98  unary                                   15
% 3.95/0.98  binary                                  2
% 3.95/0.98  lits                                    37
% 3.95/0.98  lits eq                                 25
% 3.95/0.98  fd_pure                                 0
% 3.95/0.98  fd_pseudo                               0
% 3.95/0.98  fd_cond                                 1
% 3.95/0.98  fd_pseudo_cond                          4
% 3.95/0.98  AC symbols                              0
% 3.95/0.98  
% 3.95/0.98  ------ Schedule dynamic 5 is on 
% 3.95/0.98  
% 3.95/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  ------ 
% 3.95/0.98  Current options:
% 3.95/0.98  ------ 
% 3.95/0.98  
% 3.95/0.98  ------ Input Options
% 3.95/0.98  
% 3.95/0.98  --out_options                           all
% 3.95/0.98  --tptp_safe_out                         true
% 3.95/0.98  --problem_path                          ""
% 3.95/0.98  --include_path                          ""
% 3.95/0.98  --clausifier                            res/vclausify_rel
% 3.95/0.98  --clausifier_options                    ""
% 3.95/0.98  --stdin                                 false
% 3.95/0.98  --stats_out                             all
% 3.95/0.98  
% 3.95/0.98  ------ General Options
% 3.95/0.98  
% 3.95/0.98  --fof                                   false
% 3.95/0.98  --time_out_real                         305.
% 3.95/0.98  --time_out_virtual                      -1.
% 3.95/0.98  --symbol_type_check                     false
% 3.95/0.98  --clausify_out                          false
% 3.95/0.98  --sig_cnt_out                           false
% 3.95/0.98  --trig_cnt_out                          false
% 3.95/0.98  --trig_cnt_out_tolerance                1.
% 3.95/0.98  --trig_cnt_out_sk_spl                   false
% 3.95/0.98  --abstr_cl_out                          false
% 3.95/0.98  
% 3.95/0.98  ------ Global Options
% 3.95/0.98  
% 3.95/0.98  --schedule                              default
% 3.95/0.98  --add_important_lit                     false
% 3.95/0.98  --prop_solver_per_cl                    1000
% 3.95/0.98  --min_unsat_core                        false
% 3.95/0.98  --soft_assumptions                      false
% 3.95/0.98  --soft_lemma_size                       3
% 3.95/0.98  --prop_impl_unit_size                   0
% 3.95/0.98  --prop_impl_unit                        []
% 3.95/0.98  --share_sel_clauses                     true
% 3.95/0.98  --reset_solvers                         false
% 3.95/0.98  --bc_imp_inh                            [conj_cone]
% 3.95/0.98  --conj_cone_tolerance                   3.
% 3.95/0.98  --extra_neg_conj                        none
% 3.95/0.98  --large_theory_mode                     true
% 3.95/0.98  --prolific_symb_bound                   200
% 3.95/0.98  --lt_threshold                          2000
% 3.95/0.98  --clause_weak_htbl                      true
% 3.95/0.98  --gc_record_bc_elim                     false
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing Options
% 3.95/0.98  
% 3.95/0.98  --preprocessing_flag                    true
% 3.95/0.98  --time_out_prep_mult                    0.1
% 3.95/0.98  --splitting_mode                        input
% 3.95/0.98  --splitting_grd                         true
% 3.95/0.98  --splitting_cvd                         false
% 3.95/0.98  --splitting_cvd_svl                     false
% 3.95/0.98  --splitting_nvd                         32
% 3.95/0.98  --sub_typing                            true
% 3.95/0.98  --prep_gs_sim                           true
% 3.95/0.98  --prep_unflatten                        true
% 3.95/0.98  --prep_res_sim                          true
% 3.95/0.98  --prep_upred                            true
% 3.95/0.98  --prep_sem_filter                       exhaustive
% 3.95/0.98  --prep_sem_filter_out                   false
% 3.95/0.98  --pred_elim                             true
% 3.95/0.98  --res_sim_input                         true
% 3.95/0.98  --eq_ax_congr_red                       true
% 3.95/0.98  --pure_diseq_elim                       true
% 3.95/0.98  --brand_transform                       false
% 3.95/0.98  --non_eq_to_eq                          false
% 3.95/0.98  --prep_def_merge                        true
% 3.95/0.98  --prep_def_merge_prop_impl              false
% 3.95/0.98  --prep_def_merge_mbd                    true
% 3.95/0.98  --prep_def_merge_tr_red                 false
% 3.95/0.98  --prep_def_merge_tr_cl                  false
% 3.95/0.98  --smt_preprocessing                     true
% 3.95/0.98  --smt_ac_axioms                         fast
% 3.95/0.98  --preprocessed_out                      false
% 3.95/0.98  --preprocessed_stats                    false
% 3.95/0.98  
% 3.95/0.98  ------ Abstraction refinement Options
% 3.95/0.98  
% 3.95/0.98  --abstr_ref                             []
% 3.95/0.98  --abstr_ref_prep                        false
% 3.95/0.98  --abstr_ref_until_sat                   false
% 3.95/0.98  --abstr_ref_sig_restrict                funpre
% 3.95/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.95/0.98  --abstr_ref_under                       []
% 3.95/0.98  
% 3.95/0.98  ------ SAT Options
% 3.95/0.98  
% 3.95/0.98  --sat_mode                              false
% 3.95/0.98  --sat_fm_restart_options                ""
% 3.95/0.98  --sat_gr_def                            false
% 3.95/0.98  --sat_epr_types                         true
% 3.95/0.98  --sat_non_cyclic_types                  false
% 3.95/0.98  --sat_finite_models                     false
% 3.95/0.98  --sat_fm_lemmas                         false
% 3.95/0.98  --sat_fm_prep                           false
% 3.95/0.98  --sat_fm_uc_incr                        true
% 3.95/0.98  --sat_out_model                         small
% 3.95/0.98  --sat_out_clauses                       false
% 3.95/0.98  
% 3.95/0.98  ------ QBF Options
% 3.95/0.98  
% 3.95/0.98  --qbf_mode                              false
% 3.95/0.98  --qbf_elim_univ                         false
% 3.95/0.98  --qbf_dom_inst                          none
% 3.95/0.98  --qbf_dom_pre_inst                      false
% 3.95/0.98  --qbf_sk_in                             false
% 3.95/0.98  --qbf_pred_elim                         true
% 3.95/0.98  --qbf_split                             512
% 3.95/0.98  
% 3.95/0.98  ------ BMC1 Options
% 3.95/0.98  
% 3.95/0.98  --bmc1_incremental                      false
% 3.95/0.98  --bmc1_axioms                           reachable_all
% 3.95/0.98  --bmc1_min_bound                        0
% 3.95/0.98  --bmc1_max_bound                        -1
% 3.95/0.98  --bmc1_max_bound_default                -1
% 3.95/0.98  --bmc1_symbol_reachability              true
% 3.95/0.98  --bmc1_property_lemmas                  false
% 3.95/0.98  --bmc1_k_induction                      false
% 3.95/0.98  --bmc1_non_equiv_states                 false
% 3.95/0.98  --bmc1_deadlock                         false
% 3.95/0.98  --bmc1_ucm                              false
% 3.95/0.98  --bmc1_add_unsat_core                   none
% 3.95/0.98  --bmc1_unsat_core_children              false
% 3.95/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.95/0.98  --bmc1_out_stat                         full
% 3.95/0.98  --bmc1_ground_init                      false
% 3.95/0.98  --bmc1_pre_inst_next_state              false
% 3.95/0.98  --bmc1_pre_inst_state                   false
% 3.95/0.98  --bmc1_pre_inst_reach_state             false
% 3.95/0.98  --bmc1_out_unsat_core                   false
% 3.95/0.98  --bmc1_aig_witness_out                  false
% 3.95/0.98  --bmc1_verbose                          false
% 3.95/0.98  --bmc1_dump_clauses_tptp                false
% 3.95/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.95/0.98  --bmc1_dump_file                        -
% 3.95/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.95/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.95/0.98  --bmc1_ucm_extend_mode                  1
% 3.95/0.98  --bmc1_ucm_init_mode                    2
% 3.95/0.98  --bmc1_ucm_cone_mode                    none
% 3.95/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.95/0.98  --bmc1_ucm_relax_model                  4
% 3.95/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.95/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.95/0.98  --bmc1_ucm_layered_model                none
% 3.95/0.98  --bmc1_ucm_max_lemma_size               10
% 3.95/0.98  
% 3.95/0.98  ------ AIG Options
% 3.95/0.98  
% 3.95/0.98  --aig_mode                              false
% 3.95/0.98  
% 3.95/0.98  ------ Instantiation Options
% 3.95/0.98  
% 3.95/0.98  --instantiation_flag                    true
% 3.95/0.98  --inst_sos_flag                         true
% 3.95/0.98  --inst_sos_phase                        true
% 3.95/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.95/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.95/0.98  --inst_lit_sel_side                     none
% 3.95/0.98  --inst_solver_per_active                1400
% 3.95/0.98  --inst_solver_calls_frac                1.
% 3.95/0.98  --inst_passive_queue_type               priority_queues
% 3.95/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.95/0.98  --inst_passive_queues_freq              [25;2]
% 3.95/0.98  --inst_dismatching                      true
% 3.95/0.98  --inst_eager_unprocessed_to_passive     true
% 3.95/0.98  --inst_prop_sim_given                   true
% 3.95/0.98  --inst_prop_sim_new                     false
% 3.95/0.98  --inst_subs_new                         false
% 3.95/0.98  --inst_eq_res_simp                      false
% 3.95/0.98  --inst_subs_given                       false
% 3.95/0.98  --inst_orphan_elimination               true
% 3.95/0.98  --inst_learning_loop_flag               true
% 3.95/0.98  --inst_learning_start                   3000
% 3.95/0.98  --inst_learning_factor                  2
% 3.95/0.98  --inst_start_prop_sim_after_learn       3
% 3.95/0.98  --inst_sel_renew                        solver
% 3.95/0.98  --inst_lit_activity_flag                true
% 3.95/0.98  --inst_restr_to_given                   false
% 3.95/0.98  --inst_activity_threshold               500
% 3.95/0.98  --inst_out_proof                        true
% 3.95/0.98  
% 3.95/0.98  ------ Resolution Options
% 3.95/0.98  
% 3.95/0.98  --resolution_flag                       false
% 3.95/0.98  --res_lit_sel                           adaptive
% 3.95/0.98  --res_lit_sel_side                      none
% 3.95/0.98  --res_ordering                          kbo
% 3.95/0.98  --res_to_prop_solver                    active
% 3.95/0.98  --res_prop_simpl_new                    false
% 3.95/0.98  --res_prop_simpl_given                  true
% 3.95/0.98  --res_passive_queue_type                priority_queues
% 3.95/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.95/0.98  --res_passive_queues_freq               [15;5]
% 3.95/0.98  --res_forward_subs                      full
% 3.95/0.98  --res_backward_subs                     full
% 3.95/0.98  --res_forward_subs_resolution           true
% 3.95/0.98  --res_backward_subs_resolution          true
% 3.95/0.98  --res_orphan_elimination                true
% 3.95/0.98  --res_time_limit                        2.
% 3.95/0.98  --res_out_proof                         true
% 3.95/0.98  
% 3.95/0.98  ------ Superposition Options
% 3.95/0.98  
% 3.95/0.98  --superposition_flag                    true
% 3.95/0.98  --sup_passive_queue_type                priority_queues
% 3.95/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.95/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.95/0.98  --demod_completeness_check              fast
% 3.95/0.98  --demod_use_ground                      true
% 3.95/0.98  --sup_to_prop_solver                    passive
% 3.95/0.98  --sup_prop_simpl_new                    true
% 3.95/0.98  --sup_prop_simpl_given                  true
% 3.95/0.98  --sup_fun_splitting                     true
% 3.95/0.98  --sup_smt_interval                      50000
% 3.95/0.98  
% 3.95/0.98  ------ Superposition Simplification Setup
% 3.95/0.98  
% 3.95/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.95/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.95/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.95/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.95/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.95/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.95/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.95/0.98  --sup_immed_triv                        [TrivRules]
% 3.95/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/0.98  --sup_immed_bw_main                     []
% 3.95/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.95/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.95/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/0.98  --sup_input_bw                          []
% 3.95/0.98  
% 3.95/0.98  ------ Combination Options
% 3.95/0.98  
% 3.95/0.98  --comb_res_mult                         3
% 3.95/0.98  --comb_sup_mult                         2
% 3.95/0.98  --comb_inst_mult                        10
% 3.95/0.98  
% 3.95/0.98  ------ Debug Options
% 3.95/0.98  
% 3.95/0.98  --dbg_backtrace                         false
% 3.95/0.98  --dbg_dump_prop_clauses                 false
% 3.95/0.98  --dbg_dump_prop_clauses_file            -
% 3.95/0.98  --dbg_out_stat                          false
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  ------ Proving...
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  % SZS status Theorem for theBenchmark.p
% 3.95/0.98  
% 3.95/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.95/0.98  
% 3.95/0.98  fof(f10,axiom,(
% 3.95/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f26,plain,(
% 3.95/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.95/0.98    inference(ennf_transformation,[],[f10])).
% 3.95/0.98  
% 3.95/0.98  fof(f28,plain,(
% 3.95/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.95/0.98    inference(nnf_transformation,[],[f26])).
% 3.95/0.98  
% 3.95/0.98  fof(f29,plain,(
% 3.95/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.95/0.98    inference(flattening,[],[f28])).
% 3.95/0.98  
% 3.95/0.98  fof(f30,plain,(
% 3.95/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.95/0.98    inference(rectify,[],[f29])).
% 3.95/0.98  
% 3.95/0.98  fof(f31,plain,(
% 3.95/0.98    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.95/0.98    introduced(choice_axiom,[])).
% 3.95/0.98  
% 3.95/0.98  fof(f32,plain,(
% 3.95/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.95/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.95/0.98  
% 3.95/0.98  fof(f45,plain,(
% 3.95/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.95/0.98    inference(cnf_transformation,[],[f32])).
% 3.95/0.98  
% 3.95/0.98  fof(f15,axiom,(
% 3.95/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f56,plain,(
% 3.95/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f15])).
% 3.95/0.98  
% 3.95/0.98  fof(f16,axiom,(
% 3.95/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f57,plain,(
% 3.95/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f16])).
% 3.95/0.98  
% 3.95/0.98  fof(f17,axiom,(
% 3.95/0.98    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f58,plain,(
% 3.95/0.98    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f17])).
% 3.95/0.98  
% 3.95/0.98  fof(f18,axiom,(
% 3.95/0.98    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f59,plain,(
% 3.95/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f18])).
% 3.95/0.98  
% 3.95/0.98  fof(f65,plain,(
% 3.95/0.98    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.95/0.98    inference(definition_unfolding,[],[f58,f59])).
% 3.95/0.98  
% 3.95/0.98  fof(f66,plain,(
% 3.95/0.98    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.95/0.98    inference(definition_unfolding,[],[f57,f65])).
% 3.95/0.98  
% 3.95/0.98  fof(f67,plain,(
% 3.95/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.95/0.98    inference(definition_unfolding,[],[f56,f66])).
% 3.95/0.98  
% 3.95/0.98  fof(f82,plain,(
% 3.95/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.95/0.98    inference(definition_unfolding,[],[f45,f67])).
% 3.95/0.98  
% 3.95/0.98  fof(f91,plain,(
% 3.95/0.98    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 3.95/0.98    inference(equality_resolution,[],[f82])).
% 3.95/0.98  
% 3.95/0.98  fof(f92,plain,(
% 3.95/0.98    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2))) )),
% 3.95/0.98    inference(equality_resolution,[],[f91])).
% 3.95/0.98  
% 3.95/0.98  fof(f11,axiom,(
% 3.95/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f52,plain,(
% 3.95/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f11])).
% 3.95/0.98  
% 3.95/0.98  fof(f84,plain,(
% 3.95/0.98    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X1,X0)) )),
% 3.95/0.98    inference(definition_unfolding,[],[f52,f67,f67])).
% 3.95/0.98  
% 3.95/0.98  fof(f12,axiom,(
% 3.95/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f53,plain,(
% 3.95/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f12])).
% 3.95/0.98  
% 3.95/0.98  fof(f9,axiom,(
% 3.95/0.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f43,plain,(
% 3.95/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f9])).
% 3.95/0.98  
% 3.95/0.98  fof(f13,axiom,(
% 3.95/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f54,plain,(
% 3.95/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f13])).
% 3.95/0.98  
% 3.95/0.98  fof(f14,axiom,(
% 3.95/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f55,plain,(
% 3.95/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f14])).
% 3.95/0.98  
% 3.95/0.98  fof(f68,plain,(
% 3.95/0.98    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.95/0.98    inference(definition_unfolding,[],[f55,f67])).
% 3.95/0.98  
% 3.95/0.98  fof(f69,plain,(
% 3.95/0.98    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.95/0.98    inference(definition_unfolding,[],[f54,f68])).
% 3.95/0.98  
% 3.95/0.98  fof(f71,plain,(
% 3.95/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.95/0.98    inference(definition_unfolding,[],[f53,f43,f59,f69])).
% 3.95/0.98  
% 3.95/0.98  fof(f21,conjecture,(
% 3.95/0.98    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f22,negated_conjecture,(
% 3.95/0.98    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.95/0.98    inference(negated_conjecture,[],[f21])).
% 3.95/0.98  
% 3.95/0.98  fof(f27,plain,(
% 3.95/0.98    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.95/0.98    inference(ennf_transformation,[],[f22])).
% 3.95/0.98  
% 3.95/0.98  fof(f33,plain,(
% 3.95/0.98    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 3.95/0.98    introduced(choice_axiom,[])).
% 3.95/0.98  
% 3.95/0.98  fof(f34,plain,(
% 3.95/0.98    sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 3.95/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f33])).
% 3.95/0.98  
% 3.95/0.98  fof(f62,plain,(
% 3.95/0.98    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 3.95/0.98    inference(cnf_transformation,[],[f34])).
% 3.95/0.98  
% 3.95/0.98  fof(f86,plain,(
% 3.95/0.98    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 3.95/0.98    inference(definition_unfolding,[],[f62,f69,f68])).
% 3.95/0.98  
% 3.95/0.98  fof(f5,axiom,(
% 3.95/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f24,plain,(
% 3.95/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.95/0.98    inference(ennf_transformation,[],[f5])).
% 3.95/0.98  
% 3.95/0.98  fof(f39,plain,(
% 3.95/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f24])).
% 3.95/0.98  
% 3.95/0.98  fof(f7,axiom,(
% 3.95/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f41,plain,(
% 3.95/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.95/0.98    inference(cnf_transformation,[],[f7])).
% 3.95/0.98  
% 3.95/0.98  fof(f75,plain,(
% 3.95/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.95/0.98    inference(definition_unfolding,[],[f39,f41])).
% 3.95/0.98  
% 3.95/0.98  fof(f3,axiom,(
% 3.95/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f37,plain,(
% 3.95/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.95/0.98    inference(cnf_transformation,[],[f3])).
% 3.95/0.98  
% 3.95/0.98  fof(f70,plain,(
% 3.95/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.95/0.98    inference(definition_unfolding,[],[f37,f41])).
% 3.95/0.98  
% 3.95/0.98  fof(f4,axiom,(
% 3.95/0.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f38,plain,(
% 3.95/0.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f4])).
% 3.95/0.98  
% 3.95/0.98  fof(f74,plain,(
% 3.95/0.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 3.95/0.98    inference(definition_unfolding,[],[f38,f41])).
% 3.95/0.98  
% 3.95/0.98  fof(f6,axiom,(
% 3.95/0.98    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f25,plain,(
% 3.95/0.98    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.95/0.98    inference(ennf_transformation,[],[f6])).
% 3.95/0.98  
% 3.95/0.98  fof(f40,plain,(
% 3.95/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f25])).
% 3.95/0.98  
% 3.95/0.98  fof(f8,axiom,(
% 3.95/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f42,plain,(
% 3.95/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.95/0.98    inference(cnf_transformation,[],[f8])).
% 3.95/0.98  
% 3.95/0.98  fof(f1,axiom,(
% 3.95/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f35,plain,(
% 3.95/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.95/0.98    inference(cnf_transformation,[],[f1])).
% 3.95/0.98  
% 3.95/0.98  fof(f72,plain,(
% 3.95/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.95/0.98    inference(definition_unfolding,[],[f35,f41,f41])).
% 3.95/0.98  
% 3.95/0.98  fof(f2,axiom,(
% 3.95/0.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.98  
% 3.95/0.98  fof(f23,plain,(
% 3.95/0.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.95/0.98    inference(rectify,[],[f2])).
% 3.95/0.98  
% 3.95/0.98  fof(f36,plain,(
% 3.95/0.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.95/0.98    inference(cnf_transformation,[],[f23])).
% 3.95/0.98  
% 3.95/0.98  fof(f73,plain,(
% 3.95/0.98    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 3.95/0.98    inference(definition_unfolding,[],[f36,f41])).
% 3.95/0.98  
% 3.95/0.98  fof(f44,plain,(
% 3.95/0.98    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.95/0.98    inference(cnf_transformation,[],[f32])).
% 3.95/0.98  
% 3.95/0.98  fof(f83,plain,(
% 3.95/0.98    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.95/0.98    inference(definition_unfolding,[],[f44,f67])).
% 3.95/0.98  
% 3.95/0.98  fof(f93,plain,(
% 3.95/0.98    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) )),
% 3.95/0.98    inference(equality_resolution,[],[f83])).
% 3.95/0.98  
% 3.95/0.98  fof(f64,plain,(
% 3.95/0.98    sK1 != sK3),
% 3.95/0.98    inference(cnf_transformation,[],[f34])).
% 3.95/0.98  
% 3.95/0.98  fof(f63,plain,(
% 3.95/0.98    sK1 != sK2),
% 3.95/0.98    inference(cnf_transformation,[],[f34])).
% 3.95/0.98  
% 3.95/0.98  cnf(c_14,plain,
% 3.95/0.98      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
% 3.95/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_594,plain,
% 3.95/0.98      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_16,plain,
% 3.95/0.98      ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X1,X0) ),
% 3.95/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1,plain,
% 3.95/0.98      ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.95/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2020,plain,
% 3.95/0.98      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X3),k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) = k5_enumset1(X2,X2,X2,X2,X1,X0,X3) ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_16,c_1]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_10128,plain,
% 3.95/0.98      ( k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X2,X2,X2,X2,X1,X0,X3) ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_2020,c_1]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_10280,plain,
% 3.95/0.98      ( k5_enumset1(X0,X0,X0,X0,X1,X1,X2) = k5_enumset1(X2,X2,X2,X2,X2,X0,X1) ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_10128,c_16]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_21,negated_conjecture,
% 3.95/0.98      ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 3.95/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_592,plain,
% 3.95/0.98      ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1304,plain,
% 3.95/0.98      ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2)) = iProver_top ),
% 3.95/0.98      inference(demodulation,[status(thm)],[c_16,c_592]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_5,plain,
% 3.95/0.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.95/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_602,plain,
% 3.95/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 3.95/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2743,plain,
% 3.95/0.98      ( k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2))) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1304,c_602]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_0,plain,
% 3.95/0.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.95/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_3020,plain,
% 3.95/0.98      ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2)) ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_2743,c_0]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_4,plain,
% 3.95/0.98      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 3.95/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_603,plain,
% 3.95/0.98      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_6,plain,
% 3.95/0.98      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.95/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_601,plain,
% 3.95/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1723,plain,
% 3.95/0.98      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_603,c_601]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1741,plain,
% 3.95/0.98      ( k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1723,c_0]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_7,plain,
% 3.95/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.95/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1745,plain,
% 3.95/0.98      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.95/0.98      inference(demodulation,[status(thm)],[c_1741,c_7]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2,plain,
% 3.95/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.95/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1297,plain,
% 3.95/0.98      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2114,plain,
% 3.95/0.98      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_1745,c_1297]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2115,plain,
% 3.95/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.95/0.98      inference(demodulation,[status(thm)],[c_2114,c_7,c_1745]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2185,plain,
% 3.95/0.98      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_2115,c_2]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2189,plain,
% 3.95/0.98      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.95/0.98      inference(light_normalisation,[status(thm)],[c_2185,c_1745]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2190,plain,
% 3.95/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.95/0.98      inference(demodulation,[status(thm)],[c_2189,c_1745]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_3,plain,
% 3.95/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.95/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_1234,plain,
% 3.95/0.98      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_2370,plain,
% 3.95/0.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.95/0.98      inference(demodulation,[status(thm)],[c_2190,c_1234]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_3035,plain,
% 3.95/0.98      ( k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2)) = k1_xboole_0 ),
% 3.95/0.98      inference(demodulation,[status(thm)],[c_3020,c_2370]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_3450,plain,
% 3.95/0.98      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2),k1_xboole_0) = k5_enumset1(sK3,sK3,sK3,sK3,sK2,sK2,sK1) ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_3035,c_1]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_3459,plain,
% 3.95/0.98      ( k5_enumset1(sK3,sK3,sK3,sK3,sK2,sK2,sK1) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2) ),
% 3.95/0.98      inference(demodulation,[status(thm)],[c_3450,c_7]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_10387,plain,
% 3.95/0.98      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK3,sK2) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2) ),
% 3.95/0.98      inference(demodulation,[status(thm)],[c_10280,c_3459]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_15,plain,
% 3.95/0.98      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))
% 3.95/0.98      | X0 = X1
% 3.95/0.98      | X0 = X2
% 3.95/0.98      | X0 = X3 ),
% 3.95/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_593,plain,
% 3.95/0.98      ( X0 = X1
% 3.95/0.98      | X0 = X2
% 3.95/0.98      | X0 = X3
% 3.95/0.98      | r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3)) != iProver_top ),
% 3.95/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_10998,plain,
% 3.95/0.98      ( sK2 = X0
% 3.95/0.98      | sK3 = X0
% 3.95/0.98      | r2_hidden(X0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK3,sK2)) != iProver_top ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_10387,c_593]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_13439,plain,
% 3.95/0.98      ( sK2 = sK1 | sK3 = sK1 ),
% 3.95/0.98      inference(superposition,[status(thm)],[c_594,c_10998]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_395,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_625,plain,
% 3.95/0.98      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 3.95/0.98      inference(instantiation,[status(thm)],[c_395]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_626,plain,
% 3.95/0.98      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 3.95/0.98      inference(instantiation,[status(thm)],[c_625]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_620,plain,
% 3.95/0.98      ( sK3 != X0 | sK1 != X0 | sK1 = sK3 ),
% 3.95/0.98      inference(instantiation,[status(thm)],[c_395]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_621,plain,
% 3.95/0.98      ( sK3 != sK1 | sK1 = sK3 | sK1 != sK1 ),
% 3.95/0.98      inference(instantiation,[status(thm)],[c_620]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_29,plain,
% 3.95/0.98      ( r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 3.95/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_26,plain,
% 3.95/0.98      ( ~ r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 3.95/0.98      | sK1 = sK1 ),
% 3.95/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_19,negated_conjecture,
% 3.95/0.98      ( sK1 != sK3 ),
% 3.95/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(c_20,negated_conjecture,
% 3.95/0.98      ( sK1 != sK2 ),
% 3.95/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.95/0.98  
% 3.95/0.98  cnf(contradiction,plain,
% 3.95/0.98      ( $false ),
% 3.95/0.98      inference(minisat,
% 3.95/0.98                [status(thm)],
% 3.95/0.98                [c_13439,c_626,c_621,c_29,c_26,c_19,c_20]) ).
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.95/0.98  
% 3.95/0.98  ------                               Statistics
% 3.95/0.98  
% 3.95/0.98  ------ General
% 3.95/0.98  
% 3.95/0.98  abstr_ref_over_cycles:                  0
% 3.95/0.98  abstr_ref_under_cycles:                 0
% 3.95/0.98  gc_basic_clause_elim:                   0
% 3.95/0.98  forced_gc_time:                         0
% 3.95/0.98  parsing_time:                           0.009
% 3.95/0.98  unif_index_cands_time:                  0.
% 3.95/0.98  unif_index_add_time:                    0.
% 3.95/0.98  orderings_time:                         0.
% 3.95/0.98  out_proof_time:                         0.008
% 3.95/0.98  total_time:                             0.412
% 3.95/0.98  num_of_symbols:                         42
% 3.95/0.98  num_of_terms:                           15421
% 3.95/0.98  
% 3.95/0.98  ------ Preprocessing
% 3.95/0.98  
% 3.95/0.98  num_of_splits:                          0
% 3.95/0.98  num_of_split_atoms:                     0
% 3.95/0.98  num_of_reused_defs:                     0
% 3.95/0.98  num_eq_ax_congr_red:                    24
% 3.95/0.98  num_of_sem_filtered_clauses:            1
% 3.95/0.98  num_of_subtypes:                        0
% 3.95/0.98  monotx_restored_types:                  0
% 3.95/0.98  sat_num_of_epr_types:                   0
% 3.95/0.98  sat_num_of_non_cyclic_types:            0
% 3.95/0.98  sat_guarded_non_collapsed_types:        0
% 3.95/0.98  num_pure_diseq_elim:                    0
% 3.95/0.98  simp_replaced_by:                       0
% 3.95/0.98  res_preprocessed:                       81
% 3.95/0.98  prep_upred:                             0
% 3.95/0.98  prep_unflattend:                        21
% 3.95/0.98  smt_new_axioms:                         0
% 3.95/0.98  pred_elim_cands:                        2
% 3.95/0.98  pred_elim:                              0
% 3.95/0.98  pred_elim_cl:                           0
% 3.95/0.98  pred_elim_cycles:                       2
% 3.95/0.98  merged_defs:                            0
% 3.95/0.98  merged_defs_ncl:                        0
% 3.95/0.98  bin_hyper_res:                          0
% 3.95/0.98  prep_cycles:                            3
% 3.95/0.98  pred_elim_time:                         0.003
% 3.95/0.98  splitting_time:                         0.
% 3.95/0.98  sem_filter_time:                        0.
% 3.95/0.98  monotx_time:                            0.
% 3.95/0.98  subtype_inf_time:                       0.
% 3.95/0.98  
% 3.95/0.98  ------ Problem properties
% 3.95/0.98  
% 3.95/0.98  clauses:                                22
% 3.95/0.98  conjectures:                            3
% 3.95/0.98  epr:                                    3
% 3.95/0.98  horn:                                   20
% 3.95/0.98  ground:                                 3
% 3.95/0.98  unary:                                  15
% 3.95/0.98  binary:                                 2
% 3.95/0.98  lits:                                   37
% 3.95/0.98  lits_eq:                                25
% 3.95/0.98  fd_pure:                                0
% 3.95/0.98  fd_pseudo:                              0
% 3.95/0.98  fd_cond:                                1
% 3.95/0.98  fd_pseudo_cond:                         4
% 3.95/0.98  ac_symbols:                             0
% 3.95/0.98  
% 3.95/0.98  ------ Propositional Solver
% 3.95/0.98  
% 3.95/0.98  prop_solver_calls:                      27
% 3.95/0.98  prop_fast_solver_calls:                 518
% 3.95/0.98  smt_solver_calls:                       0
% 3.95/0.98  smt_fast_solver_calls:                  0
% 3.95/0.98  prop_num_of_clauses:                    4015
% 3.95/0.98  prop_preprocess_simplified:             9210
% 3.95/0.98  prop_fo_subsumed:                       0
% 3.95/0.98  prop_solver_time:                       0.
% 3.95/0.98  smt_solver_time:                        0.
% 3.95/0.98  smt_fast_solver_time:                   0.
% 3.95/0.98  prop_fast_solver_time:                  0.
% 3.95/0.98  prop_unsat_core_time:                   0.
% 3.95/0.98  
% 3.95/0.98  ------ QBF
% 3.95/0.98  
% 3.95/0.98  qbf_q_res:                              0
% 3.95/0.98  qbf_num_tautologies:                    0
% 3.95/0.98  qbf_prep_cycles:                        0
% 3.95/0.98  
% 3.95/0.98  ------ BMC1
% 3.95/0.98  
% 3.95/0.98  bmc1_current_bound:                     -1
% 3.95/0.98  bmc1_last_solved_bound:                 -1
% 3.95/0.98  bmc1_unsat_core_size:                   -1
% 3.95/0.98  bmc1_unsat_core_parents_size:           -1
% 3.95/0.98  bmc1_merge_next_fun:                    0
% 3.95/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.95/0.98  
% 3.95/0.98  ------ Instantiation
% 3.95/0.98  
% 3.95/0.98  inst_num_of_clauses:                    1452
% 3.95/0.98  inst_num_in_passive:                    310
% 3.95/0.98  inst_num_in_active:                     440
% 3.95/0.98  inst_num_in_unprocessed:                702
% 3.95/0.98  inst_num_of_loops:                      520
% 3.95/0.98  inst_num_of_learning_restarts:          0
% 3.95/0.98  inst_num_moves_active_passive:          78
% 3.95/0.98  inst_lit_activity:                      0
% 3.95/0.98  inst_lit_activity_moves:                0
% 3.95/0.98  inst_num_tautologies:                   0
% 3.95/0.98  inst_num_prop_implied:                  0
% 3.95/0.98  inst_num_existing_simplified:           0
% 3.95/0.98  inst_num_eq_res_simplified:             0
% 3.95/0.98  inst_num_child_elim:                    0
% 3.95/0.98  inst_num_of_dismatching_blockings:      1826
% 3.95/0.98  inst_num_of_non_proper_insts:           1883
% 3.95/0.98  inst_num_of_duplicates:                 0
% 3.95/0.98  inst_inst_num_from_inst_to_res:         0
% 3.95/0.98  inst_dismatching_checking_time:         0.
% 3.95/0.98  
% 3.95/0.98  ------ Resolution
% 3.95/0.98  
% 3.95/0.98  res_num_of_clauses:                     0
% 3.95/0.98  res_num_in_passive:                     0
% 3.95/0.98  res_num_in_active:                      0
% 3.95/0.98  res_num_of_loops:                       84
% 3.95/0.98  res_forward_subset_subsumed:            860
% 3.95/0.98  res_backward_subset_subsumed:           0
% 3.95/0.98  res_forward_subsumed:                   0
% 3.95/0.98  res_backward_subsumed:                  0
% 3.95/0.98  res_forward_subsumption_resolution:     0
% 3.95/0.98  res_backward_subsumption_resolution:    0
% 3.95/0.98  res_clause_to_clause_subsumption:       2415
% 3.95/0.98  res_orphan_elimination:                 0
% 3.95/0.98  res_tautology_del:                      58
% 3.95/0.98  res_num_eq_res_simplified:              0
% 3.95/0.98  res_num_sel_changes:                    0
% 3.95/0.98  res_moves_from_active_to_pass:          0
% 3.95/0.98  
% 3.95/0.98  ------ Superposition
% 3.95/0.98  
% 3.95/0.98  sup_time_total:                         0.
% 3.95/0.98  sup_time_generating:                    0.
% 3.95/0.98  sup_time_sim_full:                      0.
% 3.95/0.98  sup_time_sim_immed:                     0.
% 3.95/0.98  
% 3.95/0.98  sup_num_of_clauses:                     171
% 3.95/0.98  sup_num_in_active:                      62
% 3.95/0.98  sup_num_in_passive:                     109
% 3.95/0.98  sup_num_of_loops:                       102
% 3.95/0.98  sup_fw_superposition:                   951
% 3.95/0.98  sup_bw_superposition:                   957
% 3.95/0.98  sup_immediate_simplified:               799
% 3.95/0.98  sup_given_eliminated:                   7
% 3.95/0.98  comparisons_done:                       0
% 3.95/0.98  comparisons_avoided:                    6
% 3.95/0.98  
% 3.95/0.98  ------ Simplifications
% 3.95/0.98  
% 3.95/0.98  
% 3.95/0.98  sim_fw_subset_subsumed:                 0
% 3.95/0.98  sim_bw_subset_subsumed:                 0
% 3.95/0.98  sim_fw_subsumed:                        136
% 3.95/0.98  sim_bw_subsumed:                        6
% 3.95/0.98  sim_fw_subsumption_res:                 0
% 3.95/0.98  sim_bw_subsumption_res:                 0
% 3.95/0.98  sim_tautology_del:                      0
% 3.95/0.98  sim_eq_tautology_del:                   101
% 3.95/0.98  sim_eq_res_simp:                        0
% 3.95/0.98  sim_fw_demodulated:                     577
% 3.95/0.98  sim_bw_demodulated:                     45
% 3.95/0.98  sim_light_normalised:                   425
% 3.95/0.98  sim_joinable_taut:                      0
% 3.95/0.98  sim_joinable_simp:                      0
% 3.95/0.98  sim_ac_normalised:                      0
% 3.95/0.98  sim_smt_subsumption:                    0
% 3.95/0.98  
%------------------------------------------------------------------------------
