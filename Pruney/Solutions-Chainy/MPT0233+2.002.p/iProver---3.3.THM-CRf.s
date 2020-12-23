%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:16 EST 2020

% Result     : Theorem 27.97s
% Output     : CNFRefutation 27.97s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 257 expanded)
%              Number of clauses        :   49 (  58 expanded)
%              Number of leaves         :   21 (  69 expanded)
%              Depth                    :   18
%              Number of atoms          :  286 ( 738 expanded)
%              Number of equality atoms :  214 ( 584 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f38,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK1 != sK4
      & sK1 != sK3
      & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( sK1 != sK4
    & sK1 != sK3
    & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f30,f38])).

fof(f71,plain,(
    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f39])).

fof(f22,axiom,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,(
    ! [X0,X1] : k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k2_tarski(X0,X0) ),
    inference(definition_unfolding,[],[f70,f63,f63])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f53,f46])).

fof(f81,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f74,f74])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f55,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f62,f74])).

fof(f76,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f75])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(definition_unfolding,[],[f55,f76])).

fof(f98,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X5,X5),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5)))) != X3 ) ),
    inference(equality_resolution,[],[f88])).

fof(f99,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_xboole_0(k2_tarski(X5,X5),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5))))) ),
    inference(equality_resolution,[],[f98])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f51,f46,f46])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(definition_unfolding,[],[f54,f76])).

fof(f100,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ) ),
    inference(equality_resolution,[],[f89])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f80,plain,(
    ! [X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f64,f76])).

fof(f73,plain,(
    sK1 != sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f86,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(definition_unfolding,[],[f57,f76])).

fof(f94,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X5),k3_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0)))) != X3 ) ),
    inference(equality_resolution,[],[f86])).

fof(f95,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X5),k3_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0))))) ),
    inference(equality_resolution,[],[f94])).

fof(f72,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_920,plain,
    ( r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,plain,
    ( k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_8,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_931,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1793,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_931])).

cnf(c_1842,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1793])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_930,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_15636,plain,
    ( r1_tarski(k2_tarski(X0,X1),X2) != iProver_top
    | r1_tarski(k2_tarski(X0,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_930])).

cnf(c_67942,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),k2_tarski(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_920,c_15636])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_929,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_69843,plain,
    ( k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK3,sK4)) = k2_tarski(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_67942,c_929])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_19,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_922,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1954,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_922])).

cnf(c_70325,plain,
    ( r2_hidden(sK1,k5_xboole_0(k2_tarski(sK3,sK4),k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_69843,c_1954])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_11,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1462,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11,c_0])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1466,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1462,c_4,c_11,c_12])).

cnf(c_70349,plain,
    ( r2_hidden(sK1,k2_tarski(sK3,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_70325,c_12,c_1466])).

cnf(c_1414,plain,
    ( k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)) = k2_tarski(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_22])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_921,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1946,plain,
    ( X0 = X1
    | X2 = X1
    | r2_hidden(X1,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X2),k2_tarski(X0,X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1414,c_921])).

cnf(c_1,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1554,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))) = k2_tarski(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1,c_1,c_1414])).

cnf(c_1947,plain,
    ( X0 = X1
    | X2 = X0
    | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1946,c_1554])).

cnf(c_72038,plain,
    ( sK3 = sK1
    | sK4 = sK1 ),
    inference(superposition,[status(thm)],[c_70349,c_1947])).

cnf(c_23,negated_conjecture,
    ( sK1 != sK4 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_949,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k2_tarski(sK4,sK4),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(sK4,sK4)))))
    | sK1 = X0
    | sK1 = X1
    | sK1 = sK4 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1017,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k2_tarski(sK4,sK4),k5_xboole_0(k2_tarski(X0,sK1),k3_xboole_0(k2_tarski(X0,sK1),k2_tarski(sK4,sK4)))))
    | sK1 = X0
    | sK1 = sK4
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_949])).

cnf(c_1117,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k2_tarski(sK4,sK4),k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK4,sK4)))))
    | sK1 = sK4
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1017])).

cnf(c_17,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X0),k3_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X1))))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1112,plain,
    ( r2_hidden(sK1,k5_xboole_0(k2_tarski(sK4,sK4),k5_xboole_0(k2_tarski(X0,sK1),k3_xboole_0(k2_tarski(X0,sK1),k2_tarski(sK4,sK4))))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1280,plain,
    ( r2_hidden(sK1,k5_xboole_0(k2_tarski(sK4,sK4),k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK4,sK4))))) ),
    inference(instantiation,[status(thm)],[c_1112])).

cnf(c_699,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_957,plain,
    ( sK4 != X0
    | sK1 != X0
    | sK1 = sK4 ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_91796,plain,
    ( sK4 != sK1
    | sK1 = sK4
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_957])).

cnf(c_91870,plain,
    ( sK3 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_72038,c_23,c_1117,c_1280,c_91796])).

cnf(c_24,negated_conjecture,
    ( sK1 != sK3 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_92075,plain,
    ( sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_91870,c_24])).

cnf(c_92076,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_92075])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:44:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.97/3.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.97/3.99  
% 27.97/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.97/3.99  
% 27.97/3.99  ------  iProver source info
% 27.97/3.99  
% 27.97/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.97/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.97/3.99  git: non_committed_changes: false
% 27.97/3.99  git: last_make_outside_of_git: false
% 27.97/3.99  
% 27.97/3.99  ------ 
% 27.97/3.99  
% 27.97/3.99  ------ Input Options
% 27.97/3.99  
% 27.97/3.99  --out_options                           all
% 27.97/3.99  --tptp_safe_out                         true
% 27.97/3.99  --problem_path                          ""
% 27.97/3.99  --include_path                          ""
% 27.97/3.99  --clausifier                            res/vclausify_rel
% 27.97/3.99  --clausifier_options                    ""
% 27.97/3.99  --stdin                                 false
% 27.97/3.99  --stats_out                             all
% 27.97/3.99  
% 27.97/3.99  ------ General Options
% 27.97/3.99  
% 27.97/3.99  --fof                                   false
% 27.97/3.99  --time_out_real                         305.
% 27.97/3.99  --time_out_virtual                      -1.
% 27.97/3.99  --symbol_type_check                     false
% 27.97/3.99  --clausify_out                          false
% 27.97/3.99  --sig_cnt_out                           false
% 27.97/3.99  --trig_cnt_out                          false
% 27.97/3.99  --trig_cnt_out_tolerance                1.
% 27.97/3.99  --trig_cnt_out_sk_spl                   false
% 27.97/3.99  --abstr_cl_out                          false
% 27.97/3.99  
% 27.97/3.99  ------ Global Options
% 27.97/3.99  
% 27.97/3.99  --schedule                              default
% 27.97/3.99  --add_important_lit                     false
% 27.97/3.99  --prop_solver_per_cl                    1000
% 27.97/3.99  --min_unsat_core                        false
% 27.97/3.99  --soft_assumptions                      false
% 27.97/3.99  --soft_lemma_size                       3
% 27.97/3.99  --prop_impl_unit_size                   0
% 27.97/3.99  --prop_impl_unit                        []
% 27.97/3.99  --share_sel_clauses                     true
% 27.97/3.99  --reset_solvers                         false
% 27.97/3.99  --bc_imp_inh                            [conj_cone]
% 27.97/3.99  --conj_cone_tolerance                   3.
% 27.97/3.99  --extra_neg_conj                        none
% 27.97/3.99  --large_theory_mode                     true
% 27.97/3.99  --prolific_symb_bound                   200
% 27.97/3.99  --lt_threshold                          2000
% 27.97/3.99  --clause_weak_htbl                      true
% 27.97/3.99  --gc_record_bc_elim                     false
% 27.97/3.99  
% 27.97/3.99  ------ Preprocessing Options
% 27.97/3.99  
% 27.97/3.99  --preprocessing_flag                    true
% 27.97/3.99  --time_out_prep_mult                    0.1
% 27.97/3.99  --splitting_mode                        input
% 27.97/3.99  --splitting_grd                         true
% 27.97/3.99  --splitting_cvd                         false
% 27.97/3.99  --splitting_cvd_svl                     false
% 27.97/3.99  --splitting_nvd                         32
% 27.97/3.99  --sub_typing                            true
% 27.97/3.99  --prep_gs_sim                           true
% 27.97/3.99  --prep_unflatten                        true
% 27.97/3.99  --prep_res_sim                          true
% 27.97/3.99  --prep_upred                            true
% 27.97/3.99  --prep_sem_filter                       exhaustive
% 27.97/3.99  --prep_sem_filter_out                   false
% 27.97/3.99  --pred_elim                             true
% 27.97/3.99  --res_sim_input                         true
% 27.97/3.99  --eq_ax_congr_red                       true
% 27.97/3.99  --pure_diseq_elim                       true
% 27.97/3.99  --brand_transform                       false
% 27.97/3.99  --non_eq_to_eq                          false
% 27.97/3.99  --prep_def_merge                        true
% 27.97/3.99  --prep_def_merge_prop_impl              false
% 27.97/3.99  --prep_def_merge_mbd                    true
% 27.97/3.99  --prep_def_merge_tr_red                 false
% 27.97/3.99  --prep_def_merge_tr_cl                  false
% 27.97/3.99  --smt_preprocessing                     true
% 27.97/3.99  --smt_ac_axioms                         fast
% 27.97/3.99  --preprocessed_out                      false
% 27.97/3.99  --preprocessed_stats                    false
% 27.97/3.99  
% 27.97/3.99  ------ Abstraction refinement Options
% 27.97/3.99  
% 27.97/3.99  --abstr_ref                             []
% 27.97/3.99  --abstr_ref_prep                        false
% 27.97/3.99  --abstr_ref_until_sat                   false
% 27.97/3.99  --abstr_ref_sig_restrict                funpre
% 27.97/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.97/3.99  --abstr_ref_under                       []
% 27.97/3.99  
% 27.97/3.99  ------ SAT Options
% 27.97/3.99  
% 27.97/3.99  --sat_mode                              false
% 27.97/3.99  --sat_fm_restart_options                ""
% 27.97/3.99  --sat_gr_def                            false
% 27.97/3.99  --sat_epr_types                         true
% 27.97/3.99  --sat_non_cyclic_types                  false
% 27.97/3.99  --sat_finite_models                     false
% 27.97/3.99  --sat_fm_lemmas                         false
% 27.97/3.99  --sat_fm_prep                           false
% 27.97/3.99  --sat_fm_uc_incr                        true
% 27.97/3.99  --sat_out_model                         small
% 27.97/3.99  --sat_out_clauses                       false
% 27.97/3.99  
% 27.97/3.99  ------ QBF Options
% 27.97/3.99  
% 27.97/3.99  --qbf_mode                              false
% 27.97/3.99  --qbf_elim_univ                         false
% 27.97/3.99  --qbf_dom_inst                          none
% 27.97/3.99  --qbf_dom_pre_inst                      false
% 27.97/3.99  --qbf_sk_in                             false
% 27.97/3.99  --qbf_pred_elim                         true
% 27.97/3.99  --qbf_split                             512
% 27.97/3.99  
% 27.97/3.99  ------ BMC1 Options
% 27.97/3.99  
% 27.97/3.99  --bmc1_incremental                      false
% 27.97/3.99  --bmc1_axioms                           reachable_all
% 27.97/3.99  --bmc1_min_bound                        0
% 27.97/3.99  --bmc1_max_bound                        -1
% 27.97/3.99  --bmc1_max_bound_default                -1
% 27.97/3.99  --bmc1_symbol_reachability              true
% 27.97/3.99  --bmc1_property_lemmas                  false
% 27.97/3.99  --bmc1_k_induction                      false
% 27.97/3.99  --bmc1_non_equiv_states                 false
% 27.97/3.99  --bmc1_deadlock                         false
% 27.97/3.99  --bmc1_ucm                              false
% 27.97/3.99  --bmc1_add_unsat_core                   none
% 27.97/3.99  --bmc1_unsat_core_children              false
% 27.97/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.97/3.99  --bmc1_out_stat                         full
% 27.97/3.99  --bmc1_ground_init                      false
% 27.97/3.99  --bmc1_pre_inst_next_state              false
% 27.97/3.99  --bmc1_pre_inst_state                   false
% 27.97/3.99  --bmc1_pre_inst_reach_state             false
% 27.97/3.99  --bmc1_out_unsat_core                   false
% 27.97/3.99  --bmc1_aig_witness_out                  false
% 27.97/3.99  --bmc1_verbose                          false
% 27.97/3.99  --bmc1_dump_clauses_tptp                false
% 27.97/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.97/3.99  --bmc1_dump_file                        -
% 27.97/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.97/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.97/3.99  --bmc1_ucm_extend_mode                  1
% 27.97/3.99  --bmc1_ucm_init_mode                    2
% 27.97/3.99  --bmc1_ucm_cone_mode                    none
% 27.97/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.97/3.99  --bmc1_ucm_relax_model                  4
% 27.97/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.97/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.97/3.99  --bmc1_ucm_layered_model                none
% 27.97/3.99  --bmc1_ucm_max_lemma_size               10
% 27.97/3.99  
% 27.97/3.99  ------ AIG Options
% 27.97/3.99  
% 27.97/3.99  --aig_mode                              false
% 27.97/3.99  
% 27.97/3.99  ------ Instantiation Options
% 27.97/3.99  
% 27.97/3.99  --instantiation_flag                    true
% 27.97/3.99  --inst_sos_flag                         true
% 27.97/3.99  --inst_sos_phase                        true
% 27.97/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.97/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.97/3.99  --inst_lit_sel_side                     num_symb
% 27.97/3.99  --inst_solver_per_active                1400
% 27.97/3.99  --inst_solver_calls_frac                1.
% 27.97/3.99  --inst_passive_queue_type               priority_queues
% 27.97/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.97/3.99  --inst_passive_queues_freq              [25;2]
% 27.97/3.99  --inst_dismatching                      true
% 27.97/3.99  --inst_eager_unprocessed_to_passive     true
% 27.97/3.99  --inst_prop_sim_given                   true
% 27.97/3.99  --inst_prop_sim_new                     false
% 27.97/3.99  --inst_subs_new                         false
% 27.97/3.99  --inst_eq_res_simp                      false
% 27.97/3.99  --inst_subs_given                       false
% 27.97/3.99  --inst_orphan_elimination               true
% 27.97/3.99  --inst_learning_loop_flag               true
% 27.97/3.99  --inst_learning_start                   3000
% 27.97/3.99  --inst_learning_factor                  2
% 27.97/3.99  --inst_start_prop_sim_after_learn       3
% 27.97/3.99  --inst_sel_renew                        solver
% 27.97/3.99  --inst_lit_activity_flag                true
% 27.97/3.99  --inst_restr_to_given                   false
% 27.97/3.99  --inst_activity_threshold               500
% 27.97/3.99  --inst_out_proof                        true
% 27.97/3.99  
% 27.97/3.99  ------ Resolution Options
% 27.97/3.99  
% 27.97/3.99  --resolution_flag                       true
% 27.97/3.99  --res_lit_sel                           adaptive
% 27.97/3.99  --res_lit_sel_side                      none
% 27.97/3.99  --res_ordering                          kbo
% 27.97/3.99  --res_to_prop_solver                    active
% 27.97/3.99  --res_prop_simpl_new                    false
% 27.97/3.99  --res_prop_simpl_given                  true
% 27.97/3.99  --res_passive_queue_type                priority_queues
% 27.97/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.97/3.99  --res_passive_queues_freq               [15;5]
% 27.97/3.99  --res_forward_subs                      full
% 27.97/3.99  --res_backward_subs                     full
% 27.97/3.99  --res_forward_subs_resolution           true
% 27.97/3.99  --res_backward_subs_resolution          true
% 27.97/3.99  --res_orphan_elimination                true
% 27.97/3.99  --res_time_limit                        2.
% 27.97/3.99  --res_out_proof                         true
% 27.97/3.99  
% 27.97/3.99  ------ Superposition Options
% 27.97/3.99  
% 27.97/3.99  --superposition_flag                    true
% 27.97/3.99  --sup_passive_queue_type                priority_queues
% 27.97/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.97/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.97/3.99  --demod_completeness_check              fast
% 27.97/3.99  --demod_use_ground                      true
% 27.97/3.99  --sup_to_prop_solver                    passive
% 27.97/3.99  --sup_prop_simpl_new                    true
% 27.97/3.99  --sup_prop_simpl_given                  true
% 27.97/3.99  --sup_fun_splitting                     true
% 27.97/3.99  --sup_smt_interval                      50000
% 27.97/3.99  
% 27.97/3.99  ------ Superposition Simplification Setup
% 27.97/3.99  
% 27.97/3.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.97/3.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.97/3.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.97/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.97/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.97/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.97/3.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.97/3.99  --sup_immed_triv                        [TrivRules]
% 27.97/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.97/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.97/3.99  --sup_immed_bw_main                     []
% 27.97/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.97/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.97/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.97/3.99  --sup_input_bw                          []
% 27.97/3.99  
% 27.97/3.99  ------ Combination Options
% 27.97/3.99  
% 27.97/3.99  --comb_res_mult                         3
% 27.97/3.99  --comb_sup_mult                         2
% 27.97/3.99  --comb_inst_mult                        10
% 27.97/3.99  
% 27.97/3.99  ------ Debug Options
% 27.97/3.99  
% 27.97/3.99  --dbg_backtrace                         false
% 27.97/3.99  --dbg_dump_prop_clauses                 false
% 27.97/3.99  --dbg_dump_prop_clauses_file            -
% 27.97/3.99  --dbg_out_stat                          false
% 27.97/3.99  ------ Parsing...
% 27.97/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.97/3.99  
% 27.97/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.97/3.99  
% 27.97/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.97/3.99  
% 27.97/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.97/3.99  ------ Proving...
% 27.97/3.99  ------ Problem Properties 
% 27.97/3.99  
% 27.97/3.99  
% 27.97/3.99  clauses                                 25
% 27.97/3.99  conjectures                             3
% 27.97/3.99  EPR                                     5
% 27.97/3.99  Horn                                    23
% 27.97/3.99  unary                                   17
% 27.97/3.99  binary                                  1
% 27.97/3.99  lits                                    43
% 27.97/3.99  lits eq                                 26
% 27.97/3.99  fd_pure                                 0
% 27.97/3.99  fd_pseudo                               0
% 27.97/3.99  fd_cond                                 0
% 27.97/3.99  fd_pseudo_cond                          5
% 27.97/3.99  AC symbols                              0
% 27.97/3.99  
% 27.97/3.99  ------ Schedule dynamic 5 is on 
% 27.97/3.99  
% 27.97/3.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.97/3.99  
% 27.97/3.99  
% 27.97/3.99  ------ 
% 27.97/3.99  Current options:
% 27.97/3.99  ------ 
% 27.97/3.99  
% 27.97/3.99  ------ Input Options
% 27.97/3.99  
% 27.97/3.99  --out_options                           all
% 27.97/3.99  --tptp_safe_out                         true
% 27.97/3.99  --problem_path                          ""
% 27.97/3.99  --include_path                          ""
% 27.97/3.99  --clausifier                            res/vclausify_rel
% 27.97/3.99  --clausifier_options                    ""
% 27.97/3.99  --stdin                                 false
% 27.97/3.99  --stats_out                             all
% 27.97/3.99  
% 27.97/3.99  ------ General Options
% 27.97/3.99  
% 27.97/3.99  --fof                                   false
% 27.97/3.99  --time_out_real                         305.
% 27.97/3.99  --time_out_virtual                      -1.
% 27.97/3.99  --symbol_type_check                     false
% 27.97/3.99  --clausify_out                          false
% 27.97/3.99  --sig_cnt_out                           false
% 27.97/3.99  --trig_cnt_out                          false
% 27.97/3.99  --trig_cnt_out_tolerance                1.
% 27.97/3.99  --trig_cnt_out_sk_spl                   false
% 27.97/3.99  --abstr_cl_out                          false
% 27.97/3.99  
% 27.97/3.99  ------ Global Options
% 27.97/3.99  
% 27.97/3.99  --schedule                              default
% 27.97/3.99  --add_important_lit                     false
% 27.97/3.99  --prop_solver_per_cl                    1000
% 27.97/3.99  --min_unsat_core                        false
% 27.97/3.99  --soft_assumptions                      false
% 27.97/3.99  --soft_lemma_size                       3
% 27.97/3.99  --prop_impl_unit_size                   0
% 27.97/3.99  --prop_impl_unit                        []
% 27.97/3.99  --share_sel_clauses                     true
% 27.97/3.99  --reset_solvers                         false
% 27.97/3.99  --bc_imp_inh                            [conj_cone]
% 27.97/3.99  --conj_cone_tolerance                   3.
% 27.97/3.99  --extra_neg_conj                        none
% 27.97/3.99  --large_theory_mode                     true
% 27.97/3.99  --prolific_symb_bound                   200
% 27.97/3.99  --lt_threshold                          2000
% 27.97/3.99  --clause_weak_htbl                      true
% 27.97/3.99  --gc_record_bc_elim                     false
% 27.97/3.99  
% 27.97/3.99  ------ Preprocessing Options
% 27.97/3.99  
% 27.97/3.99  --preprocessing_flag                    true
% 27.97/3.99  --time_out_prep_mult                    0.1
% 27.97/3.99  --splitting_mode                        input
% 27.97/3.99  --splitting_grd                         true
% 27.97/3.99  --splitting_cvd                         false
% 27.97/3.99  --splitting_cvd_svl                     false
% 27.97/3.99  --splitting_nvd                         32
% 27.97/3.99  --sub_typing                            true
% 27.97/3.99  --prep_gs_sim                           true
% 27.97/3.99  --prep_unflatten                        true
% 27.97/3.99  --prep_res_sim                          true
% 27.97/3.99  --prep_upred                            true
% 27.97/3.99  --prep_sem_filter                       exhaustive
% 27.97/3.99  --prep_sem_filter_out                   false
% 27.97/3.99  --pred_elim                             true
% 27.97/3.99  --res_sim_input                         true
% 27.97/3.99  --eq_ax_congr_red                       true
% 27.97/3.99  --pure_diseq_elim                       true
% 27.97/3.99  --brand_transform                       false
% 27.97/3.99  --non_eq_to_eq                          false
% 27.97/3.99  --prep_def_merge                        true
% 27.97/3.99  --prep_def_merge_prop_impl              false
% 27.97/3.99  --prep_def_merge_mbd                    true
% 27.97/3.99  --prep_def_merge_tr_red                 false
% 27.97/3.99  --prep_def_merge_tr_cl                  false
% 27.97/3.99  --smt_preprocessing                     true
% 27.97/3.99  --smt_ac_axioms                         fast
% 27.97/3.99  --preprocessed_out                      false
% 27.97/3.99  --preprocessed_stats                    false
% 27.97/3.99  
% 27.97/3.99  ------ Abstraction refinement Options
% 27.97/3.99  
% 27.97/3.99  --abstr_ref                             []
% 27.97/3.99  --abstr_ref_prep                        false
% 27.97/3.99  --abstr_ref_until_sat                   false
% 27.97/3.99  --abstr_ref_sig_restrict                funpre
% 27.97/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.97/3.99  --abstr_ref_under                       []
% 27.97/3.99  
% 27.97/3.99  ------ SAT Options
% 27.97/3.99  
% 27.97/3.99  --sat_mode                              false
% 27.97/3.99  --sat_fm_restart_options                ""
% 27.97/3.99  --sat_gr_def                            false
% 27.97/3.99  --sat_epr_types                         true
% 27.97/3.99  --sat_non_cyclic_types                  false
% 27.97/3.99  --sat_finite_models                     false
% 27.97/3.99  --sat_fm_lemmas                         false
% 27.97/3.99  --sat_fm_prep                           false
% 27.97/3.99  --sat_fm_uc_incr                        true
% 27.97/3.99  --sat_out_model                         small
% 27.97/3.99  --sat_out_clauses                       false
% 27.97/3.99  
% 27.97/3.99  ------ QBF Options
% 27.97/3.99  
% 27.97/3.99  --qbf_mode                              false
% 27.97/3.99  --qbf_elim_univ                         false
% 27.97/3.99  --qbf_dom_inst                          none
% 27.97/3.99  --qbf_dom_pre_inst                      false
% 27.97/3.99  --qbf_sk_in                             false
% 27.97/3.99  --qbf_pred_elim                         true
% 27.97/3.99  --qbf_split                             512
% 27.97/3.99  
% 27.97/3.99  ------ BMC1 Options
% 27.97/3.99  
% 27.97/3.99  --bmc1_incremental                      false
% 27.97/3.99  --bmc1_axioms                           reachable_all
% 27.97/3.99  --bmc1_min_bound                        0
% 27.97/3.99  --bmc1_max_bound                        -1
% 27.97/3.99  --bmc1_max_bound_default                -1
% 27.97/3.99  --bmc1_symbol_reachability              true
% 27.97/3.99  --bmc1_property_lemmas                  false
% 27.97/3.99  --bmc1_k_induction                      false
% 27.97/3.99  --bmc1_non_equiv_states                 false
% 27.97/3.99  --bmc1_deadlock                         false
% 27.97/3.99  --bmc1_ucm                              false
% 27.97/3.99  --bmc1_add_unsat_core                   none
% 27.97/3.99  --bmc1_unsat_core_children              false
% 27.97/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.97/3.99  --bmc1_out_stat                         full
% 27.97/3.99  --bmc1_ground_init                      false
% 27.97/3.99  --bmc1_pre_inst_next_state              false
% 27.97/3.99  --bmc1_pre_inst_state                   false
% 27.97/3.99  --bmc1_pre_inst_reach_state             false
% 27.97/3.99  --bmc1_out_unsat_core                   false
% 27.97/3.99  --bmc1_aig_witness_out                  false
% 27.97/3.99  --bmc1_verbose                          false
% 27.97/3.99  --bmc1_dump_clauses_tptp                false
% 27.97/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.97/3.99  --bmc1_dump_file                        -
% 27.97/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.97/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.97/3.99  --bmc1_ucm_extend_mode                  1
% 27.97/3.99  --bmc1_ucm_init_mode                    2
% 27.97/3.99  --bmc1_ucm_cone_mode                    none
% 27.97/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.97/3.99  --bmc1_ucm_relax_model                  4
% 27.97/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.97/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.97/3.99  --bmc1_ucm_layered_model                none
% 27.97/3.99  --bmc1_ucm_max_lemma_size               10
% 27.97/3.99  
% 27.97/3.99  ------ AIG Options
% 27.97/3.99  
% 27.97/3.99  --aig_mode                              false
% 27.97/3.99  
% 27.97/3.99  ------ Instantiation Options
% 27.97/3.99  
% 27.97/3.99  --instantiation_flag                    true
% 27.97/3.99  --inst_sos_flag                         true
% 27.97/3.99  --inst_sos_phase                        true
% 27.97/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.97/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.97/3.99  --inst_lit_sel_side                     none
% 27.97/3.99  --inst_solver_per_active                1400
% 27.97/3.99  --inst_solver_calls_frac                1.
% 27.97/3.99  --inst_passive_queue_type               priority_queues
% 27.97/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.97/3.99  --inst_passive_queues_freq              [25;2]
% 27.97/3.99  --inst_dismatching                      true
% 27.97/3.99  --inst_eager_unprocessed_to_passive     true
% 27.97/4.00  --inst_prop_sim_given                   true
% 27.97/4.00  --inst_prop_sim_new                     false
% 27.97/4.00  --inst_subs_new                         false
% 27.97/4.00  --inst_eq_res_simp                      false
% 27.97/4.00  --inst_subs_given                       false
% 27.97/4.00  --inst_orphan_elimination               true
% 27.97/4.00  --inst_learning_loop_flag               true
% 27.97/4.00  --inst_learning_start                   3000
% 27.97/4.00  --inst_learning_factor                  2
% 27.97/4.00  --inst_start_prop_sim_after_learn       3
% 27.97/4.00  --inst_sel_renew                        solver
% 27.97/4.00  --inst_lit_activity_flag                true
% 27.97/4.00  --inst_restr_to_given                   false
% 27.97/4.00  --inst_activity_threshold               500
% 27.97/4.00  --inst_out_proof                        true
% 27.97/4.00  
% 27.97/4.00  ------ Resolution Options
% 27.97/4.00  
% 27.97/4.00  --resolution_flag                       false
% 27.97/4.00  --res_lit_sel                           adaptive
% 27.97/4.00  --res_lit_sel_side                      none
% 27.97/4.00  --res_ordering                          kbo
% 27.97/4.00  --res_to_prop_solver                    active
% 27.97/4.00  --res_prop_simpl_new                    false
% 27.97/4.00  --res_prop_simpl_given                  true
% 27.97/4.00  --res_passive_queue_type                priority_queues
% 27.97/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.97/4.00  --res_passive_queues_freq               [15;5]
% 27.97/4.00  --res_forward_subs                      full
% 27.97/4.00  --res_backward_subs                     full
% 27.97/4.00  --res_forward_subs_resolution           true
% 27.97/4.00  --res_backward_subs_resolution          true
% 27.97/4.00  --res_orphan_elimination                true
% 27.97/4.00  --res_time_limit                        2.
% 27.97/4.00  --res_out_proof                         true
% 27.97/4.00  
% 27.97/4.00  ------ Superposition Options
% 27.97/4.00  
% 27.97/4.00  --superposition_flag                    true
% 27.97/4.00  --sup_passive_queue_type                priority_queues
% 27.97/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.97/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.97/4.00  --demod_completeness_check              fast
% 27.97/4.00  --demod_use_ground                      true
% 27.97/4.00  --sup_to_prop_solver                    passive
% 27.97/4.00  --sup_prop_simpl_new                    true
% 27.97/4.00  --sup_prop_simpl_given                  true
% 27.97/4.00  --sup_fun_splitting                     true
% 27.97/4.00  --sup_smt_interval                      50000
% 27.97/4.00  
% 27.97/4.00  ------ Superposition Simplification Setup
% 27.97/4.00  
% 27.97/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.97/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.97/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.97/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.97/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.97/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.97/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.97/4.00  --sup_immed_triv                        [TrivRules]
% 27.97/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.97/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.97/4.00  --sup_immed_bw_main                     []
% 27.97/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.97/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.97/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.97/4.00  --sup_input_bw                          []
% 27.97/4.00  
% 27.97/4.00  ------ Combination Options
% 27.97/4.00  
% 27.97/4.00  --comb_res_mult                         3
% 27.97/4.00  --comb_sup_mult                         2
% 27.97/4.00  --comb_inst_mult                        10
% 27.97/4.00  
% 27.97/4.00  ------ Debug Options
% 27.97/4.00  
% 27.97/4.00  --dbg_backtrace                         false
% 27.97/4.00  --dbg_dump_prop_clauses                 false
% 27.97/4.00  --dbg_dump_prop_clauses_file            -
% 27.97/4.00  --dbg_out_stat                          false
% 27.97/4.00  
% 27.97/4.00  
% 27.97/4.00  
% 27.97/4.00  
% 27.97/4.00  ------ Proving...
% 27.97/4.00  
% 27.97/4.00  
% 27.97/4.00  % SZS status Theorem for theBenchmark.p
% 27.97/4.00  
% 27.97/4.00   Resolution empty clause
% 27.97/4.00  
% 27.97/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.97/4.00  
% 27.97/4.00  fof(f23,conjecture,(
% 27.97/4.00    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f24,negated_conjecture,(
% 27.97/4.00    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 27.97/4.00    inference(negated_conjecture,[],[f23])).
% 27.97/4.00  
% 27.97/4.00  fof(f30,plain,(
% 27.97/4.00    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 27.97/4.00    inference(ennf_transformation,[],[f24])).
% 27.97/4.00  
% 27.97/4.00  fof(f38,plain,(
% 27.97/4.00    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 27.97/4.00    introduced(choice_axiom,[])).
% 27.97/4.00  
% 27.97/4.00  fof(f39,plain,(
% 27.97/4.00    sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 27.97/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f30,f38])).
% 27.97/4.00  
% 27.97/4.00  fof(f71,plain,(
% 27.97/4.00    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 27.97/4.00    inference(cnf_transformation,[],[f39])).
% 27.97/4.00  
% 27.97/4.00  fof(f22,axiom,(
% 27.97/4.00    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f70,plain,(
% 27.97/4.00    ( ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f22])).
% 27.97/4.00  
% 27.97/4.00  fof(f15,axiom,(
% 27.97/4.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f63,plain,(
% 27.97/4.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f15])).
% 27.97/4.00  
% 27.97/4.00  fof(f91,plain,(
% 27.97/4.00    ( ! [X0,X1] : (k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k2_tarski(X0,X0)) )),
% 27.97/4.00    inference(definition_unfolding,[],[f70,f63,f63])).
% 27.97/4.00  
% 27.97/4.00  fof(f2,axiom,(
% 27.97/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f41,plain,(
% 27.97/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f2])).
% 27.97/4.00  
% 27.97/4.00  fof(f6,axiom,(
% 27.97/4.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f47,plain,(
% 27.97/4.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f6])).
% 27.97/4.00  
% 27.97/4.00  fof(f7,axiom,(
% 27.97/4.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f26,plain,(
% 27.97/4.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 27.97/4.00    inference(ennf_transformation,[],[f7])).
% 27.97/4.00  
% 27.97/4.00  fof(f27,plain,(
% 27.97/4.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 27.97/4.00    inference(flattening,[],[f26])).
% 27.97/4.00  
% 27.97/4.00  fof(f48,plain,(
% 27.97/4.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f27])).
% 27.97/4.00  
% 27.97/4.00  fof(f8,axiom,(
% 27.97/4.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f28,plain,(
% 27.97/4.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 27.97/4.00    inference(ennf_transformation,[],[f8])).
% 27.97/4.00  
% 27.97/4.00  fof(f49,plain,(
% 27.97/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f28])).
% 27.97/4.00  
% 27.97/4.00  fof(f1,axiom,(
% 27.97/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f40,plain,(
% 27.97/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f1])).
% 27.97/4.00  
% 27.97/4.00  fof(f12,axiom,(
% 27.97/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f53,plain,(
% 27.97/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 27.97/4.00    inference(cnf_transformation,[],[f12])).
% 27.97/4.00  
% 27.97/4.00  fof(f5,axiom,(
% 27.97/4.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f46,plain,(
% 27.97/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.97/4.00    inference(cnf_transformation,[],[f5])).
% 27.97/4.00  
% 27.97/4.00  fof(f74,plain,(
% 27.97/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 27.97/4.00    inference(definition_unfolding,[],[f53,f46])).
% 27.97/4.00  
% 27.97/4.00  fof(f81,plain,(
% 27.97/4.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 27.97/4.00    inference(definition_unfolding,[],[f40,f74,f74])).
% 27.97/4.00  
% 27.97/4.00  fof(f13,axiom,(
% 27.97/4.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f29,plain,(
% 27.97/4.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 27.97/4.00    inference(ennf_transformation,[],[f13])).
% 27.97/4.00  
% 27.97/4.00  fof(f33,plain,(
% 27.97/4.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 27.97/4.00    inference(nnf_transformation,[],[f29])).
% 27.97/4.00  
% 27.97/4.00  fof(f34,plain,(
% 27.97/4.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 27.97/4.00    inference(flattening,[],[f33])).
% 27.97/4.00  
% 27.97/4.00  fof(f35,plain,(
% 27.97/4.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 27.97/4.00    inference(rectify,[],[f34])).
% 27.97/4.00  
% 27.97/4.00  fof(f36,plain,(
% 27.97/4.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 27.97/4.00    introduced(choice_axiom,[])).
% 27.97/4.00  
% 27.97/4.00  fof(f37,plain,(
% 27.97/4.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 27.97/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 27.97/4.00  
% 27.97/4.00  fof(f55,plain,(
% 27.97/4.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 27.97/4.00    inference(cnf_transformation,[],[f37])).
% 27.97/4.00  
% 27.97/4.00  fof(f17,axiom,(
% 27.97/4.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f65,plain,(
% 27.97/4.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f17])).
% 27.97/4.00  
% 27.97/4.00  fof(f14,axiom,(
% 27.97/4.00    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f62,plain,(
% 27.97/4.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f14])).
% 27.97/4.00  
% 27.97/4.00  fof(f75,plain,(
% 27.97/4.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) = k2_enumset1(X0,X1,X2,X3)) )),
% 27.97/4.00    inference(definition_unfolding,[],[f62,f74])).
% 27.97/4.00  
% 27.97/4.00  fof(f76,plain,(
% 27.97/4.00    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2)) )),
% 27.97/4.00    inference(definition_unfolding,[],[f65,f75])).
% 27.97/4.00  
% 27.97/4.00  fof(f88,plain,(
% 27.97/4.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3) )),
% 27.97/4.00    inference(definition_unfolding,[],[f55,f76])).
% 27.97/4.00  
% 27.97/4.00  fof(f98,plain,(
% 27.97/4.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X5,X5),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5)))) != X3) )),
% 27.97/4.00    inference(equality_resolution,[],[f88])).
% 27.97/4.00  
% 27.97/4.00  fof(f99,plain,(
% 27.97/4.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_xboole_0(k2_tarski(X5,X5),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5)))))) )),
% 27.97/4.00    inference(equality_resolution,[],[f98])).
% 27.97/4.00  
% 27.97/4.00  fof(f11,axiom,(
% 27.97/4.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f52,plain,(
% 27.97/4.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.97/4.00    inference(cnf_transformation,[],[f11])).
% 27.97/4.00  
% 27.97/4.00  fof(f9,axiom,(
% 27.97/4.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f50,plain,(
% 27.97/4.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 27.97/4.00    inference(cnf_transformation,[],[f9])).
% 27.97/4.00  
% 27.97/4.00  fof(f10,axiom,(
% 27.97/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f51,plain,(
% 27.97/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.97/4.00    inference(cnf_transformation,[],[f10])).
% 27.97/4.00  
% 27.97/4.00  fof(f79,plain,(
% 27.97/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 27.97/4.00    inference(definition_unfolding,[],[f51,f46,f46])).
% 27.97/4.00  
% 27.97/4.00  fof(f3,axiom,(
% 27.97/4.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f25,plain,(
% 27.97/4.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 27.97/4.00    inference(rectify,[],[f3])).
% 27.97/4.00  
% 27.97/4.00  fof(f42,plain,(
% 27.97/4.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 27.97/4.00    inference(cnf_transformation,[],[f25])).
% 27.97/4.00  
% 27.97/4.00  fof(f54,plain,(
% 27.97/4.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 27.97/4.00    inference(cnf_transformation,[],[f37])).
% 27.97/4.00  
% 27.97/4.00  fof(f89,plain,(
% 27.97/4.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3) )),
% 27.97/4.00    inference(definition_unfolding,[],[f54,f76])).
% 27.97/4.00  
% 27.97/4.00  fof(f100,plain,(
% 27.97/4.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))))) )),
% 27.97/4.00    inference(equality_resolution,[],[f89])).
% 27.97/4.00  
% 27.97/4.00  fof(f16,axiom,(
% 27.97/4.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f64,plain,(
% 27.97/4.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f16])).
% 27.97/4.00  
% 27.97/4.00  fof(f80,plain,(
% 27.97/4.00    ( ! [X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1)) )),
% 27.97/4.00    inference(definition_unfolding,[],[f64,f76])).
% 27.97/4.00  
% 27.97/4.00  fof(f73,plain,(
% 27.97/4.00    sK1 != sK4),
% 27.97/4.00    inference(cnf_transformation,[],[f39])).
% 27.97/4.00  
% 27.97/4.00  fof(f57,plain,(
% 27.97/4.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 27.97/4.00    inference(cnf_transformation,[],[f37])).
% 27.97/4.00  
% 27.97/4.00  fof(f86,plain,(
% 27.97/4.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3) )),
% 27.97/4.00    inference(definition_unfolding,[],[f57,f76])).
% 27.97/4.00  
% 27.97/4.00  fof(f94,plain,(
% 27.97/4.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X5),k3_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0)))) != X3) )),
% 27.97/4.00    inference(equality_resolution,[],[f86])).
% 27.97/4.00  
% 27.97/4.00  fof(f95,plain,(
% 27.97/4.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X5),k3_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0)))))) )),
% 27.97/4.00    inference(equality_resolution,[],[f94])).
% 27.97/4.00  
% 27.97/4.00  fof(f72,plain,(
% 27.97/4.00    sK1 != sK3),
% 27.97/4.00    inference(cnf_transformation,[],[f39])).
% 27.97/4.00  
% 27.97/4.00  cnf(c_25,negated_conjecture,
% 27.97/4.00      ( r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
% 27.97/4.00      inference(cnf_transformation,[],[f71]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_920,plain,
% 27.97/4.00      ( r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_22,plain,
% 27.97/4.00      ( k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k2_tarski(X0,X0) ),
% 27.97/4.00      inference(cnf_transformation,[],[f91]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3,plain,
% 27.97/4.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 27.97/4.00      inference(cnf_transformation,[],[f41]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_8,plain,
% 27.97/4.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 27.97/4.00      inference(cnf_transformation,[],[f47]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_931,plain,
% 27.97/4.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1793,plain,
% 27.97/4.00      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_3,c_931]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1842,plain,
% 27.97/4.00      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) = iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_22,c_1793]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_9,plain,
% 27.97/4.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 27.97/4.00      inference(cnf_transformation,[],[f48]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_930,plain,
% 27.97/4.00      ( r1_tarski(X0,X1) != iProver_top
% 27.97/4.00      | r1_tarski(X1,X2) != iProver_top
% 27.97/4.00      | r1_tarski(X0,X2) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_15636,plain,
% 27.97/4.00      ( r1_tarski(k2_tarski(X0,X1),X2) != iProver_top
% 27.97/4.00      | r1_tarski(k2_tarski(X0,X0),X2) = iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_1842,c_930]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_67942,plain,
% 27.97/4.00      ( r1_tarski(k2_tarski(sK1,sK1),k2_tarski(sK3,sK4)) = iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_920,c_15636]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_10,plain,
% 27.97/4.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 27.97/4.00      inference(cnf_transformation,[],[f49]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_929,plain,
% 27.97/4.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_69843,plain,
% 27.97/4.00      ( k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK3,sK4)) = k2_tarski(sK1,sK1) ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_67942,c_929]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_2,plain,
% 27.97/4.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 27.97/4.00      inference(cnf_transformation,[],[f81]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_19,plain,
% 27.97/4.00      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ),
% 27.97/4.00      inference(cnf_transformation,[],[f99]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_922,plain,
% 27.97/4.00      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1954,plain,
% 27.97/4.00      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2))))) = iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_2,c_922]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_70325,plain,
% 27.97/4.00      ( r2_hidden(sK1,k5_xboole_0(k2_tarski(sK3,sK4),k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)))) = iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_69843,c_1954]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_12,plain,
% 27.97/4.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.97/4.00      inference(cnf_transformation,[],[f52]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_11,plain,
% 27.97/4.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 27.97/4.00      inference(cnf_transformation,[],[f50]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_0,plain,
% 27.97/4.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 27.97/4.00      inference(cnf_transformation,[],[f79]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1462,plain,
% 27.97/4.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_11,c_0]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_4,plain,
% 27.97/4.00      ( k3_xboole_0(X0,X0) = X0 ),
% 27.97/4.00      inference(cnf_transformation,[],[f42]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1466,plain,
% 27.97/4.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.97/4.00      inference(light_normalisation,[status(thm)],[c_1462,c_4,c_11,c_12]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_70349,plain,
% 27.97/4.00      ( r2_hidden(sK1,k2_tarski(sK3,sK4)) = iProver_top ),
% 27.97/4.00      inference(demodulation,[status(thm)],[c_70325,c_12,c_1466]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1414,plain,
% 27.97/4.00      ( k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)) = k2_tarski(X0,X0) ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_3,c_22]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_20,plain,
% 27.97/4.00      ( ~ r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))))
% 27.97/4.00      | X0 = X1
% 27.97/4.00      | X0 = X2
% 27.97/4.00      | X0 = X3 ),
% 27.97/4.00      inference(cnf_transformation,[],[f100]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_921,plain,
% 27.97/4.00      ( X0 = X1
% 27.97/4.00      | X0 = X2
% 27.97/4.00      | X0 = X3
% 27.97/4.00      | r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))) != iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1946,plain,
% 27.97/4.00      ( X0 = X1
% 27.97/4.00      | X2 = X1
% 27.97/4.00      | r2_hidden(X1,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X2),k2_tarski(X0,X0)))) != iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_1414,c_921]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1,plain,
% 27.97/4.00      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
% 27.97/4.00      inference(cnf_transformation,[],[f80]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1554,plain,
% 27.97/4.00      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))) = k2_tarski(X0,X1) ),
% 27.97/4.00      inference(light_normalisation,[status(thm)],[c_1,c_1,c_1414]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1947,plain,
% 27.97/4.00      ( X0 = X1 | X2 = X0 | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
% 27.97/4.00      inference(demodulation,[status(thm)],[c_1946,c_1554]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_72038,plain,
% 27.97/4.00      ( sK3 = sK1 | sK4 = sK1 ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_70349,c_1947]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_23,negated_conjecture,
% 27.97/4.00      ( sK1 != sK4 ),
% 27.97/4.00      inference(cnf_transformation,[],[f73]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_949,plain,
% 27.97/4.00      ( ~ r2_hidden(sK1,k5_xboole_0(k2_tarski(sK4,sK4),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(sK4,sK4)))))
% 27.97/4.00      | sK1 = X0
% 27.97/4.00      | sK1 = X1
% 27.97/4.00      | sK1 = sK4 ),
% 27.97/4.00      inference(instantiation,[status(thm)],[c_20]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1017,plain,
% 27.97/4.00      ( ~ r2_hidden(sK1,k5_xboole_0(k2_tarski(sK4,sK4),k5_xboole_0(k2_tarski(X0,sK1),k3_xboole_0(k2_tarski(X0,sK1),k2_tarski(sK4,sK4)))))
% 27.97/4.00      | sK1 = X0
% 27.97/4.00      | sK1 = sK4
% 27.97/4.00      | sK1 = sK1 ),
% 27.97/4.00      inference(instantiation,[status(thm)],[c_949]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1117,plain,
% 27.97/4.00      ( ~ r2_hidden(sK1,k5_xboole_0(k2_tarski(sK4,sK4),k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK4,sK4)))))
% 27.97/4.00      | sK1 = sK4
% 27.97/4.00      | sK1 = sK1 ),
% 27.97/4.00      inference(instantiation,[status(thm)],[c_1017]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_17,plain,
% 27.97/4.00      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X0),k3_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X1))))) ),
% 27.97/4.00      inference(cnf_transformation,[],[f95]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1112,plain,
% 27.97/4.00      ( r2_hidden(sK1,k5_xboole_0(k2_tarski(sK4,sK4),k5_xboole_0(k2_tarski(X0,sK1),k3_xboole_0(k2_tarski(X0,sK1),k2_tarski(sK4,sK4))))) ),
% 27.97/4.00      inference(instantiation,[status(thm)],[c_17]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1280,plain,
% 27.97/4.00      ( r2_hidden(sK1,k5_xboole_0(k2_tarski(sK4,sK4),k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK4,sK4))))) ),
% 27.97/4.00      inference(instantiation,[status(thm)],[c_1112]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_699,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_957,plain,
% 27.97/4.00      ( sK4 != X0 | sK1 != X0 | sK1 = sK4 ),
% 27.97/4.00      inference(instantiation,[status(thm)],[c_699]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_91796,plain,
% 27.97/4.00      ( sK4 != sK1 | sK1 = sK4 | sK1 != sK1 ),
% 27.97/4.00      inference(instantiation,[status(thm)],[c_957]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_91870,plain,
% 27.97/4.00      ( sK3 = sK1 ),
% 27.97/4.00      inference(global_propositional_subsumption,
% 27.97/4.00                [status(thm)],
% 27.97/4.00                [c_72038,c_23,c_1117,c_1280,c_91796]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_24,negated_conjecture,
% 27.97/4.00      ( sK1 != sK3 ),
% 27.97/4.00      inference(cnf_transformation,[],[f72]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_92075,plain,
% 27.97/4.00      ( sK1 != sK1 ),
% 27.97/4.00      inference(demodulation,[status(thm)],[c_91870,c_24]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_92076,plain,
% 27.97/4.00      ( $false ),
% 27.97/4.00      inference(equality_resolution_simp,[status(thm)],[c_92075]) ).
% 27.97/4.00  
% 27.97/4.00  
% 27.97/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.97/4.00  
% 27.97/4.00  ------                               Statistics
% 27.97/4.00  
% 27.97/4.00  ------ General
% 27.97/4.00  
% 27.97/4.00  abstr_ref_over_cycles:                  0
% 27.97/4.00  abstr_ref_under_cycles:                 0
% 27.97/4.00  gc_basic_clause_elim:                   0
% 27.97/4.00  forced_gc_time:                         0
% 27.97/4.00  parsing_time:                           0.008
% 27.97/4.00  unif_index_cands_time:                  0.
% 27.97/4.00  unif_index_add_time:                    0.
% 27.97/4.00  orderings_time:                         0.
% 27.97/4.00  out_proof_time:                         0.011
% 27.97/4.00  total_time:                             3.353
% 27.97/4.00  num_of_symbols:                         43
% 27.97/4.00  num_of_terms:                           137072
% 27.97/4.00  
% 27.97/4.00  ------ Preprocessing
% 27.97/4.00  
% 27.97/4.00  num_of_splits:                          0
% 27.97/4.00  num_of_split_atoms:                     0
% 27.97/4.00  num_of_reused_defs:                     0
% 27.97/4.00  num_eq_ax_congr_red:                    36
% 27.97/4.00  num_of_sem_filtered_clauses:            1
% 27.97/4.00  num_of_subtypes:                        0
% 27.97/4.00  monotx_restored_types:                  0
% 27.97/4.00  sat_num_of_epr_types:                   0
% 27.97/4.00  sat_num_of_non_cyclic_types:            0
% 27.97/4.00  sat_guarded_non_collapsed_types:        0
% 27.97/4.00  num_pure_diseq_elim:                    0
% 27.97/4.00  simp_replaced_by:                       0
% 27.97/4.00  res_preprocessed:                       115
% 27.97/4.00  prep_upred:                             0
% 27.97/4.00  prep_unflattend:                        28
% 27.97/4.00  smt_new_axioms:                         0
% 27.97/4.00  pred_elim_cands:                        2
% 27.97/4.00  pred_elim:                              0
% 27.97/4.00  pred_elim_cl:                           0
% 27.97/4.00  pred_elim_cycles:                       2
% 27.97/4.00  merged_defs:                            0
% 27.97/4.00  merged_defs_ncl:                        0
% 27.97/4.00  bin_hyper_res:                          0
% 27.97/4.00  prep_cycles:                            4
% 27.97/4.00  pred_elim_time:                         0.008
% 27.97/4.00  splitting_time:                         0.
% 27.97/4.00  sem_filter_time:                        0.
% 27.97/4.00  monotx_time:                            0.
% 27.97/4.00  subtype_inf_time:                       0.
% 27.97/4.00  
% 27.97/4.00  ------ Problem properties
% 27.97/4.00  
% 27.97/4.00  clauses:                                25
% 27.97/4.00  conjectures:                            3
% 27.97/4.00  epr:                                    5
% 27.97/4.00  horn:                                   23
% 27.97/4.00  ground:                                 3
% 27.97/4.00  unary:                                  17
% 27.97/4.00  binary:                                 1
% 27.97/4.00  lits:                                   43
% 27.97/4.00  lits_eq:                                26
% 27.97/4.00  fd_pure:                                0
% 27.97/4.00  fd_pseudo:                              0
% 27.97/4.00  fd_cond:                                0
% 27.97/4.00  fd_pseudo_cond:                         5
% 27.97/4.00  ac_symbols:                             0
% 27.97/4.00  
% 27.97/4.00  ------ Propositional Solver
% 27.97/4.00  
% 27.97/4.00  prop_solver_calls:                      34
% 27.97/4.00  prop_fast_solver_calls:                 1600
% 27.97/4.00  smt_solver_calls:                       0
% 27.97/4.00  smt_fast_solver_calls:                  0
% 27.97/4.00  prop_num_of_clauses:                    32493
% 27.97/4.00  prop_preprocess_simplified:             58009
% 27.97/4.00  prop_fo_subsumed:                       4
% 27.97/4.00  prop_solver_time:                       0.
% 27.97/4.00  smt_solver_time:                        0.
% 27.97/4.00  smt_fast_solver_time:                   0.
% 27.97/4.00  prop_fast_solver_time:                  0.
% 27.97/4.00  prop_unsat_core_time:                   0.
% 27.97/4.00  
% 27.97/4.00  ------ QBF
% 27.97/4.00  
% 27.97/4.00  qbf_q_res:                              0
% 27.97/4.00  qbf_num_tautologies:                    0
% 27.97/4.00  qbf_prep_cycles:                        0
% 27.97/4.00  
% 27.97/4.00  ------ BMC1
% 27.97/4.00  
% 27.97/4.00  bmc1_current_bound:                     -1
% 27.97/4.00  bmc1_last_solved_bound:                 -1
% 27.97/4.00  bmc1_unsat_core_size:                   -1
% 27.97/4.00  bmc1_unsat_core_parents_size:           -1
% 27.97/4.00  bmc1_merge_next_fun:                    0
% 27.97/4.00  bmc1_unsat_core_clauses_time:           0.
% 27.97/4.00  
% 27.97/4.00  ------ Instantiation
% 27.97/4.00  
% 27.97/4.00  inst_num_of_clauses:                    7031
% 27.97/4.00  inst_num_in_passive:                    5160
% 27.97/4.00  inst_num_in_active:                     1841
% 27.97/4.00  inst_num_in_unprocessed:                31
% 27.97/4.00  inst_num_of_loops:                      1960
% 27.97/4.00  inst_num_of_learning_restarts:          0
% 27.97/4.00  inst_num_moves_active_passive:          117
% 27.97/4.00  inst_lit_activity:                      0
% 27.97/4.00  inst_lit_activity_moves:                0
% 27.97/4.00  inst_num_tautologies:                   0
% 27.97/4.00  inst_num_prop_implied:                  0
% 27.97/4.00  inst_num_existing_simplified:           0
% 27.97/4.00  inst_num_eq_res_simplified:             0
% 27.97/4.00  inst_num_child_elim:                    0
% 27.97/4.00  inst_num_of_dismatching_blockings:      13880
% 27.97/4.00  inst_num_of_non_proper_insts:           6957
% 27.97/4.00  inst_num_of_duplicates:                 0
% 27.97/4.00  inst_inst_num_from_inst_to_res:         0
% 27.97/4.00  inst_dismatching_checking_time:         0.
% 27.97/4.00  
% 27.97/4.00  ------ Resolution
% 27.97/4.00  
% 27.97/4.00  res_num_of_clauses:                     0
% 27.97/4.00  res_num_in_passive:                     0
% 27.97/4.00  res_num_in_active:                      0
% 27.97/4.00  res_num_of_loops:                       119
% 27.97/4.00  res_forward_subset_subsumed:            2803
% 27.97/4.00  res_backward_subset_subsumed:           4
% 27.97/4.00  res_forward_subsumed:                   0
% 27.97/4.00  res_backward_subsumed:                  0
% 27.97/4.00  res_forward_subsumption_resolution:     0
% 27.97/4.00  res_backward_subsumption_resolution:    0
% 27.97/4.00  res_clause_to_clause_subsumption:       50835
% 27.97/4.00  res_orphan_elimination:                 0
% 27.97/4.00  res_tautology_del:                      694
% 27.97/4.00  res_num_eq_res_simplified:              0
% 27.97/4.00  res_num_sel_changes:                    0
% 27.97/4.00  res_moves_from_active_to_pass:          0
% 27.97/4.00  
% 27.97/4.00  ------ Superposition
% 27.97/4.00  
% 27.97/4.00  sup_time_total:                         0.
% 27.97/4.00  sup_time_generating:                    0.
% 27.97/4.00  sup_time_sim_full:                      0.
% 27.97/4.00  sup_time_sim_immed:                     0.
% 27.97/4.00  
% 27.97/4.00  sup_num_of_clauses:                     3098
% 27.97/4.00  sup_num_in_active:                      167
% 27.97/4.00  sup_num_in_passive:                     2931
% 27.97/4.00  sup_num_of_loops:                       390
% 27.97/4.00  sup_fw_superposition:                   10306
% 27.97/4.00  sup_bw_superposition:                   5539
% 27.97/4.00  sup_immediate_simplified:               5114
% 27.97/4.00  sup_given_eliminated:                   2
% 27.97/4.00  comparisons_done:                       0
% 27.97/4.00  comparisons_avoided:                    517
% 27.97/4.00  
% 27.97/4.00  ------ Simplifications
% 27.97/4.00  
% 27.97/4.00  
% 27.97/4.00  sim_fw_subset_subsumed:                 324
% 27.97/4.00  sim_bw_subset_subsumed:                 22
% 27.97/4.00  sim_fw_subsumed:                        1310
% 27.97/4.00  sim_bw_subsumed:                        42
% 27.97/4.00  sim_fw_subsumption_res:                 0
% 27.97/4.00  sim_bw_subsumption_res:                 0
% 27.97/4.00  sim_tautology_del:                      121
% 27.97/4.00  sim_eq_tautology_del:                   718
% 27.97/4.00  sim_eq_res_simp:                        0
% 27.97/4.00  sim_fw_demodulated:                     2839
% 27.97/4.00  sim_bw_demodulated:                     231
% 27.97/4.00  sim_light_normalised:                   1534
% 27.97/4.00  sim_joinable_taut:                      0
% 27.97/4.00  sim_joinable_simp:                      0
% 27.97/4.00  sim_ac_normalised:                      0
% 27.97/4.00  sim_smt_subsumption:                    0
% 27.97/4.00  
%------------------------------------------------------------------------------
