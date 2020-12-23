%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:30 EST 2020

% Result     : Theorem 23.34s
% Output     : CNFRefutation 23.34s
% Verified   : 
% Statistics : Number of formulae       :  230 (465900 expanded)
%              Number of clauses        :  162 (137735 expanded)
%              Number of leaves         :   24 (133661 expanded)
%              Depth                    :   51
%              Number of atoms          :  349 (473633 expanded)
%              Number of equality atoms :  283 (473524 expanded)
%              Maximal formula depth    :   13 (   2 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f21,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f21])).

fof(f27,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f22])).

fof(f35,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f35])).

fof(f65,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f67])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f68])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f69])).

fof(f81,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f65,f49,f70])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f69])).

fof(f84,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f77])).

fof(f85,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f84])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f64,f49,f70])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f28])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_20,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_313,negated_conjecture,
    ( k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_20,c_9,c_1])).

cnf(c_926,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_0,c_313])).

cnf(c_1126,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_926,c_9])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1104,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_1133,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1126,c_1104])).

cnf(c_1466,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),X0))) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_1133])).

cnf(c_1707,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0)) = k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_10,c_1466])).

cnf(c_1727,plain,
    ( k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_1707,c_8])).

cnf(c_1467,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k5_xboole_0(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10,c_1133])).

cnf(c_1476,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = sK4 ),
    inference(demodulation,[status(thm)],[c_1467,c_8])).

cnf(c_1483,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(sK4,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1476,c_1133])).

cnf(c_1494,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1483,c_9])).

cnf(c_1129,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_10])).

cnf(c_1492,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK4,X0)) = k5_xboole_0(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1129,c_1483])).

cnf(c_1497,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK4,X0)) = sK4 ),
    inference(demodulation,[status(thm)],[c_1492,c_8])).

cnf(c_2255,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK4,X0),X1),k5_xboole_0(X0,X1)) = sK4 ),
    inference(superposition,[status(thm)],[c_1494,c_1497])).

cnf(c_5601,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(X1,k5_xboole_0(X0,X1))) = sK4 ),
    inference(superposition,[status(thm)],[c_2255,c_9])).

cnf(c_1486,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(X0,sK4)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_1483])).

cnf(c_1717,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(X1,sK4))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_9,c_1486])).

cnf(c_5602,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK4,X0),sK4),X0) = k5_xboole_0(sK4,sK4) ),
    inference(superposition,[status(thm)],[c_2255,c_1717])).

cnf(c_5607,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK4,X0),sK4),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5602,c_10])).

cnf(c_554,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_6826,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK4,X0),sK4),k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5607,c_554])).

cnf(c_1878,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(sK4,X1))) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_1494])).

cnf(c_6897,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK4,X2)))) = k5_xboole_0(k5_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_554,c_1878])).

cnf(c_5266,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK4,X2)))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_9,c_1878])).

cnf(c_6908,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X2,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_6897,c_5266])).

cnf(c_7016,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,sK4),k5_xboole_0(k5_xboole_0(X0,X1),X1)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6826,c_6908])).

cnf(c_7017,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),sK4)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7016,c_6908])).

cnf(c_7018,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK4,X0))) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7017,c_6908])).

cnf(c_7019,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK4,X1),X1))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7018,c_6908])).

cnf(c_6890,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK4,X1),X2))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_554,c_1494])).

cnf(c_6931,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,sK4)))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_6890,c_6908])).

cnf(c_7020,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7019,c_6908,c_6931])).

cnf(c_7021,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_7020,c_8])).

cnf(c_1493,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,X0),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1483,c_1129])).

cnf(c_1870,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,X0),X0) = k5_xboole_0(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1493,c_1483])).

cnf(c_1872,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,X0),X0) = sK4 ),
    inference(demodulation,[status(thm)],[c_1870,c_8])).

cnf(c_2297,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(sK4,X1) ),
    inference(superposition,[status(thm)],[c_1872,c_9])).

cnf(c_9253,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK4,X0))) = k5_xboole_0(sK4,X1) ),
    inference(superposition,[status(thm)],[c_7021,c_1494])).

cnf(c_10627,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(X1,X0)) = k5_xboole_0(sK4,X1) ),
    inference(superposition,[status(thm)],[c_1483,c_9253])).

cnf(c_10796,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,X1)),X0) = k5_xboole_0(sK4,X1) ),
    inference(superposition,[status(thm)],[c_7021,c_10627])).

cnf(c_11439,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(X0,sK4),X1)),X0) = k5_xboole_0(sK4,k5_xboole_0(sK4,X1)) ),
    inference(superposition,[status(thm)],[c_10796,c_1717])).

cnf(c_4935,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(X0,sK4),X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_1717])).

cnf(c_11445,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = k5_xboole_0(sK4,k5_xboole_0(sK4,X0)) ),
    inference(light_normalisation,[status(thm)],[c_11439,c_4935])).

cnf(c_555,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_9833,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,sK4)))) = k5_xboole_0(k5_xboole_0(X2,X1),X0) ),
    inference(superposition,[status(thm)],[c_555,c_1878])).

cnf(c_9842,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_9833,c_6931])).

cnf(c_11446,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(demodulation,[status(thm)],[c_11445,c_1483,c_9842])).

cnf(c_11868,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_9,c_11446])).

cnf(c_26199,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,X0),X0) = k5_xboole_0(k5_xboole_0(sK4,X1),X1) ),
    inference(superposition,[status(thm)],[c_2297,c_11868])).

cnf(c_26439,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,X0),X0) = sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_26199])).

cnf(c_29512,plain,
    ( sP0_iProver_split = sK4 ),
    inference(demodulation,[status(thm)],[c_5601,c_7021,c_26439])).

cnf(c_7,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_538,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1279,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_538])).

cnf(c_2949,plain,
    ( r1_tarski(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1476,c_1279])).

cnf(c_49828,plain,
    ( r1_tarski(sP0_iProver_split,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2949,c_29512])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_540,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_49830,plain,
    ( k3_xboole_0(sP0_iProver_split,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_49828,c_540])).

cnf(c_77815,plain,
    ( k5_xboole_0(sP0_iProver_split,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_1727,c_1727,c_29512,c_49830])).

cnf(c_10825,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,X1)),k5_xboole_0(sK4,X0)) = k5_xboole_0(sK4,k5_xboole_0(sK4,X1)) ),
    inference(superposition,[status(thm)],[c_10627,c_10627])).

cnf(c_9749,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(sK4,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1483,c_555])).

cnf(c_10857,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,X1)),k5_xboole_0(sK4,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_10825,c_1483,c_9749])).

cnf(c_11243,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(X1,X2))),k5_xboole_0(sK4,k5_xboole_0(X0,X1))) = X2 ),
    inference(superposition,[status(thm)],[c_9,c_10857])).

cnf(c_57622,plain,
    ( k5_xboole_0(k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,k5_xboole_0(X1,X2))),k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,X1))) = X2 ),
    inference(light_normalisation,[status(thm)],[c_11243,c_11243,c_29512])).

cnf(c_77868,plain,
    ( k5_xboole_0(k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,sP0_iProver_split)),k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,sP0_iProver_split))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_77815,c_57622])).

cnf(c_11903,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_11446,c_9])).

cnf(c_29127,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X0)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_11903,c_1])).

cnf(c_11400,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,X1)),k5_xboole_0(sK4,X1)) = k5_xboole_0(sK4,k5_xboole_0(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_9749,c_10796])).

cnf(c_11470,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,X1)),k5_xboole_0(sK4,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_11400,c_1483])).

cnf(c_12046,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(sK4,k5_xboole_0(X1,X0))) = X1 ),
    inference(superposition,[status(thm)],[c_11470,c_1])).

cnf(c_31187,plain,
    ( k5_xboole_0(k5_xboole_0(sP0_iProver_split,X0),k5_xboole_0(sP0_iProver_split,k5_xboole_0(X1,X0))) = X1 ),
    inference(light_normalisation,[status(thm)],[c_12046,c_12046,c_29512])).

cnf(c_38627,plain,
    ( k5_xboole_0(k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,X1)),k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_29127,c_31187])).

cnf(c_78305,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_77868,c_10,c_38627])).

cnf(c_16,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_532,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_78778,plain,
    ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_78305,c_532])).

cnf(c_19,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_314,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(theory_normalisation,[status(thm)],[c_19,c_9,c_1])).

cnf(c_1117,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_314,c_926])).

cnf(c_29572,plain,
    ( k3_tarski(k6_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_29512,c_1117])).

cnf(c_78773,plain,
    ( k3_tarski(k6_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_78305,c_29572])).

cnf(c_1490,plain,
    ( k5_xboole_0(sK4,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0))) = k5_xboole_0(X0,k3_xboole_0(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_314,c_1483])).

cnf(c_11382,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(sK4,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0)))),X0) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_1490,c_10796])).

cnf(c_11479,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0)),X0) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_11382,c_1483,c_9842])).

cnf(c_13804,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,X0))),k5_xboole_0(sK4,X0)) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0)) ),
    inference(superposition,[status(thm)],[c_11479,c_11470])).

cnf(c_556,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_13120,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,X1)),k5_xboole_0(X0,X2)) = k5_xboole_0(X2,k5_xboole_0(sK4,X1)) ),
    inference(superposition,[status(thm)],[c_10796,c_556])).

cnf(c_13860,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0)) = k5_xboole_0(k3_xboole_0(sK4,X0),k5_xboole_0(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_13804,c_1483,c_13120])).

cnf(c_14750,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0))),k5_xboole_0(sK4,k5_xboole_0(sK4,X0))) = k3_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_13860,c_11470])).

cnf(c_14783,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0))),X0) = k3_xboole_0(sK4,X0) ),
    inference(light_normalisation,[status(thm)],[c_14750,c_1483])).

cnf(c_15210,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK4,X0)),X0) = k3_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1490,c_14783])).

cnf(c_32841,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,X0)),X0) = k3_xboole_0(sP0_iProver_split,X0) ),
    inference(light_normalisation,[status(thm)],[c_15210,c_15210,c_29512])).

cnf(c_32855,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sP0_iProver_split)),X0) = k3_xboole_0(sP0_iProver_split,X0) ),
    inference(superposition,[status(thm)],[c_0,c_32841])).

cnf(c_42637,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,sP0_iProver_split))) = k3_xboole_0(sP0_iProver_split,X0) ),
    inference(superposition,[status(thm)],[c_32855,c_1])).

cnf(c_47958,plain,
    ( k5_xboole_0(k3_xboole_0(sP0_iProver_split,X0),k3_xboole_0(X0,sP0_iProver_split)) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_42637,c_11868])).

cnf(c_47997,plain,
    ( k5_xboole_0(k3_xboole_0(sP0_iProver_split,X0),k3_xboole_0(X0,sP0_iProver_split)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_47958,c_10])).

cnf(c_49193,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sP0_iProver_split),k3_xboole_0(sP0_iProver_split,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_47997,c_1])).

cnf(c_11871,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X2)) = X1 ),
    inference(superposition,[status(thm)],[c_554,c_11446])).

cnf(c_51872,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,X1))) = k3_xboole_0(X1,sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_49193,c_11871])).

cnf(c_51888,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,X1))) = k3_xboole_0(X1,sP0_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_51872,c_8])).

cnf(c_1130,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X0,k5_xboole_0(X1,X2))))) ),
    inference(superposition,[status(thm)],[c_9,c_314])).

cnf(c_65771,plain,
    ( k3_tarski(k6_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,k5_xboole_0(X0,X0))) = k5_xboole_0(sP0_iProver_split,k3_xboole_0(k5_xboole_0(X0,X0),sP0_iProver_split)) ),
    inference(superposition,[status(thm)],[c_51888,c_1130])).

cnf(c_42657,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sP0_iProver_split),X0)) = k3_xboole_0(sP0_iProver_split,X0) ),
    inference(superposition,[status(thm)],[c_32855,c_9])).

cnf(c_10812,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(sK4,X1))),k5_xboole_0(X1,X0)) = k5_xboole_0(sK4,sK4) ),
    inference(superposition,[status(thm)],[c_1878,c_10627])).

cnf(c_4946,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(sK4,X1))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_1717])).

cnf(c_10867,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k5_xboole_0(sK4,sK4) ),
    inference(light_normalisation,[status(thm)],[c_10812,c_4946])).

cnf(c_9743,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_7021,c_555])).

cnf(c_10868,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10867,c_10,c_9743])).

cnf(c_13002,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X0))) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10868,c_554])).

cnf(c_13015,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X0))) = X2 ),
    inference(demodulation,[status(thm)],[c_13002,c_8,c_9842])).

cnf(c_52582,plain,
    ( k3_xboole_0(sP0_iProver_split,k5_xboole_0(X0,X0)) = k3_xboole_0(k5_xboole_0(X0,X0),sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_42657,c_13015])).

cnf(c_42638,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sP0_iProver_split)) = k3_xboole_0(sP0_iProver_split,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_32855,c_8])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_539,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_33681,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_539,c_540])).

cnf(c_42734,plain,
    ( k3_xboole_0(sP0_iProver_split,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_42638,c_1104,c_33681])).

cnf(c_52623,plain,
    ( k3_xboole_0(k1_xboole_0,sP0_iProver_split) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_52582,c_10,c_42734])).

cnf(c_65839,plain,
    ( k3_tarski(k6_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,k1_xboole_0)) = k5_xboole_0(sP0_iProver_split,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_65771,c_10,c_52623])).

cnf(c_46485,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X2,X1)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X0,k1_xboole_0)))) ),
    inference(superposition,[status(thm)],[c_10868,c_1130])).

cnf(c_13232,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_556,c_11446])).

cnf(c_26615,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_11446,c_11871])).

cnf(c_33737,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),X3)) = k5_xboole_0(k5_xboole_0(X2,X1),X3) ),
    inference(superposition,[status(thm)],[c_13232,c_26615])).

cnf(c_13265,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(X1,k5_xboole_0(sK4,X2))) = k5_xboole_0(k5_xboole_0(X2,X1),X0) ),
    inference(superposition,[status(thm)],[c_556,c_9749])).

cnf(c_10175,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(X1,k5_xboole_0(sK4,X2))) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_9749,c_554])).

cnf(c_13293,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_13265,c_10175])).

cnf(c_33878,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3))) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(demodulation,[status(thm)],[c_33737,c_13293])).

cnf(c_11872,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X0)) = X2 ),
    inference(superposition,[status(thm)],[c_555,c_11446])).

cnf(c_27999,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X1,X0),X3)) = k5_xboole_0(X3,X2) ),
    inference(superposition,[status(thm)],[c_11872,c_556])).

cnf(c_26619,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X3)) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_11868,c_11871])).

cnf(c_28047,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
    inference(demodulation,[status(thm)],[c_27999,c_13293,c_26619])).

cnf(c_33879,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_33878,c_13293,c_28047])).

cnf(c_46739,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X0,k1_xboole_0)),X2))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_46485,c_10868,c_33879])).

cnf(c_46740,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X1),k5_xboole_0(X2,k3_xboole_0(X0,k1_xboole_0))))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_46739,c_33879])).

cnf(c_1124,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_10,c_9])).

cnf(c_1134,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1124,c_1104])).

cnf(c_46741,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_46740,c_1134,c_26615])).

cnf(c_65840,plain,
    ( k3_tarski(k6_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,k1_xboole_0)) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_65839,c_8,c_46741])).

cnf(c_78774,plain,
    ( sP0_iProver_split = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_78773,c_65840])).

cnf(c_78786,plain,
    ( r2_hidden(sK2,sP0_iProver_split) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_78778,c_78774])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_4,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_198,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | k5_xboole_0(X3,X4) != X2
    | k3_xboole_0(X3,X4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_199,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_528,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_199])).

cnf(c_2064,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(sK4,k5_xboole_0(sK4,X1)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_528])).

cnf(c_29567,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(sP0_iProver_split,k5_xboole_0(sP0_iProver_split,X1)),X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29512,c_2064])).

cnf(c_77907,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(sP0_iProver_split,sP0_iProver_split),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_77815,c_29567])).

cnf(c_52692,plain,
    ( r1_tarski(k5_xboole_0(sP0_iProver_split,k1_xboole_0),sP0_iProver_split) = iProver_top ),
    inference(superposition,[status(thm)],[c_52623,c_1279])).

cnf(c_52712,plain,
    ( r1_tarski(sP0_iProver_split,sP0_iProver_split) = iProver_top ),
    inference(demodulation,[status(thm)],[c_52692,c_8])).

cnf(c_55573,plain,
    ( k3_xboole_0(sP0_iProver_split,sP0_iProver_split) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_52712,c_540])).

cnf(c_78275,plain,
    ( r2_hidden(X0,sP0_iProver_split) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_77907,c_49830,c_55573])).

cnf(c_78383,plain,
    ( r2_hidden(sK2,sP0_iProver_split) != iProver_top ),
    inference(instantiation,[status(thm)],[c_78275])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_78786,c_78383])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:50:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 23.34/3.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.34/3.49  
% 23.34/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.34/3.49  
% 23.34/3.49  ------  iProver source info
% 23.34/3.49  
% 23.34/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.34/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.34/3.49  git: non_committed_changes: false
% 23.34/3.49  git: last_make_outside_of_git: false
% 23.34/3.49  
% 23.34/3.49  ------ 
% 23.34/3.49  
% 23.34/3.49  ------ Input Options
% 23.34/3.49  
% 23.34/3.49  --out_options                           all
% 23.34/3.49  --tptp_safe_out                         true
% 23.34/3.49  --problem_path                          ""
% 23.34/3.49  --include_path                          ""
% 23.34/3.49  --clausifier                            res/vclausify_rel
% 23.34/3.49  --clausifier_options                    ""
% 23.34/3.49  --stdin                                 false
% 23.34/3.49  --stats_out                             all
% 23.34/3.49  
% 23.34/3.49  ------ General Options
% 23.34/3.49  
% 23.34/3.49  --fof                                   false
% 23.34/3.49  --time_out_real                         305.
% 23.34/3.49  --time_out_virtual                      -1.
% 23.34/3.49  --symbol_type_check                     false
% 23.34/3.49  --clausify_out                          false
% 23.34/3.49  --sig_cnt_out                           false
% 23.34/3.49  --trig_cnt_out                          false
% 23.34/3.49  --trig_cnt_out_tolerance                1.
% 23.34/3.49  --trig_cnt_out_sk_spl                   false
% 23.34/3.49  --abstr_cl_out                          false
% 23.34/3.49  
% 23.34/3.49  ------ Global Options
% 23.34/3.49  
% 23.34/3.49  --schedule                              default
% 23.34/3.49  --add_important_lit                     false
% 23.34/3.49  --prop_solver_per_cl                    1000
% 23.34/3.49  --min_unsat_core                        false
% 23.34/3.49  --soft_assumptions                      false
% 23.34/3.49  --soft_lemma_size                       3
% 23.34/3.49  --prop_impl_unit_size                   0
% 23.34/3.49  --prop_impl_unit                        []
% 23.34/3.49  --share_sel_clauses                     true
% 23.34/3.49  --reset_solvers                         false
% 23.34/3.49  --bc_imp_inh                            [conj_cone]
% 23.34/3.49  --conj_cone_tolerance                   3.
% 23.34/3.49  --extra_neg_conj                        none
% 23.34/3.49  --large_theory_mode                     true
% 23.34/3.49  --prolific_symb_bound                   200
% 23.34/3.49  --lt_threshold                          2000
% 23.34/3.49  --clause_weak_htbl                      true
% 23.34/3.49  --gc_record_bc_elim                     false
% 23.34/3.49  
% 23.34/3.49  ------ Preprocessing Options
% 23.34/3.49  
% 23.34/3.49  --preprocessing_flag                    true
% 23.34/3.49  --time_out_prep_mult                    0.1
% 23.34/3.49  --splitting_mode                        input
% 23.34/3.49  --splitting_grd                         true
% 23.34/3.49  --splitting_cvd                         false
% 23.34/3.49  --splitting_cvd_svl                     false
% 23.34/3.49  --splitting_nvd                         32
% 23.34/3.49  --sub_typing                            true
% 23.34/3.49  --prep_gs_sim                           true
% 23.34/3.49  --prep_unflatten                        true
% 23.34/3.49  --prep_res_sim                          true
% 23.34/3.49  --prep_upred                            true
% 23.34/3.49  --prep_sem_filter                       exhaustive
% 23.34/3.49  --prep_sem_filter_out                   false
% 23.34/3.49  --pred_elim                             true
% 23.34/3.49  --res_sim_input                         true
% 23.34/3.49  --eq_ax_congr_red                       true
% 23.34/3.49  --pure_diseq_elim                       true
% 23.34/3.49  --brand_transform                       false
% 23.34/3.49  --non_eq_to_eq                          false
% 23.34/3.49  --prep_def_merge                        true
% 23.34/3.49  --prep_def_merge_prop_impl              false
% 23.34/3.49  --prep_def_merge_mbd                    true
% 23.34/3.49  --prep_def_merge_tr_red                 false
% 23.34/3.49  --prep_def_merge_tr_cl                  false
% 23.34/3.49  --smt_preprocessing                     true
% 23.34/3.49  --smt_ac_axioms                         fast
% 23.34/3.49  --preprocessed_out                      false
% 23.34/3.49  --preprocessed_stats                    false
% 23.34/3.49  
% 23.34/3.49  ------ Abstraction refinement Options
% 23.34/3.49  
% 23.34/3.49  --abstr_ref                             []
% 23.34/3.49  --abstr_ref_prep                        false
% 23.34/3.49  --abstr_ref_until_sat                   false
% 23.34/3.49  --abstr_ref_sig_restrict                funpre
% 23.34/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.34/3.49  --abstr_ref_under                       []
% 23.34/3.49  
% 23.34/3.49  ------ SAT Options
% 23.34/3.49  
% 23.34/3.49  --sat_mode                              false
% 23.34/3.49  --sat_fm_restart_options                ""
% 23.34/3.49  --sat_gr_def                            false
% 23.34/3.49  --sat_epr_types                         true
% 23.34/3.49  --sat_non_cyclic_types                  false
% 23.34/3.49  --sat_finite_models                     false
% 23.34/3.49  --sat_fm_lemmas                         false
% 23.34/3.49  --sat_fm_prep                           false
% 23.34/3.49  --sat_fm_uc_incr                        true
% 23.34/3.49  --sat_out_model                         small
% 23.34/3.49  --sat_out_clauses                       false
% 23.34/3.49  
% 23.34/3.49  ------ QBF Options
% 23.34/3.49  
% 23.34/3.49  --qbf_mode                              false
% 23.34/3.49  --qbf_elim_univ                         false
% 23.34/3.49  --qbf_dom_inst                          none
% 23.34/3.49  --qbf_dom_pre_inst                      false
% 23.34/3.49  --qbf_sk_in                             false
% 23.34/3.49  --qbf_pred_elim                         true
% 23.34/3.49  --qbf_split                             512
% 23.34/3.49  
% 23.34/3.49  ------ BMC1 Options
% 23.34/3.49  
% 23.34/3.49  --bmc1_incremental                      false
% 23.34/3.49  --bmc1_axioms                           reachable_all
% 23.34/3.49  --bmc1_min_bound                        0
% 23.34/3.49  --bmc1_max_bound                        -1
% 23.34/3.49  --bmc1_max_bound_default                -1
% 23.34/3.49  --bmc1_symbol_reachability              true
% 23.34/3.49  --bmc1_property_lemmas                  false
% 23.34/3.49  --bmc1_k_induction                      false
% 23.34/3.49  --bmc1_non_equiv_states                 false
% 23.34/3.49  --bmc1_deadlock                         false
% 23.34/3.49  --bmc1_ucm                              false
% 23.34/3.49  --bmc1_add_unsat_core                   none
% 23.34/3.49  --bmc1_unsat_core_children              false
% 23.34/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.34/3.49  --bmc1_out_stat                         full
% 23.34/3.49  --bmc1_ground_init                      false
% 23.34/3.49  --bmc1_pre_inst_next_state              false
% 23.34/3.49  --bmc1_pre_inst_state                   false
% 23.34/3.49  --bmc1_pre_inst_reach_state             false
% 23.34/3.49  --bmc1_out_unsat_core                   false
% 23.34/3.49  --bmc1_aig_witness_out                  false
% 23.34/3.49  --bmc1_verbose                          false
% 23.34/3.49  --bmc1_dump_clauses_tptp                false
% 23.34/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.34/3.49  --bmc1_dump_file                        -
% 23.34/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.34/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.34/3.49  --bmc1_ucm_extend_mode                  1
% 23.34/3.49  --bmc1_ucm_init_mode                    2
% 23.34/3.49  --bmc1_ucm_cone_mode                    none
% 23.34/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.34/3.49  --bmc1_ucm_relax_model                  4
% 23.34/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.34/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.34/3.49  --bmc1_ucm_layered_model                none
% 23.34/3.49  --bmc1_ucm_max_lemma_size               10
% 23.34/3.49  
% 23.34/3.49  ------ AIG Options
% 23.34/3.49  
% 23.34/3.49  --aig_mode                              false
% 23.34/3.49  
% 23.34/3.49  ------ Instantiation Options
% 23.34/3.49  
% 23.34/3.49  --instantiation_flag                    true
% 23.34/3.49  --inst_sos_flag                         true
% 23.34/3.49  --inst_sos_phase                        true
% 23.34/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.34/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.34/3.49  --inst_lit_sel_side                     num_symb
% 23.34/3.49  --inst_solver_per_active                1400
% 23.34/3.49  --inst_solver_calls_frac                1.
% 23.34/3.49  --inst_passive_queue_type               priority_queues
% 23.34/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.34/3.49  --inst_passive_queues_freq              [25;2]
% 23.34/3.49  --inst_dismatching                      true
% 23.34/3.49  --inst_eager_unprocessed_to_passive     true
% 23.34/3.49  --inst_prop_sim_given                   true
% 23.34/3.49  --inst_prop_sim_new                     false
% 23.34/3.49  --inst_subs_new                         false
% 23.34/3.49  --inst_eq_res_simp                      false
% 23.34/3.49  --inst_subs_given                       false
% 23.34/3.49  --inst_orphan_elimination               true
% 23.34/3.49  --inst_learning_loop_flag               true
% 23.34/3.49  --inst_learning_start                   3000
% 23.34/3.49  --inst_learning_factor                  2
% 23.34/3.49  --inst_start_prop_sim_after_learn       3
% 23.34/3.49  --inst_sel_renew                        solver
% 23.34/3.49  --inst_lit_activity_flag                true
% 23.34/3.49  --inst_restr_to_given                   false
% 23.34/3.49  --inst_activity_threshold               500
% 23.34/3.49  --inst_out_proof                        true
% 23.34/3.49  
% 23.34/3.49  ------ Resolution Options
% 23.34/3.49  
% 23.34/3.49  --resolution_flag                       true
% 23.34/3.49  --res_lit_sel                           adaptive
% 23.34/3.49  --res_lit_sel_side                      none
% 23.34/3.49  --res_ordering                          kbo
% 23.34/3.49  --res_to_prop_solver                    active
% 23.34/3.49  --res_prop_simpl_new                    false
% 23.34/3.49  --res_prop_simpl_given                  true
% 23.34/3.49  --res_passive_queue_type                priority_queues
% 23.34/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.34/3.49  --res_passive_queues_freq               [15;5]
% 23.34/3.49  --res_forward_subs                      full
% 23.34/3.49  --res_backward_subs                     full
% 23.34/3.49  --res_forward_subs_resolution           true
% 23.34/3.49  --res_backward_subs_resolution          true
% 23.34/3.49  --res_orphan_elimination                true
% 23.34/3.49  --res_time_limit                        2.
% 23.34/3.49  --res_out_proof                         true
% 23.34/3.49  
% 23.34/3.49  ------ Superposition Options
% 23.34/3.49  
% 23.34/3.49  --superposition_flag                    true
% 23.34/3.49  --sup_passive_queue_type                priority_queues
% 23.34/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.34/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.34/3.49  --demod_completeness_check              fast
% 23.34/3.49  --demod_use_ground                      true
% 23.34/3.49  --sup_to_prop_solver                    passive
% 23.34/3.49  --sup_prop_simpl_new                    true
% 23.34/3.49  --sup_prop_simpl_given                  true
% 23.34/3.49  --sup_fun_splitting                     true
% 23.34/3.49  --sup_smt_interval                      50000
% 23.34/3.49  
% 23.34/3.49  ------ Superposition Simplification Setup
% 23.34/3.49  
% 23.34/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.34/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.34/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.34/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.34/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.34/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.34/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.34/3.49  --sup_immed_triv                        [TrivRules]
% 23.34/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.34/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.34/3.49  --sup_immed_bw_main                     []
% 23.34/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.34/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.34/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.34/3.49  --sup_input_bw                          []
% 23.34/3.49  
% 23.34/3.49  ------ Combination Options
% 23.34/3.49  
% 23.34/3.49  --comb_res_mult                         3
% 23.34/3.49  --comb_sup_mult                         2
% 23.34/3.49  --comb_inst_mult                        10
% 23.34/3.49  
% 23.34/3.49  ------ Debug Options
% 23.34/3.49  
% 23.34/3.49  --dbg_backtrace                         false
% 23.34/3.49  --dbg_dump_prop_clauses                 false
% 23.34/3.49  --dbg_dump_prop_clauses_file            -
% 23.34/3.49  --dbg_out_stat                          false
% 23.34/3.49  ------ Parsing...
% 23.34/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.34/3.49  
% 23.34/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 23.34/3.49  
% 23.34/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.34/3.49  
% 23.34/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.34/3.49  ------ Proving...
% 23.34/3.49  ------ Problem Properties 
% 23.34/3.49  
% 23.34/3.49  
% 23.34/3.49  clauses                                 20
% 23.34/3.49  conjectures                             1
% 23.34/3.49  EPR                                     1
% 23.34/3.49  Horn                                    18
% 23.34/3.49  unary                                   13
% 23.34/3.49  binary                                  2
% 23.34/3.49  lits                                    35
% 23.34/3.49  lits eq                                 21
% 23.34/3.49  fd_pure                                 0
% 23.34/3.49  fd_pseudo                               0
% 23.34/3.49  fd_cond                                 0
% 23.34/3.49  fd_pseudo_cond                          4
% 23.34/3.49  AC symbols                              1
% 23.34/3.49  
% 23.34/3.49  ------ Schedule dynamic 5 is on 
% 23.34/3.49  
% 23.34/3.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.34/3.49  
% 23.34/3.49  
% 23.34/3.49  ------ 
% 23.34/3.49  Current options:
% 23.34/3.49  ------ 
% 23.34/3.49  
% 23.34/3.49  ------ Input Options
% 23.34/3.49  
% 23.34/3.49  --out_options                           all
% 23.34/3.49  --tptp_safe_out                         true
% 23.34/3.49  --problem_path                          ""
% 23.34/3.49  --include_path                          ""
% 23.34/3.49  --clausifier                            res/vclausify_rel
% 23.34/3.49  --clausifier_options                    ""
% 23.34/3.49  --stdin                                 false
% 23.34/3.49  --stats_out                             all
% 23.34/3.49  
% 23.34/3.49  ------ General Options
% 23.34/3.49  
% 23.34/3.49  --fof                                   false
% 23.34/3.49  --time_out_real                         305.
% 23.34/3.49  --time_out_virtual                      -1.
% 23.34/3.49  --symbol_type_check                     false
% 23.34/3.49  --clausify_out                          false
% 23.34/3.49  --sig_cnt_out                           false
% 23.34/3.49  --trig_cnt_out                          false
% 23.34/3.49  --trig_cnt_out_tolerance                1.
% 23.34/3.49  --trig_cnt_out_sk_spl                   false
% 23.34/3.49  --abstr_cl_out                          false
% 23.34/3.49  
% 23.34/3.49  ------ Global Options
% 23.34/3.49  
% 23.34/3.49  --schedule                              default
% 23.34/3.49  --add_important_lit                     false
% 23.34/3.49  --prop_solver_per_cl                    1000
% 23.34/3.49  --min_unsat_core                        false
% 23.34/3.49  --soft_assumptions                      false
% 23.34/3.49  --soft_lemma_size                       3
% 23.34/3.49  --prop_impl_unit_size                   0
% 23.34/3.49  --prop_impl_unit                        []
% 23.34/3.49  --share_sel_clauses                     true
% 23.34/3.49  --reset_solvers                         false
% 23.34/3.49  --bc_imp_inh                            [conj_cone]
% 23.34/3.49  --conj_cone_tolerance                   3.
% 23.34/3.49  --extra_neg_conj                        none
% 23.34/3.49  --large_theory_mode                     true
% 23.34/3.49  --prolific_symb_bound                   200
% 23.34/3.49  --lt_threshold                          2000
% 23.34/3.49  --clause_weak_htbl                      true
% 23.34/3.49  --gc_record_bc_elim                     false
% 23.34/3.49  
% 23.34/3.49  ------ Preprocessing Options
% 23.34/3.49  
% 23.34/3.49  --preprocessing_flag                    true
% 23.34/3.49  --time_out_prep_mult                    0.1
% 23.34/3.49  --splitting_mode                        input
% 23.34/3.49  --splitting_grd                         true
% 23.34/3.49  --splitting_cvd                         false
% 23.34/3.49  --splitting_cvd_svl                     false
% 23.34/3.49  --splitting_nvd                         32
% 23.34/3.49  --sub_typing                            true
% 23.34/3.49  --prep_gs_sim                           true
% 23.34/3.49  --prep_unflatten                        true
% 23.34/3.49  --prep_res_sim                          true
% 23.34/3.49  --prep_upred                            true
% 23.34/3.49  --prep_sem_filter                       exhaustive
% 23.34/3.49  --prep_sem_filter_out                   false
% 23.34/3.49  --pred_elim                             true
% 23.34/3.49  --res_sim_input                         true
% 23.34/3.49  --eq_ax_congr_red                       true
% 23.34/3.49  --pure_diseq_elim                       true
% 23.34/3.49  --brand_transform                       false
% 23.34/3.49  --non_eq_to_eq                          false
% 23.34/3.49  --prep_def_merge                        true
% 23.34/3.49  --prep_def_merge_prop_impl              false
% 23.34/3.49  --prep_def_merge_mbd                    true
% 23.34/3.49  --prep_def_merge_tr_red                 false
% 23.34/3.49  --prep_def_merge_tr_cl                  false
% 23.34/3.49  --smt_preprocessing                     true
% 23.34/3.49  --smt_ac_axioms                         fast
% 23.34/3.49  --preprocessed_out                      false
% 23.34/3.49  --preprocessed_stats                    false
% 23.34/3.49  
% 23.34/3.49  ------ Abstraction refinement Options
% 23.34/3.49  
% 23.34/3.49  --abstr_ref                             []
% 23.34/3.49  --abstr_ref_prep                        false
% 23.34/3.49  --abstr_ref_until_sat                   false
% 23.34/3.49  --abstr_ref_sig_restrict                funpre
% 23.34/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.34/3.49  --abstr_ref_under                       []
% 23.34/3.49  
% 23.34/3.49  ------ SAT Options
% 23.34/3.49  
% 23.34/3.49  --sat_mode                              false
% 23.34/3.49  --sat_fm_restart_options                ""
% 23.34/3.49  --sat_gr_def                            false
% 23.34/3.49  --sat_epr_types                         true
% 23.34/3.49  --sat_non_cyclic_types                  false
% 23.34/3.49  --sat_finite_models                     false
% 23.34/3.49  --sat_fm_lemmas                         false
% 23.34/3.49  --sat_fm_prep                           false
% 23.34/3.49  --sat_fm_uc_incr                        true
% 23.34/3.49  --sat_out_model                         small
% 23.34/3.49  --sat_out_clauses                       false
% 23.34/3.49  
% 23.34/3.49  ------ QBF Options
% 23.34/3.49  
% 23.34/3.49  --qbf_mode                              false
% 23.34/3.49  --qbf_elim_univ                         false
% 23.34/3.49  --qbf_dom_inst                          none
% 23.34/3.49  --qbf_dom_pre_inst                      false
% 23.34/3.49  --qbf_sk_in                             false
% 23.34/3.49  --qbf_pred_elim                         true
% 23.34/3.49  --qbf_split                             512
% 23.34/3.49  
% 23.34/3.49  ------ BMC1 Options
% 23.34/3.49  
% 23.34/3.49  --bmc1_incremental                      false
% 23.34/3.49  --bmc1_axioms                           reachable_all
% 23.34/3.49  --bmc1_min_bound                        0
% 23.34/3.49  --bmc1_max_bound                        -1
% 23.34/3.49  --bmc1_max_bound_default                -1
% 23.34/3.49  --bmc1_symbol_reachability              true
% 23.34/3.49  --bmc1_property_lemmas                  false
% 23.34/3.49  --bmc1_k_induction                      false
% 23.34/3.49  --bmc1_non_equiv_states                 false
% 23.34/3.49  --bmc1_deadlock                         false
% 23.34/3.49  --bmc1_ucm                              false
% 23.34/3.49  --bmc1_add_unsat_core                   none
% 23.34/3.49  --bmc1_unsat_core_children              false
% 23.34/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.34/3.49  --bmc1_out_stat                         full
% 23.34/3.49  --bmc1_ground_init                      false
% 23.34/3.49  --bmc1_pre_inst_next_state              false
% 23.34/3.49  --bmc1_pre_inst_state                   false
% 23.34/3.49  --bmc1_pre_inst_reach_state             false
% 23.34/3.49  --bmc1_out_unsat_core                   false
% 23.34/3.49  --bmc1_aig_witness_out                  false
% 23.34/3.49  --bmc1_verbose                          false
% 23.34/3.49  --bmc1_dump_clauses_tptp                false
% 23.34/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.34/3.49  --bmc1_dump_file                        -
% 23.34/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.34/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.34/3.49  --bmc1_ucm_extend_mode                  1
% 23.34/3.49  --bmc1_ucm_init_mode                    2
% 23.34/3.49  --bmc1_ucm_cone_mode                    none
% 23.34/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.34/3.49  --bmc1_ucm_relax_model                  4
% 23.34/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.34/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.34/3.49  --bmc1_ucm_layered_model                none
% 23.34/3.49  --bmc1_ucm_max_lemma_size               10
% 23.34/3.49  
% 23.34/3.49  ------ AIG Options
% 23.34/3.49  
% 23.34/3.49  --aig_mode                              false
% 23.34/3.49  
% 23.34/3.49  ------ Instantiation Options
% 23.34/3.49  
% 23.34/3.49  --instantiation_flag                    true
% 23.34/3.49  --inst_sos_flag                         true
% 23.34/3.49  --inst_sos_phase                        true
% 23.34/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.34/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.34/3.49  --inst_lit_sel_side                     none
% 23.34/3.49  --inst_solver_per_active                1400
% 23.34/3.49  --inst_solver_calls_frac                1.
% 23.34/3.49  --inst_passive_queue_type               priority_queues
% 23.34/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.34/3.49  --inst_passive_queues_freq              [25;2]
% 23.34/3.49  --inst_dismatching                      true
% 23.34/3.49  --inst_eager_unprocessed_to_passive     true
% 23.34/3.49  --inst_prop_sim_given                   true
% 23.34/3.49  --inst_prop_sim_new                     false
% 23.34/3.49  --inst_subs_new                         false
% 23.34/3.49  --inst_eq_res_simp                      false
% 23.34/3.49  --inst_subs_given                       false
% 23.34/3.49  --inst_orphan_elimination               true
% 23.34/3.49  --inst_learning_loop_flag               true
% 23.34/3.49  --inst_learning_start                   3000
% 23.34/3.49  --inst_learning_factor                  2
% 23.34/3.49  --inst_start_prop_sim_after_learn       3
% 23.34/3.49  --inst_sel_renew                        solver
% 23.34/3.49  --inst_lit_activity_flag                true
% 23.34/3.49  --inst_restr_to_given                   false
% 23.34/3.49  --inst_activity_threshold               500
% 23.34/3.49  --inst_out_proof                        true
% 23.34/3.49  
% 23.34/3.49  ------ Resolution Options
% 23.34/3.49  
% 23.34/3.49  --resolution_flag                       false
% 23.34/3.49  --res_lit_sel                           adaptive
% 23.34/3.49  --res_lit_sel_side                      none
% 23.34/3.49  --res_ordering                          kbo
% 23.34/3.49  --res_to_prop_solver                    active
% 23.34/3.49  --res_prop_simpl_new                    false
% 23.34/3.49  --res_prop_simpl_given                  true
% 23.34/3.49  --res_passive_queue_type                priority_queues
% 23.34/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.34/3.49  --res_passive_queues_freq               [15;5]
% 23.34/3.49  --res_forward_subs                      full
% 23.34/3.49  --res_backward_subs                     full
% 23.34/3.49  --res_forward_subs_resolution           true
% 23.34/3.49  --res_backward_subs_resolution          true
% 23.34/3.49  --res_orphan_elimination                true
% 23.34/3.49  --res_time_limit                        2.
% 23.34/3.49  --res_out_proof                         true
% 23.34/3.49  
% 23.34/3.49  ------ Superposition Options
% 23.34/3.49  
% 23.34/3.49  --superposition_flag                    true
% 23.34/3.49  --sup_passive_queue_type                priority_queues
% 23.34/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.34/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.34/3.49  --demod_completeness_check              fast
% 23.34/3.49  --demod_use_ground                      true
% 23.34/3.49  --sup_to_prop_solver                    passive
% 23.34/3.49  --sup_prop_simpl_new                    true
% 23.34/3.49  --sup_prop_simpl_given                  true
% 23.34/3.49  --sup_fun_splitting                     true
% 23.34/3.49  --sup_smt_interval                      50000
% 23.34/3.49  
% 23.34/3.49  ------ Superposition Simplification Setup
% 23.34/3.49  
% 23.34/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.34/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.34/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.34/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.34/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.34/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.34/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.34/3.49  --sup_immed_triv                        [TrivRules]
% 23.34/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.34/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.34/3.49  --sup_immed_bw_main                     []
% 23.34/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.34/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.34/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.34/3.49  --sup_input_bw                          []
% 23.34/3.49  
% 23.34/3.49  ------ Combination Options
% 23.34/3.49  
% 23.34/3.49  --comb_res_mult                         3
% 23.34/3.49  --comb_sup_mult                         2
% 23.34/3.49  --comb_inst_mult                        10
% 23.34/3.49  
% 23.34/3.49  ------ Debug Options
% 23.34/3.49  
% 23.34/3.49  --dbg_backtrace                         false
% 23.34/3.49  --dbg_dump_prop_clauses                 false
% 23.34/3.49  --dbg_dump_prop_clauses_file            -
% 23.34/3.49  --dbg_out_stat                          false
% 23.34/3.49  
% 23.34/3.49  
% 23.34/3.49  
% 23.34/3.49  
% 23.34/3.49  ------ Proving...
% 23.34/3.49  
% 23.34/3.49  
% 23.34/3.49  % SZS status Theorem for theBenchmark.p
% 23.34/3.49  
% 23.34/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.34/3.49  
% 23.34/3.49  fof(f11,axiom,(
% 23.34/3.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f48,plain,(
% 23.34/3.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 23.34/3.49    inference(cnf_transformation,[],[f11])).
% 23.34/3.49  
% 23.34/3.49  fof(f10,axiom,(
% 23.34/3.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f47,plain,(
% 23.34/3.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 23.34/3.49    inference(cnf_transformation,[],[f10])).
% 23.34/3.49  
% 23.34/3.49  fof(f1,axiom,(
% 23.34/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f37,plain,(
% 23.34/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.34/3.49    inference(cnf_transformation,[],[f1])).
% 23.34/3.49  
% 23.34/3.49  fof(f21,conjecture,(
% 23.34/3.49    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f22,negated_conjecture,(
% 23.34/3.49    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 23.34/3.49    inference(negated_conjecture,[],[f21])).
% 23.34/3.49  
% 23.34/3.49  fof(f27,plain,(
% 23.34/3.49    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 23.34/3.49    inference(ennf_transformation,[],[f22])).
% 23.34/3.49  
% 23.34/3.49  fof(f35,plain,(
% 23.34/3.49    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 23.34/3.49    introduced(choice_axiom,[])).
% 23.34/3.49  
% 23.34/3.49  fof(f36,plain,(
% 23.34/3.49    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 23.34/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f35])).
% 23.34/3.49  
% 23.34/3.49  fof(f65,plain,(
% 23.34/3.49    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 23.34/3.49    inference(cnf_transformation,[],[f36])).
% 23.34/3.49  
% 23.34/3.49  fof(f12,axiom,(
% 23.34/3.49    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f49,plain,(
% 23.34/3.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 23.34/3.49    inference(cnf_transformation,[],[f12])).
% 23.34/3.49  
% 23.34/3.49  fof(f14,axiom,(
% 23.34/3.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f58,plain,(
% 23.34/3.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 23.34/3.49    inference(cnf_transformation,[],[f14])).
% 23.34/3.49  
% 23.34/3.49  fof(f15,axiom,(
% 23.34/3.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f59,plain,(
% 23.34/3.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.34/3.49    inference(cnf_transformation,[],[f15])).
% 23.34/3.49  
% 23.34/3.49  fof(f16,axiom,(
% 23.34/3.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f60,plain,(
% 23.34/3.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 23.34/3.49    inference(cnf_transformation,[],[f16])).
% 23.34/3.49  
% 23.34/3.49  fof(f17,axiom,(
% 23.34/3.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f61,plain,(
% 23.34/3.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 23.34/3.49    inference(cnf_transformation,[],[f17])).
% 23.34/3.49  
% 23.34/3.49  fof(f18,axiom,(
% 23.34/3.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f62,plain,(
% 23.34/3.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 23.34/3.49    inference(cnf_transformation,[],[f18])).
% 23.34/3.49  
% 23.34/3.49  fof(f19,axiom,(
% 23.34/3.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f63,plain,(
% 23.34/3.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 23.34/3.49    inference(cnf_transformation,[],[f19])).
% 23.34/3.49  
% 23.34/3.49  fof(f66,plain,(
% 23.34/3.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 23.34/3.49    inference(definition_unfolding,[],[f62,f63])).
% 23.34/3.49  
% 23.34/3.49  fof(f67,plain,(
% 23.34/3.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 23.34/3.49    inference(definition_unfolding,[],[f61,f66])).
% 23.34/3.49  
% 23.34/3.49  fof(f68,plain,(
% 23.34/3.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 23.34/3.49    inference(definition_unfolding,[],[f60,f67])).
% 23.34/3.49  
% 23.34/3.49  fof(f69,plain,(
% 23.34/3.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 23.34/3.49    inference(definition_unfolding,[],[f59,f68])).
% 23.34/3.49  
% 23.34/3.49  fof(f70,plain,(
% 23.34/3.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 23.34/3.49    inference(definition_unfolding,[],[f58,f69])).
% 23.34/3.49  
% 23.34/3.49  fof(f81,plain,(
% 23.34/3.49    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k1_xboole_0),
% 23.34/3.49    inference(definition_unfolding,[],[f65,f49,f70])).
% 23.34/3.49  
% 23.34/3.49  fof(f2,axiom,(
% 23.34/3.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f38,plain,(
% 23.34/3.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 23.34/3.49    inference(cnf_transformation,[],[f2])).
% 23.34/3.49  
% 23.34/3.49  fof(f9,axiom,(
% 23.34/3.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f46,plain,(
% 23.34/3.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.34/3.49    inference(cnf_transformation,[],[f9])).
% 23.34/3.49  
% 23.34/3.49  fof(f8,axiom,(
% 23.34/3.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f45,plain,(
% 23.34/3.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 23.34/3.49    inference(cnf_transformation,[],[f8])).
% 23.34/3.49  
% 23.34/3.49  fof(f5,axiom,(
% 23.34/3.49    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f42,plain,(
% 23.34/3.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 23.34/3.49    inference(cnf_transformation,[],[f5])).
% 23.34/3.49  
% 23.34/3.49  fof(f71,plain,(
% 23.34/3.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 23.34/3.49    inference(definition_unfolding,[],[f45,f42])).
% 23.34/3.49  
% 23.34/3.49  fof(f6,axiom,(
% 23.34/3.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f25,plain,(
% 23.34/3.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 23.34/3.49    inference(ennf_transformation,[],[f6])).
% 23.34/3.49  
% 23.34/3.49  fof(f43,plain,(
% 23.34/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 23.34/3.49    inference(cnf_transformation,[],[f25])).
% 23.34/3.49  
% 23.34/3.49  fof(f13,axiom,(
% 23.34/3.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f26,plain,(
% 23.34/3.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 23.34/3.49    inference(ennf_transformation,[],[f13])).
% 23.34/3.49  
% 23.34/3.49  fof(f30,plain,(
% 23.34/3.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.34/3.49    inference(nnf_transformation,[],[f26])).
% 23.34/3.49  
% 23.34/3.49  fof(f31,plain,(
% 23.34/3.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.34/3.49    inference(flattening,[],[f30])).
% 23.34/3.49  
% 23.34/3.49  fof(f32,plain,(
% 23.34/3.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.34/3.49    inference(rectify,[],[f31])).
% 23.34/3.49  
% 23.34/3.49  fof(f33,plain,(
% 23.34/3.49    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 23.34/3.49    introduced(choice_axiom,[])).
% 23.34/3.49  
% 23.34/3.49  fof(f34,plain,(
% 23.34/3.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.34/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 23.34/3.49  
% 23.34/3.49  fof(f52,plain,(
% 23.34/3.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 23.34/3.49    inference(cnf_transformation,[],[f34])).
% 23.34/3.49  
% 23.34/3.49  fof(f77,plain,(
% 23.34/3.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 23.34/3.49    inference(definition_unfolding,[],[f52,f69])).
% 23.34/3.49  
% 23.34/3.49  fof(f84,plain,(
% 23.34/3.49    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 23.34/3.49    inference(equality_resolution,[],[f77])).
% 23.34/3.49  
% 23.34/3.49  fof(f85,plain,(
% 23.34/3.49    ( ! [X2,X0,X5] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2))) )),
% 23.34/3.49    inference(equality_resolution,[],[f84])).
% 23.34/3.49  
% 23.34/3.49  fof(f20,axiom,(
% 23.34/3.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f64,plain,(
% 23.34/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 23.34/3.49    inference(cnf_transformation,[],[f20])).
% 23.34/3.49  
% 23.34/3.49  fof(f80,plain,(
% 23.34/3.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 23.34/3.49    inference(definition_unfolding,[],[f64,f49,f70])).
% 23.34/3.49  
% 23.34/3.49  fof(f7,axiom,(
% 23.34/3.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f44,plain,(
% 23.34/3.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 23.34/3.49    inference(cnf_transformation,[],[f7])).
% 23.34/3.49  
% 23.34/3.49  fof(f3,axiom,(
% 23.34/3.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f23,plain,(
% 23.34/3.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 23.34/3.49    inference(rectify,[],[f3])).
% 23.34/3.49  
% 23.34/3.49  fof(f24,plain,(
% 23.34/3.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 23.34/3.49    inference(ennf_transformation,[],[f23])).
% 23.34/3.49  
% 23.34/3.49  fof(f28,plain,(
% 23.34/3.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 23.34/3.49    introduced(choice_axiom,[])).
% 23.34/3.49  
% 23.34/3.49  fof(f29,plain,(
% 23.34/3.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 23.34/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f28])).
% 23.34/3.49  
% 23.34/3.49  fof(f40,plain,(
% 23.34/3.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 23.34/3.49    inference(cnf_transformation,[],[f29])).
% 23.34/3.49  
% 23.34/3.49  fof(f4,axiom,(
% 23.34/3.49    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 23.34/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.49  
% 23.34/3.49  fof(f41,plain,(
% 23.34/3.49    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 23.34/3.49    inference(cnf_transformation,[],[f4])).
% 23.34/3.49  
% 23.34/3.49  cnf(c_10,plain,
% 23.34/3.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.34/3.49      inference(cnf_transformation,[],[f48]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_9,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 23.34/3.49      inference(cnf_transformation,[],[f47]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_0,plain,
% 23.34/3.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 23.34/3.49      inference(cnf_transformation,[],[f37]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_20,negated_conjecture,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k1_xboole_0 ),
% 23.34/3.49      inference(cnf_transformation,[],[f81]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1,plain,
% 23.34/3.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 23.34/3.49      inference(cnf_transformation,[],[f38]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_313,negated_conjecture,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = k1_xboole_0 ),
% 23.34/3.49      inference(theory_normalisation,[status(thm)],[c_20,c_9,c_1]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_926,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))) = k1_xboole_0 ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_0,c_313]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1126,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_926,c_9]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_8,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.34/3.49      inference(cnf_transformation,[],[f46]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1104,plain,
% 23.34/3.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1133,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),X0)) = X0 ),
% 23.34/3.49      inference(light_normalisation,[status(thm)],[c_1126,c_1104]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1466,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),X0))) = X0 ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_9,c_1133]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1707,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k1_xboole_0)) = k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_10,c_1466]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1727,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_1707,c_8]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1467,plain,
% 23.34/3.49      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k5_xboole_0(sK4,k1_xboole_0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_10,c_1133]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1476,plain,
% 23.34/3.49      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = sK4 ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_1467,c_8]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1483,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(sK4,X0)) = X0 ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_1476,c_1133]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1494,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,X0),X1)) = k5_xboole_0(X0,X1) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_1483,c_9]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1129,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_9,c_10]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1492,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(sK4,X0)) = k5_xboole_0(sK4,k1_xboole_0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_1129,c_1483]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1497,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(sK4,X0)) = sK4 ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_1492,c_8]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_2255,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK4,X0),X1),k5_xboole_0(X0,X1)) = sK4 ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_1494,c_1497]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_5601,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(X1,k5_xboole_0(X0,X1))) = sK4 ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_2255,c_9]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1486,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(X0,sK4)) = X0 ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_1,c_1483]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1717,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(X1,sK4))) = k5_xboole_0(X0,X1) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_9,c_1486]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_5602,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK4,X0),sK4),X0) = k5_xboole_0(sK4,sK4) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_2255,c_1717]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_5607,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK4,X0),sK4),X0) = k1_xboole_0 ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_5602,c_10]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_554,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_6826,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK4,X0),sK4),k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_5607,c_554]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1878,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(sK4,X1))) = k5_xboole_0(X1,X0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_1,c_1494]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_6897,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK4,X2)))) = k5_xboole_0(k5_xboole_0(X1,X2),X0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_554,c_1878]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_5266,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK4,X2)))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_9,c_1878]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_6908,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X2,X0),X1) ),
% 23.34/3.49      inference(light_normalisation,[status(thm)],[c_6897,c_5266]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_7016,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,sK4),k5_xboole_0(k5_xboole_0(X0,X1),X1)) = k5_xboole_0(X0,k1_xboole_0) ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_6826,c_6908]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_7017,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),sK4)) = k5_xboole_0(X1,k1_xboole_0) ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_7016,c_6908]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_7018,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK4,X0))) = k5_xboole_0(X1,k1_xboole_0) ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_7017,c_6908]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_7019,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK4,X1),X1))) = k5_xboole_0(X0,k1_xboole_0) ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_7018,c_6908]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_6890,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK4,X1),X2))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_554,c_1494]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_6931,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,sK4)))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_6890,c_6908]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_7020,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_7019,c_6908,c_6931]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_7021,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_7020,c_8]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1493,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,X0),X0)) = k1_xboole_0 ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_1483,c_1129]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1870,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,X0),X0) = k5_xboole_0(sK4,k1_xboole_0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_1493,c_1483]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1872,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,X0),X0) = sK4 ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_1870,c_8]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_2297,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(sK4,X1) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_1872,c_9]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_9253,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK4,X0))) = k5_xboole_0(sK4,X1) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_7021,c_1494]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_10627,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(X1,X0)) = k5_xboole_0(sK4,X1) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_1483,c_9253]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_10796,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,X1)),X0) = k5_xboole_0(sK4,X1) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_7021,c_10627]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_11439,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(X0,sK4),X1)),X0) = k5_xboole_0(sK4,k5_xboole_0(sK4,X1)) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_10796,c_1717]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_4935,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(X0,sK4),X1)) = k5_xboole_0(X1,X0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_1,c_1717]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_11445,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = k5_xboole_0(sK4,k5_xboole_0(sK4,X0)) ),
% 23.34/3.49      inference(light_normalisation,[status(thm)],[c_11439,c_4935]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_555,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_9833,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,sK4)))) = k5_xboole_0(k5_xboole_0(X2,X1),X0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_555,c_1878]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_9842,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 23.34/3.49      inference(light_normalisation,[status(thm)],[c_9833,c_6931]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_11446,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_11445,c_1483,c_9842]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_11868,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2) = k5_xboole_0(X0,X1) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_9,c_11446]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_26199,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,X0),X0) = k5_xboole_0(k5_xboole_0(sK4,X1),X1) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_2297,c_11868]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_26439,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,X0),X0) = sP0_iProver_split ),
% 23.34/3.49      inference(splitting,
% 23.34/3.49                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 23.34/3.49                [c_26199]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_29512,plain,
% 23.34/3.49      ( sP0_iProver_split = sK4 ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_5601,c_7021,c_26439]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_7,plain,
% 23.34/3.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 23.34/3.49      inference(cnf_transformation,[],[f71]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_538,plain,
% 23.34/3.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 23.34/3.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1279,plain,
% 23.34/3.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_0,c_538]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_2949,plain,
% 23.34/3.49      ( r1_tarski(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_1476,c_1279]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_49828,plain,
% 23.34/3.49      ( r1_tarski(sP0_iProver_split,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
% 23.34/3.49      inference(light_normalisation,[status(thm)],[c_2949,c_29512]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_5,plain,
% 23.34/3.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 23.34/3.49      inference(cnf_transformation,[],[f43]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_540,plain,
% 23.34/3.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 23.34/3.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_49830,plain,
% 23.34/3.49      ( k3_xboole_0(sP0_iProver_split,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = sP0_iProver_split ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_49828,c_540]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_77815,plain,
% 23.34/3.49      ( k5_xboole_0(sP0_iProver_split,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = sP0_iProver_split ),
% 23.34/3.49      inference(light_normalisation,
% 23.34/3.49                [status(thm)],
% 23.34/3.49                [c_1727,c_1727,c_29512,c_49830]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_10825,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,X1)),k5_xboole_0(sK4,X0)) = k5_xboole_0(sK4,k5_xboole_0(sK4,X1)) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_10627,c_10627]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_9749,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(sK4,X1)) = k5_xboole_0(X1,X0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_1483,c_555]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_10857,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,X1)),k5_xboole_0(sK4,X0)) = X1 ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_10825,c_1483,c_9749]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_11243,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(X1,X2))),k5_xboole_0(sK4,k5_xboole_0(X0,X1))) = X2 ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_9,c_10857]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_57622,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,k5_xboole_0(X1,X2))),k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,X1))) = X2 ),
% 23.34/3.49      inference(light_normalisation,
% 23.34/3.49                [status(thm)],
% 23.34/3.49                [c_11243,c_11243,c_29512]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_77868,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,sP0_iProver_split)),k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,sP0_iProver_split))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_77815,c_57622]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_11903,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_11446,c_9]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_29127,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X0)) = k5_xboole_0(X2,X1) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_11903,c_1]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_11400,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,X1)),k5_xboole_0(sK4,X1)) = k5_xboole_0(sK4,k5_xboole_0(sK4,X0)) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_9749,c_10796]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_11470,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,X1)),k5_xboole_0(sK4,X1)) = X0 ),
% 23.34/3.49      inference(light_normalisation,[status(thm)],[c_11400,c_1483]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_12046,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(sK4,k5_xboole_0(X1,X0))) = X1 ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_11470,c_1]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_31187,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sP0_iProver_split,X0),k5_xboole_0(sP0_iProver_split,k5_xboole_0(X1,X0))) = X1 ),
% 23.34/3.49      inference(light_normalisation,
% 23.34/3.49                [status(thm)],
% 23.34/3.49                [c_12046,c_12046,c_29512]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_38627,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,X1)),k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_29127,c_31187]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_78305,plain,
% 23.34/3.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0 ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_77868,c_10,c_38627]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_16,plain,
% 23.34/3.49      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
% 23.34/3.49      inference(cnf_transformation,[],[f85]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_532,plain,
% 23.34/3.49      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) = iProver_top ),
% 23.34/3.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_78778,plain,
% 23.34/3.49      ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_78305,c_532]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_19,plain,
% 23.34/3.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 23.34/3.49      inference(cnf_transformation,[],[f80]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_314,plain,
% 23.34/3.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
% 23.34/3.49      inference(theory_normalisation,[status(thm)],[c_19,c_9,c_1]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1117,plain,
% 23.34/3.49      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k1_xboole_0 ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_314,c_926]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_29572,plain,
% 23.34/3.49      ( k3_tarski(k6_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k1_xboole_0 ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_29512,c_1117]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_78773,plain,
% 23.34/3.49      ( k3_tarski(k6_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,k1_xboole_0)) = k1_xboole_0 ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_78305,c_29572]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1490,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0))) = k5_xboole_0(X0,k3_xboole_0(sK4,X0)) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_314,c_1483]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_11382,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(sK4,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0)))),X0) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_1490,c_10796]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_11479,plain,
% 23.34/3.49      ( k5_xboole_0(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0)),X0) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_11382,c_1483,c_9842]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_13804,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,X0))),k5_xboole_0(sK4,X0)) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0)) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_11479,c_11470]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_556,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_13120,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,X1)),k5_xboole_0(X0,X2)) = k5_xboole_0(X2,k5_xboole_0(sK4,X1)) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_10796,c_556]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_13860,plain,
% 23.34/3.49      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0)) = k5_xboole_0(k3_xboole_0(sK4,X0),k5_xboole_0(sK4,X0)) ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_13804,c_1483,c_13120]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_14750,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0))),k5_xboole_0(sK4,k5_xboole_0(sK4,X0))) = k3_xboole_0(sK4,X0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_13860,c_11470]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_14783,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0))),X0) = k3_xboole_0(sK4,X0) ),
% 23.34/3.49      inference(light_normalisation,[status(thm)],[c_14750,c_1483]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_15210,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK4,X0)),X0) = k3_xboole_0(sK4,X0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_1490,c_14783]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_32841,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,X0)),X0) = k3_xboole_0(sP0_iProver_split,X0) ),
% 23.34/3.49      inference(light_normalisation,
% 23.34/3.49                [status(thm)],
% 23.34/3.49                [c_15210,c_15210,c_29512]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_32855,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sP0_iProver_split)),X0) = k3_xboole_0(sP0_iProver_split,X0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_0,c_32841]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_42637,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,sP0_iProver_split))) = k3_xboole_0(sP0_iProver_split,X0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_32855,c_1]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_47958,plain,
% 23.34/3.49      ( k5_xboole_0(k3_xboole_0(sP0_iProver_split,X0),k3_xboole_0(X0,sP0_iProver_split)) = k5_xboole_0(X0,X0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_42637,c_11868]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_47997,plain,
% 23.34/3.49      ( k5_xboole_0(k3_xboole_0(sP0_iProver_split,X0),k3_xboole_0(X0,sP0_iProver_split)) = k1_xboole_0 ),
% 23.34/3.49      inference(light_normalisation,[status(thm)],[c_47958,c_10]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_49193,plain,
% 23.34/3.49      ( k5_xboole_0(k3_xboole_0(X0,sP0_iProver_split),k3_xboole_0(sP0_iProver_split,X0)) = k1_xboole_0 ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_47997,c_1]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_11871,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X2)) = X1 ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_554,c_11446]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_51872,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,X1))) = k3_xboole_0(X1,sP0_iProver_split) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_49193,c_11871]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_51888,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(sP0_iProver_split,X1))) = k3_xboole_0(X1,sP0_iProver_split) ),
% 23.34/3.49      inference(light_normalisation,[status(thm)],[c_51872,c_8]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1130,plain,
% 23.34/3.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X0,k5_xboole_0(X1,X2))))) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_9,c_314]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_65771,plain,
% 23.34/3.49      ( k3_tarski(k6_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,k5_xboole_0(X0,X0))) = k5_xboole_0(sP0_iProver_split,k3_xboole_0(k5_xboole_0(X0,X0),sP0_iProver_split)) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_51888,c_1130]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_42657,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sP0_iProver_split),X0)) = k3_xboole_0(sP0_iProver_split,X0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_32855,c_9]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_10812,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(sK4,X1))),k5_xboole_0(X1,X0)) = k5_xboole_0(sK4,sK4) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_1878,c_10627]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_4946,plain,
% 23.34/3.49      ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(sK4,X1))) = k5_xboole_0(X0,X1) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_1,c_1717]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_10867,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k5_xboole_0(sK4,sK4) ),
% 23.34/3.49      inference(light_normalisation,[status(thm)],[c_10812,c_4946]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_9743,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X2,X0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_7021,c_555]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_10868,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_10867,c_10,c_9743]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_13002,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X0))) = k5_xboole_0(X2,k1_xboole_0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_10868,c_554]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_13015,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X0))) = X2 ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_13002,c_8,c_9842]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_52582,plain,
% 23.34/3.49      ( k3_xboole_0(sP0_iProver_split,k5_xboole_0(X0,X0)) = k3_xboole_0(k5_xboole_0(X0,X0),sP0_iProver_split) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_42657,c_13015]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_42638,plain,
% 23.34/3.49      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sP0_iProver_split)) = k3_xboole_0(sP0_iProver_split,k1_xboole_0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_32855,c_8]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_6,plain,
% 23.34/3.49      ( r1_tarski(k1_xboole_0,X0) ),
% 23.34/3.49      inference(cnf_transformation,[],[f44]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_539,plain,
% 23.34/3.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 23.34/3.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_33681,plain,
% 23.34/3.49      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_539,c_540]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_42734,plain,
% 23.34/3.49      ( k3_xboole_0(sP0_iProver_split,k1_xboole_0) = k1_xboole_0 ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_42638,c_1104,c_33681]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_52623,plain,
% 23.34/3.49      ( k3_xboole_0(k1_xboole_0,sP0_iProver_split) = k1_xboole_0 ),
% 23.34/3.49      inference(light_normalisation,[status(thm)],[c_52582,c_10,c_42734]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_65839,plain,
% 23.34/3.49      ( k3_tarski(k6_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,k1_xboole_0)) = k5_xboole_0(sP0_iProver_split,k1_xboole_0) ),
% 23.34/3.49      inference(light_normalisation,[status(thm)],[c_65771,c_10,c_52623]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_46485,plain,
% 23.34/3.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X2,X1)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X0,k1_xboole_0)))) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_10868,c_1130]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_13232,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X0)) = X1 ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_556,c_11446]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_26615,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_11446,c_11871]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_33737,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),X3)) = k5_xboole_0(k5_xboole_0(X2,X1),X3) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_13232,c_26615]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_13265,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(X1,k5_xboole_0(sK4,X2))) = k5_xboole_0(k5_xboole_0(X2,X1),X0) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_556,c_9749]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_10175,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(X1,k5_xboole_0(sK4,X2))) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_9749,c_554]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_13293,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 23.34/3.49      inference(light_normalisation,[status(thm)],[c_13265,c_10175]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_33878,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3))) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_33737,c_13293]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_11872,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X0)) = X2 ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_555,c_11446]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_27999,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X1,X0),X3)) = k5_xboole_0(X3,X2) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_11872,c_556]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_26619,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X3)) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_11868,c_11871]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_28047,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_27999,c_13293,c_26619]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_33879,plain,
% 23.34/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_33878,c_13293,c_28047]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_46739,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X0,k1_xboole_0)),X2))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_46485,c_10868,c_33879]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_46740,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X1),k5_xboole_0(X2,k3_xboole_0(X0,k1_xboole_0))))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_46739,c_33879]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1124,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_10,c_9]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_1134,plain,
% 23.34/3.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_1124,c_1104]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_46741,plain,
% 23.34/3.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_46740,c_1134,c_26615]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_65840,plain,
% 23.34/3.49      ( k3_tarski(k6_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,k1_xboole_0)) = sP0_iProver_split ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_65839,c_8,c_46741]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_78774,plain,
% 23.34/3.49      ( sP0_iProver_split = k1_xboole_0 ),
% 23.34/3.49      inference(light_normalisation,[status(thm)],[c_78773,c_65840]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_78786,plain,
% 23.34/3.49      ( r2_hidden(sK2,sP0_iProver_split) = iProver_top ),
% 23.34/3.49      inference(light_normalisation,[status(thm)],[c_78778,c_78774]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_2,plain,
% 23.34/3.49      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 23.34/3.49      inference(cnf_transformation,[],[f40]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_4,plain,
% 23.34/3.49      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 23.34/3.49      inference(cnf_transformation,[],[f41]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_198,plain,
% 23.34/3.49      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 23.34/3.49      | k5_xboole_0(X3,X4) != X2
% 23.34/3.49      | k3_xboole_0(X3,X4) != X1 ),
% 23.34/3.49      inference(resolution_lifted,[status(thm)],[c_2,c_4]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_199,plain,
% 23.34/3.49      ( ~ r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) ),
% 23.34/3.49      inference(unflattening,[status(thm)],[c_198]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_528,plain,
% 23.34/3.49      ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) != iProver_top ),
% 23.34/3.49      inference(predicate_to_equality,[status(thm)],[c_199]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_2064,plain,
% 23.34/3.49      ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(sK4,k5_xboole_0(sK4,X1)),X1)) != iProver_top ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_1483,c_528]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_29567,plain,
% 23.34/3.49      ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(sP0_iProver_split,k5_xboole_0(sP0_iProver_split,X1)),X1)) != iProver_top ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_29512,c_2064]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_77907,plain,
% 23.34/3.49      ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(sP0_iProver_split,sP0_iProver_split),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) != iProver_top ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_77815,c_29567]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_52692,plain,
% 23.34/3.49      ( r1_tarski(k5_xboole_0(sP0_iProver_split,k1_xboole_0),sP0_iProver_split) = iProver_top ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_52623,c_1279]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_52712,plain,
% 23.34/3.49      ( r1_tarski(sP0_iProver_split,sP0_iProver_split) = iProver_top ),
% 23.34/3.49      inference(demodulation,[status(thm)],[c_52692,c_8]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_55573,plain,
% 23.34/3.49      ( k3_xboole_0(sP0_iProver_split,sP0_iProver_split) = sP0_iProver_split ),
% 23.34/3.49      inference(superposition,[status(thm)],[c_52712,c_540]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_78275,plain,
% 23.34/3.49      ( r2_hidden(X0,sP0_iProver_split) != iProver_top ),
% 23.34/3.49      inference(light_normalisation,
% 23.34/3.49                [status(thm)],
% 23.34/3.49                [c_77907,c_49830,c_55573]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(c_78383,plain,
% 23.34/3.49      ( r2_hidden(sK2,sP0_iProver_split) != iProver_top ),
% 23.34/3.49      inference(instantiation,[status(thm)],[c_78275]) ).
% 23.34/3.49  
% 23.34/3.49  cnf(contradiction,plain,
% 23.34/3.49      ( $false ),
% 23.34/3.49      inference(minisat,[status(thm)],[c_78786,c_78383]) ).
% 23.34/3.49  
% 23.34/3.49  
% 23.34/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.34/3.49  
% 23.34/3.49  ------                               Statistics
% 23.34/3.49  
% 23.34/3.49  ------ General
% 23.34/3.49  
% 23.34/3.49  abstr_ref_over_cycles:                  0
% 23.34/3.49  abstr_ref_under_cycles:                 0
% 23.34/3.49  gc_basic_clause_elim:                   0
% 23.34/3.49  forced_gc_time:                         0
% 23.34/3.49  parsing_time:                           0.007
% 23.34/3.49  unif_index_cands_time:                  0.
% 23.34/3.49  unif_index_add_time:                    0.
% 23.34/3.49  orderings_time:                         0.
% 23.34/3.49  out_proof_time:                         0.014
% 23.34/3.49  total_time:                             2.575
% 23.34/3.49  num_of_symbols:                         46
% 23.34/3.49  num_of_terms:                           140559
% 23.34/3.49  
% 23.34/3.49  ------ Preprocessing
% 23.34/3.49  
% 23.34/3.49  num_of_splits:                          0
% 23.34/3.49  num_of_split_atoms:                     2
% 23.34/3.49  num_of_reused_defs:                     0
% 23.34/3.49  num_eq_ax_congr_red:                    21
% 23.34/3.49  num_of_sem_filtered_clauses:            1
% 23.34/3.49  num_of_subtypes:                        0
% 23.34/3.49  monotx_restored_types:                  0
% 23.34/3.49  sat_num_of_epr_types:                   0
% 23.34/3.49  sat_num_of_non_cyclic_types:            0
% 23.34/3.49  sat_guarded_non_collapsed_types:        0
% 23.34/3.49  num_pure_diseq_elim:                    0
% 23.34/3.49  simp_replaced_by:                       0
% 23.34/3.49  res_preprocessed:                       98
% 23.34/3.49  prep_upred:                             0
% 23.34/3.49  prep_unflattend:                        12
% 23.34/3.49  smt_new_axioms:                         0
% 23.34/3.49  pred_elim_cands:                        2
% 23.34/3.49  pred_elim:                              1
% 23.34/3.49  pred_elim_cl:                           1
% 23.34/3.49  pred_elim_cycles:                       4
% 23.34/3.49  merged_defs:                            0
% 23.34/3.49  merged_defs_ncl:                        0
% 23.34/3.49  bin_hyper_res:                          0
% 23.34/3.49  prep_cycles:                            4
% 23.34/3.49  pred_elim_time:                         0.
% 23.34/3.49  splitting_time:                         0.
% 23.34/3.49  sem_filter_time:                        0.
% 23.34/3.49  monotx_time:                            0.
% 23.34/3.49  subtype_inf_time:                       0.
% 23.34/3.49  
% 23.34/3.49  ------ Problem properties
% 23.34/3.49  
% 23.34/3.49  clauses:                                20
% 23.34/3.49  conjectures:                            1
% 23.34/3.49  epr:                                    1
% 23.34/3.49  horn:                                   18
% 23.34/3.49  ground:                                 1
% 23.34/3.49  unary:                                  13
% 23.34/3.49  binary:                                 2
% 23.34/3.49  lits:                                   35
% 23.34/3.49  lits_eq:                                21
% 23.34/3.49  fd_pure:                                0
% 23.34/3.49  fd_pseudo:                              0
% 23.34/3.49  fd_cond:                                0
% 23.34/3.49  fd_pseudo_cond:                         4
% 23.34/3.49  ac_symbols:                             1
% 23.34/3.49  
% 23.34/3.49  ------ Propositional Solver
% 23.34/3.49  
% 23.34/3.49  prop_solver_calls:                      32
% 23.34/3.49  prop_fast_solver_calls:                 788
% 23.34/3.49  smt_solver_calls:                       0
% 23.34/3.49  smt_fast_solver_calls:                  0
% 23.34/3.49  prop_num_of_clauses:                    18943
% 23.34/3.49  prop_preprocess_simplified:             27679
% 23.34/3.49  prop_fo_subsumed:                       0
% 23.34/3.49  prop_solver_time:                       0.
% 23.34/3.49  smt_solver_time:                        0.
% 23.34/3.49  smt_fast_solver_time:                   0.
% 23.34/3.49  prop_fast_solver_time:                  0.
% 23.34/3.49  prop_unsat_core_time:                   0.002
% 23.34/3.49  
% 23.34/3.49  ------ QBF
% 23.34/3.49  
% 23.34/3.49  qbf_q_res:                              0
% 23.34/3.49  qbf_num_tautologies:                    0
% 23.34/3.49  qbf_prep_cycles:                        0
% 23.34/3.49  
% 23.34/3.49  ------ BMC1
% 23.34/3.49  
% 23.34/3.49  bmc1_current_bound:                     -1
% 23.34/3.49  bmc1_last_solved_bound:                 -1
% 23.34/3.49  bmc1_unsat_core_size:                   -1
% 23.34/3.49  bmc1_unsat_core_parents_size:           -1
% 23.34/3.49  bmc1_merge_next_fun:                    0
% 23.34/3.49  bmc1_unsat_core_clauses_time:           0.
% 23.34/3.49  
% 23.34/3.49  ------ Instantiation
% 23.34/3.49  
% 23.34/3.49  inst_num_of_clauses:                    4567
% 23.34/3.49  inst_num_in_passive:                    2183
% 23.34/3.49  inst_num_in_active:                     1042
% 23.34/3.49  inst_num_in_unprocessed:                1346
% 23.34/3.49  inst_num_of_loops:                      1140
% 23.34/3.49  inst_num_of_learning_restarts:          0
% 23.34/3.49  inst_num_moves_active_passive:          95
% 23.34/3.49  inst_lit_activity:                      0
% 23.34/3.49  inst_lit_activity_moves:                0
% 23.34/3.49  inst_num_tautologies:                   0
% 23.34/3.49  inst_num_prop_implied:                  0
% 23.34/3.49  inst_num_existing_simplified:           0
% 23.34/3.49  inst_num_eq_res_simplified:             0
% 23.34/3.49  inst_num_child_elim:                    0
% 23.34/3.49  inst_num_of_dismatching_blockings:      15132
% 23.34/3.49  inst_num_of_non_proper_insts:           9282
% 23.34/3.49  inst_num_of_duplicates:                 0
% 23.34/3.49  inst_inst_num_from_inst_to_res:         0
% 23.34/3.49  inst_dismatching_checking_time:         0.
% 23.34/3.49  
% 23.34/3.49  ------ Resolution
% 23.34/3.49  
% 23.34/3.49  res_num_of_clauses:                     0
% 23.34/3.49  res_num_in_passive:                     0
% 23.34/3.49  res_num_in_active:                      0
% 23.34/3.49  res_num_of_loops:                       102
% 23.34/3.49  res_forward_subset_subsumed:            2293
% 23.34/3.49  res_backward_subset_subsumed:           10
% 23.34/3.49  res_forward_subsumed:                   0
% 23.34/3.49  res_backward_subsumed:                  0
% 23.34/3.49  res_forward_subsumption_resolution:     0
% 23.34/3.49  res_backward_subsumption_resolution:    0
% 23.34/3.49  res_clause_to_clause_subsumption:       79231
% 23.34/3.49  res_orphan_elimination:                 0
% 23.34/3.49  res_tautology_del:                      946
% 23.34/3.49  res_num_eq_res_simplified:              0
% 23.34/3.49  res_num_sel_changes:                    0
% 23.34/3.49  res_moves_from_active_to_pass:          0
% 23.34/3.49  
% 23.34/3.49  ------ Superposition
% 23.34/3.49  
% 23.34/3.49  sup_time_total:                         0.
% 23.34/3.49  sup_time_generating:                    0.
% 23.34/3.49  sup_time_sim_full:                      0.
% 23.34/3.49  sup_time_sim_immed:                     0.
% 23.34/3.49  
% 23.34/3.49  sup_num_of_clauses:                     4436
% 23.34/3.49  sup_num_in_active:                      129
% 23.34/3.49  sup_num_in_passive:                     4307
% 23.34/3.49  sup_num_of_loops:                       226
% 23.34/3.49  sup_fw_superposition:                   12072
% 23.34/3.49  sup_bw_superposition:                   9086
% 23.34/3.49  sup_immediate_simplified:               9578
% 23.34/3.49  sup_given_eliminated:                   7
% 23.34/3.49  comparisons_done:                       0
% 23.34/3.49  comparisons_avoided:                    6
% 23.34/3.49  
% 23.34/3.49  ------ Simplifications
% 23.34/3.49  
% 23.34/3.49  
% 23.34/3.49  sim_fw_subset_subsumed:                 2
% 23.34/3.49  sim_bw_subset_subsumed:                 0
% 23.34/3.49  sim_fw_subsumed:                        981
% 23.34/3.49  sim_bw_subsumed:                        64
% 23.34/3.49  sim_fw_subsumption_res:                 0
% 23.34/3.49  sim_bw_subsumption_res:                 0
% 23.34/3.49  sim_tautology_del:                      0
% 23.34/3.49  sim_eq_tautology_del:                   2206
% 23.34/3.49  sim_eq_res_simp:                        0
% 23.34/3.49  sim_fw_demodulated:                     7787
% 23.34/3.49  sim_bw_demodulated:                     140
% 23.34/3.49  sim_light_normalised:                   3498
% 23.34/3.49  sim_joinable_taut:                      705
% 23.34/3.49  sim_joinable_simp:                      0
% 23.34/3.49  sim_ac_normalised:                      0
% 23.34/3.49  sim_smt_subsumption:                    0
% 23.34/3.49  
%------------------------------------------------------------------------------
