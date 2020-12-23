%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:32 EST 2020

% Result     : Theorem 7.76s
% Output     : CNFRefutation 7.76s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 833 expanded)
%              Number of clauses        :   48 ( 215 expanded)
%              Number of leaves         :   21 ( 238 expanded)
%              Depth                    :   21
%              Number of atoms          :  242 ( 966 expanded)
%              Number of equality atoms :  183 ( 907 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f43,f45])).

fof(f20,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f20])).

fof(f26,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f21])).

fof(f35,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f35])).

fof(f65,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f49,f45])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f67])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f68])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f69])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f70])).

fof(f88,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f65,f66,f71])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f75,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

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
    inference(nnf_transformation,[],[f25])).

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

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f70])).

fof(f91,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f84])).

fof(f92,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f91])).

fof(f4,axiom,(
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
    inference(rectify,[],[f4])).

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

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f39,f45])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_20,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_622,negated_conjecture,
    ( k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_20,c_10,c_1])).

cnf(c_972,plain,
    ( k5_xboole_0(sK4,k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_622,c_0])).

cnf(c_1674,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_972,c_10])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1087,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_1681,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1674,c_1087])).

cnf(c_1865,plain,
    ( k4_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k4_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),X0)) = k5_xboole_0(sK4,k4_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),X0)) ),
    inference(superposition,[status(thm)],[c_0,c_1681])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2197,plain,
    ( k5_xboole_0(sK4,k4_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4) ),
    inference(superposition,[status(thm)],[c_1865,c_4])).

cnf(c_1553,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1554,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_1560,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1554,c_8])).

cnf(c_1556,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_1558,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1556,c_7])).

cnf(c_1561,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1560,c_1558])).

cnf(c_1562,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1553,c_1561])).

cnf(c_2200,plain,
    ( k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4) = sK4 ),
    inference(demodulation,[status(thm)],[c_2197,c_8,c_1562])).

cnf(c_986,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_2722,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k5_xboole_0(X1,k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_986])).

cnf(c_25054,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_4,c_2722])).

cnf(c_25219,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_25054,c_8,c_1562])).

cnf(c_25584,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_25219])).

cnf(c_25927,plain,
    ( k5_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_2200,c_25584])).

cnf(c_1866,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(X0,k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_1681])).

cnf(c_1995,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_10,c_1866])).

cnf(c_2323,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(X1,sK4))) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1995,c_1995,c_2200])).

cnf(c_2331,plain,
    ( k5_xboole_0(sK4,k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k5_xboole_0(sK4,sK4) ),
    inference(superposition,[status(thm)],[c_1681,c_2323])).

cnf(c_2346,plain,
    ( k5_xboole_0(sK4,sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2331,c_972])).

cnf(c_25988,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_25927,c_2200,c_2346])).

cnf(c_16,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_961,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_26183,plain,
    ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_25988,c_961])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_969,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_24776,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1560,c_969])).

cnf(c_24782,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24776,c_1562])).

cnf(c_24799,plain,
    ( r2_hidden(sK2,k1_xboole_0) != iProver_top
    | r1_xboole_0(sK2,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_24782])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1005,plain,
    ( r1_xboole_0(X0,k1_xboole_0)
    | k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1006,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) != k1_xboole_0
    | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1005])).

cnf(c_1008,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k1_xboole_0
    | r1_xboole_0(sK2,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1006])).

cnf(c_43,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26183,c_24799,c_1008,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:05:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.76/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.76/1.50  
% 7.76/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.76/1.50  
% 7.76/1.50  ------  iProver source info
% 7.76/1.50  
% 7.76/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.76/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.76/1.50  git: non_committed_changes: false
% 7.76/1.50  git: last_make_outside_of_git: false
% 7.76/1.50  
% 7.76/1.50  ------ 
% 7.76/1.50  
% 7.76/1.50  ------ Input Options
% 7.76/1.50  
% 7.76/1.50  --out_options                           all
% 7.76/1.50  --tptp_safe_out                         true
% 7.76/1.50  --problem_path                          ""
% 7.76/1.50  --include_path                          ""
% 7.76/1.50  --clausifier                            res/vclausify_rel
% 7.76/1.50  --clausifier_options                    ""
% 7.76/1.50  --stdin                                 false
% 7.76/1.50  --stats_out                             all
% 7.76/1.50  
% 7.76/1.50  ------ General Options
% 7.76/1.50  
% 7.76/1.50  --fof                                   false
% 7.76/1.50  --time_out_real                         305.
% 7.76/1.50  --time_out_virtual                      -1.
% 7.76/1.50  --symbol_type_check                     false
% 7.76/1.50  --clausify_out                          false
% 7.76/1.50  --sig_cnt_out                           false
% 7.76/1.50  --trig_cnt_out                          false
% 7.76/1.50  --trig_cnt_out_tolerance                1.
% 7.76/1.50  --trig_cnt_out_sk_spl                   false
% 7.76/1.50  --abstr_cl_out                          false
% 7.76/1.50  
% 7.76/1.50  ------ Global Options
% 7.76/1.50  
% 7.76/1.50  --schedule                              default
% 7.76/1.50  --add_important_lit                     false
% 7.76/1.50  --prop_solver_per_cl                    1000
% 7.76/1.50  --min_unsat_core                        false
% 7.76/1.50  --soft_assumptions                      false
% 7.76/1.50  --soft_lemma_size                       3
% 7.76/1.50  --prop_impl_unit_size                   0
% 7.76/1.50  --prop_impl_unit                        []
% 7.76/1.50  --share_sel_clauses                     true
% 7.76/1.50  --reset_solvers                         false
% 7.76/1.50  --bc_imp_inh                            [conj_cone]
% 7.76/1.50  --conj_cone_tolerance                   3.
% 7.76/1.50  --extra_neg_conj                        none
% 7.76/1.50  --large_theory_mode                     true
% 7.76/1.50  --prolific_symb_bound                   200
% 7.76/1.50  --lt_threshold                          2000
% 7.76/1.50  --clause_weak_htbl                      true
% 7.76/1.50  --gc_record_bc_elim                     false
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing Options
% 7.76/1.50  
% 7.76/1.50  --preprocessing_flag                    true
% 7.76/1.50  --time_out_prep_mult                    0.1
% 7.76/1.50  --splitting_mode                        input
% 7.76/1.50  --splitting_grd                         true
% 7.76/1.50  --splitting_cvd                         false
% 7.76/1.50  --splitting_cvd_svl                     false
% 7.76/1.50  --splitting_nvd                         32
% 7.76/1.50  --sub_typing                            true
% 7.76/1.50  --prep_gs_sim                           true
% 7.76/1.50  --prep_unflatten                        true
% 7.76/1.50  --prep_res_sim                          true
% 7.76/1.50  --prep_upred                            true
% 7.76/1.50  --prep_sem_filter                       exhaustive
% 7.76/1.50  --prep_sem_filter_out                   false
% 7.76/1.50  --pred_elim                             true
% 7.76/1.50  --res_sim_input                         true
% 7.76/1.50  --eq_ax_congr_red                       true
% 7.76/1.50  --pure_diseq_elim                       true
% 7.76/1.50  --brand_transform                       false
% 7.76/1.50  --non_eq_to_eq                          false
% 7.76/1.50  --prep_def_merge                        true
% 7.76/1.50  --prep_def_merge_prop_impl              false
% 7.76/1.50  --prep_def_merge_mbd                    true
% 7.76/1.50  --prep_def_merge_tr_red                 false
% 7.76/1.50  --prep_def_merge_tr_cl                  false
% 7.76/1.50  --smt_preprocessing                     true
% 7.76/1.50  --smt_ac_axioms                         fast
% 7.76/1.50  --preprocessed_out                      false
% 7.76/1.50  --preprocessed_stats                    false
% 7.76/1.50  
% 7.76/1.50  ------ Abstraction refinement Options
% 7.76/1.50  
% 7.76/1.50  --abstr_ref                             []
% 7.76/1.50  --abstr_ref_prep                        false
% 7.76/1.50  --abstr_ref_until_sat                   false
% 7.76/1.50  --abstr_ref_sig_restrict                funpre
% 7.76/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.76/1.50  --abstr_ref_under                       []
% 7.76/1.50  
% 7.76/1.50  ------ SAT Options
% 7.76/1.50  
% 7.76/1.50  --sat_mode                              false
% 7.76/1.50  --sat_fm_restart_options                ""
% 7.76/1.50  --sat_gr_def                            false
% 7.76/1.50  --sat_epr_types                         true
% 7.76/1.50  --sat_non_cyclic_types                  false
% 7.76/1.50  --sat_finite_models                     false
% 7.76/1.50  --sat_fm_lemmas                         false
% 7.76/1.50  --sat_fm_prep                           false
% 7.76/1.50  --sat_fm_uc_incr                        true
% 7.76/1.50  --sat_out_model                         small
% 7.76/1.50  --sat_out_clauses                       false
% 7.76/1.50  
% 7.76/1.50  ------ QBF Options
% 7.76/1.50  
% 7.76/1.50  --qbf_mode                              false
% 7.76/1.50  --qbf_elim_univ                         false
% 7.76/1.50  --qbf_dom_inst                          none
% 7.76/1.50  --qbf_dom_pre_inst                      false
% 7.76/1.50  --qbf_sk_in                             false
% 7.76/1.50  --qbf_pred_elim                         true
% 7.76/1.50  --qbf_split                             512
% 7.76/1.50  
% 7.76/1.50  ------ BMC1 Options
% 7.76/1.50  
% 7.76/1.50  --bmc1_incremental                      false
% 7.76/1.50  --bmc1_axioms                           reachable_all
% 7.76/1.50  --bmc1_min_bound                        0
% 7.76/1.50  --bmc1_max_bound                        -1
% 7.76/1.50  --bmc1_max_bound_default                -1
% 7.76/1.50  --bmc1_symbol_reachability              true
% 7.76/1.50  --bmc1_property_lemmas                  false
% 7.76/1.50  --bmc1_k_induction                      false
% 7.76/1.50  --bmc1_non_equiv_states                 false
% 7.76/1.50  --bmc1_deadlock                         false
% 7.76/1.50  --bmc1_ucm                              false
% 7.76/1.50  --bmc1_add_unsat_core                   none
% 7.76/1.50  --bmc1_unsat_core_children              false
% 7.76/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.76/1.50  --bmc1_out_stat                         full
% 7.76/1.50  --bmc1_ground_init                      false
% 7.76/1.50  --bmc1_pre_inst_next_state              false
% 7.76/1.50  --bmc1_pre_inst_state                   false
% 7.76/1.50  --bmc1_pre_inst_reach_state             false
% 7.76/1.50  --bmc1_out_unsat_core                   false
% 7.76/1.50  --bmc1_aig_witness_out                  false
% 7.76/1.50  --bmc1_verbose                          false
% 7.76/1.50  --bmc1_dump_clauses_tptp                false
% 7.76/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.76/1.50  --bmc1_dump_file                        -
% 7.76/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.76/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.76/1.50  --bmc1_ucm_extend_mode                  1
% 7.76/1.50  --bmc1_ucm_init_mode                    2
% 7.76/1.50  --bmc1_ucm_cone_mode                    none
% 7.76/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.76/1.50  --bmc1_ucm_relax_model                  4
% 7.76/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.76/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.76/1.50  --bmc1_ucm_layered_model                none
% 7.76/1.50  --bmc1_ucm_max_lemma_size               10
% 7.76/1.50  
% 7.76/1.50  ------ AIG Options
% 7.76/1.50  
% 7.76/1.50  --aig_mode                              false
% 7.76/1.50  
% 7.76/1.50  ------ Instantiation Options
% 7.76/1.50  
% 7.76/1.50  --instantiation_flag                    true
% 7.76/1.50  --inst_sos_flag                         true
% 7.76/1.50  --inst_sos_phase                        true
% 7.76/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.76/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.76/1.50  --inst_lit_sel_side                     num_symb
% 7.76/1.50  --inst_solver_per_active                1400
% 7.76/1.50  --inst_solver_calls_frac                1.
% 7.76/1.50  --inst_passive_queue_type               priority_queues
% 7.76/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.76/1.50  --inst_passive_queues_freq              [25;2]
% 7.76/1.50  --inst_dismatching                      true
% 7.76/1.50  --inst_eager_unprocessed_to_passive     true
% 7.76/1.50  --inst_prop_sim_given                   true
% 7.76/1.50  --inst_prop_sim_new                     false
% 7.76/1.50  --inst_subs_new                         false
% 7.76/1.50  --inst_eq_res_simp                      false
% 7.76/1.50  --inst_subs_given                       false
% 7.76/1.50  --inst_orphan_elimination               true
% 7.76/1.50  --inst_learning_loop_flag               true
% 7.76/1.50  --inst_learning_start                   3000
% 7.76/1.50  --inst_learning_factor                  2
% 7.76/1.50  --inst_start_prop_sim_after_learn       3
% 7.76/1.50  --inst_sel_renew                        solver
% 7.76/1.50  --inst_lit_activity_flag                true
% 7.76/1.50  --inst_restr_to_given                   false
% 7.76/1.50  --inst_activity_threshold               500
% 7.76/1.50  --inst_out_proof                        true
% 7.76/1.50  
% 7.76/1.50  ------ Resolution Options
% 7.76/1.50  
% 7.76/1.50  --resolution_flag                       true
% 7.76/1.50  --res_lit_sel                           adaptive
% 7.76/1.50  --res_lit_sel_side                      none
% 7.76/1.50  --res_ordering                          kbo
% 7.76/1.50  --res_to_prop_solver                    active
% 7.76/1.50  --res_prop_simpl_new                    false
% 7.76/1.50  --res_prop_simpl_given                  true
% 7.76/1.50  --res_passive_queue_type                priority_queues
% 7.76/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.76/1.50  --res_passive_queues_freq               [15;5]
% 7.76/1.50  --res_forward_subs                      full
% 7.76/1.50  --res_backward_subs                     full
% 7.76/1.50  --res_forward_subs_resolution           true
% 7.76/1.50  --res_backward_subs_resolution          true
% 7.76/1.50  --res_orphan_elimination                true
% 7.76/1.50  --res_time_limit                        2.
% 7.76/1.50  --res_out_proof                         true
% 7.76/1.50  
% 7.76/1.50  ------ Superposition Options
% 7.76/1.50  
% 7.76/1.50  --superposition_flag                    true
% 7.76/1.50  --sup_passive_queue_type                priority_queues
% 7.76/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.76/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.76/1.50  --demod_completeness_check              fast
% 7.76/1.50  --demod_use_ground                      true
% 7.76/1.50  --sup_to_prop_solver                    passive
% 7.76/1.50  --sup_prop_simpl_new                    true
% 7.76/1.50  --sup_prop_simpl_given                  true
% 7.76/1.50  --sup_fun_splitting                     true
% 7.76/1.50  --sup_smt_interval                      50000
% 7.76/1.50  
% 7.76/1.50  ------ Superposition Simplification Setup
% 7.76/1.50  
% 7.76/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.76/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.76/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.76/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.76/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.76/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.76/1.50  --sup_immed_triv                        [TrivRules]
% 7.76/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.50  --sup_immed_bw_main                     []
% 7.76/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.76/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.76/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.50  --sup_input_bw                          []
% 7.76/1.50  
% 7.76/1.50  ------ Combination Options
% 7.76/1.50  
% 7.76/1.50  --comb_res_mult                         3
% 7.76/1.50  --comb_sup_mult                         2
% 7.76/1.50  --comb_inst_mult                        10
% 7.76/1.50  
% 7.76/1.50  ------ Debug Options
% 7.76/1.50  
% 7.76/1.50  --dbg_backtrace                         false
% 7.76/1.50  --dbg_dump_prop_clauses                 false
% 7.76/1.50  --dbg_dump_prop_clauses_file            -
% 7.76/1.50  --dbg_out_stat                          false
% 7.76/1.50  ------ Parsing...
% 7.76/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  ------ Proving...
% 7.76/1.50  ------ Problem Properties 
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  clauses                                 21
% 7.76/1.50  conjectures                             1
% 7.76/1.50  EPR                                     0
% 7.76/1.50  Horn                                    18
% 7.76/1.50  unary                                   12
% 7.76/1.50  binary                                  4
% 7.76/1.50  lits                                    38
% 7.76/1.50  lits eq                                 23
% 7.76/1.50  fd_pure                                 0
% 7.76/1.50  fd_pseudo                               0
% 7.76/1.50  fd_cond                                 0
% 7.76/1.50  fd_pseudo_cond                          4
% 7.76/1.50  AC symbols                              1
% 7.76/1.50  
% 7.76/1.50  ------ Schedule dynamic 5 is on 
% 7.76/1.50  
% 7.76/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ 
% 7.76/1.50  Current options:
% 7.76/1.50  ------ 
% 7.76/1.50  
% 7.76/1.50  ------ Input Options
% 7.76/1.50  
% 7.76/1.50  --out_options                           all
% 7.76/1.50  --tptp_safe_out                         true
% 7.76/1.50  --problem_path                          ""
% 7.76/1.50  --include_path                          ""
% 7.76/1.50  --clausifier                            res/vclausify_rel
% 7.76/1.50  --clausifier_options                    ""
% 7.76/1.50  --stdin                                 false
% 7.76/1.50  --stats_out                             all
% 7.76/1.50  
% 7.76/1.50  ------ General Options
% 7.76/1.50  
% 7.76/1.50  --fof                                   false
% 7.76/1.50  --time_out_real                         305.
% 7.76/1.50  --time_out_virtual                      -1.
% 7.76/1.50  --symbol_type_check                     false
% 7.76/1.50  --clausify_out                          false
% 7.76/1.50  --sig_cnt_out                           false
% 7.76/1.50  --trig_cnt_out                          false
% 7.76/1.50  --trig_cnt_out_tolerance                1.
% 7.76/1.50  --trig_cnt_out_sk_spl                   false
% 7.76/1.50  --abstr_cl_out                          false
% 7.76/1.50  
% 7.76/1.50  ------ Global Options
% 7.76/1.50  
% 7.76/1.50  --schedule                              default
% 7.76/1.50  --add_important_lit                     false
% 7.76/1.50  --prop_solver_per_cl                    1000
% 7.76/1.50  --min_unsat_core                        false
% 7.76/1.50  --soft_assumptions                      false
% 7.76/1.50  --soft_lemma_size                       3
% 7.76/1.50  --prop_impl_unit_size                   0
% 7.76/1.50  --prop_impl_unit                        []
% 7.76/1.50  --share_sel_clauses                     true
% 7.76/1.50  --reset_solvers                         false
% 7.76/1.50  --bc_imp_inh                            [conj_cone]
% 7.76/1.50  --conj_cone_tolerance                   3.
% 7.76/1.50  --extra_neg_conj                        none
% 7.76/1.50  --large_theory_mode                     true
% 7.76/1.50  --prolific_symb_bound                   200
% 7.76/1.50  --lt_threshold                          2000
% 7.76/1.50  --clause_weak_htbl                      true
% 7.76/1.50  --gc_record_bc_elim                     false
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing Options
% 7.76/1.50  
% 7.76/1.50  --preprocessing_flag                    true
% 7.76/1.50  --time_out_prep_mult                    0.1
% 7.76/1.50  --splitting_mode                        input
% 7.76/1.50  --splitting_grd                         true
% 7.76/1.50  --splitting_cvd                         false
% 7.76/1.50  --splitting_cvd_svl                     false
% 7.76/1.50  --splitting_nvd                         32
% 7.76/1.50  --sub_typing                            true
% 7.76/1.50  --prep_gs_sim                           true
% 7.76/1.50  --prep_unflatten                        true
% 7.76/1.50  --prep_res_sim                          true
% 7.76/1.50  --prep_upred                            true
% 7.76/1.50  --prep_sem_filter                       exhaustive
% 7.76/1.50  --prep_sem_filter_out                   false
% 7.76/1.50  --pred_elim                             true
% 7.76/1.50  --res_sim_input                         true
% 7.76/1.50  --eq_ax_congr_red                       true
% 7.76/1.50  --pure_diseq_elim                       true
% 7.76/1.50  --brand_transform                       false
% 7.76/1.50  --non_eq_to_eq                          false
% 7.76/1.50  --prep_def_merge                        true
% 7.76/1.50  --prep_def_merge_prop_impl              false
% 7.76/1.50  --prep_def_merge_mbd                    true
% 7.76/1.50  --prep_def_merge_tr_red                 false
% 7.76/1.50  --prep_def_merge_tr_cl                  false
% 7.76/1.50  --smt_preprocessing                     true
% 7.76/1.50  --smt_ac_axioms                         fast
% 7.76/1.50  --preprocessed_out                      false
% 7.76/1.50  --preprocessed_stats                    false
% 7.76/1.50  
% 7.76/1.50  ------ Abstraction refinement Options
% 7.76/1.50  
% 7.76/1.50  --abstr_ref                             []
% 7.76/1.50  --abstr_ref_prep                        false
% 7.76/1.50  --abstr_ref_until_sat                   false
% 7.76/1.50  --abstr_ref_sig_restrict                funpre
% 7.76/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.76/1.50  --abstr_ref_under                       []
% 7.76/1.50  
% 7.76/1.50  ------ SAT Options
% 7.76/1.50  
% 7.76/1.50  --sat_mode                              false
% 7.76/1.50  --sat_fm_restart_options                ""
% 7.76/1.50  --sat_gr_def                            false
% 7.76/1.50  --sat_epr_types                         true
% 7.76/1.50  --sat_non_cyclic_types                  false
% 7.76/1.50  --sat_finite_models                     false
% 7.76/1.50  --sat_fm_lemmas                         false
% 7.76/1.50  --sat_fm_prep                           false
% 7.76/1.50  --sat_fm_uc_incr                        true
% 7.76/1.50  --sat_out_model                         small
% 7.76/1.50  --sat_out_clauses                       false
% 7.76/1.50  
% 7.76/1.50  ------ QBF Options
% 7.76/1.50  
% 7.76/1.50  --qbf_mode                              false
% 7.76/1.50  --qbf_elim_univ                         false
% 7.76/1.50  --qbf_dom_inst                          none
% 7.76/1.50  --qbf_dom_pre_inst                      false
% 7.76/1.50  --qbf_sk_in                             false
% 7.76/1.50  --qbf_pred_elim                         true
% 7.76/1.50  --qbf_split                             512
% 7.76/1.50  
% 7.76/1.50  ------ BMC1 Options
% 7.76/1.50  
% 7.76/1.50  --bmc1_incremental                      false
% 7.76/1.50  --bmc1_axioms                           reachable_all
% 7.76/1.50  --bmc1_min_bound                        0
% 7.76/1.50  --bmc1_max_bound                        -1
% 7.76/1.50  --bmc1_max_bound_default                -1
% 7.76/1.50  --bmc1_symbol_reachability              true
% 7.76/1.50  --bmc1_property_lemmas                  false
% 7.76/1.50  --bmc1_k_induction                      false
% 7.76/1.50  --bmc1_non_equiv_states                 false
% 7.76/1.50  --bmc1_deadlock                         false
% 7.76/1.50  --bmc1_ucm                              false
% 7.76/1.50  --bmc1_add_unsat_core                   none
% 7.76/1.50  --bmc1_unsat_core_children              false
% 7.76/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.76/1.50  --bmc1_out_stat                         full
% 7.76/1.50  --bmc1_ground_init                      false
% 7.76/1.50  --bmc1_pre_inst_next_state              false
% 7.76/1.50  --bmc1_pre_inst_state                   false
% 7.76/1.50  --bmc1_pre_inst_reach_state             false
% 7.76/1.50  --bmc1_out_unsat_core                   false
% 7.76/1.50  --bmc1_aig_witness_out                  false
% 7.76/1.50  --bmc1_verbose                          false
% 7.76/1.50  --bmc1_dump_clauses_tptp                false
% 7.76/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.76/1.50  --bmc1_dump_file                        -
% 7.76/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.76/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.76/1.50  --bmc1_ucm_extend_mode                  1
% 7.76/1.50  --bmc1_ucm_init_mode                    2
% 7.76/1.50  --bmc1_ucm_cone_mode                    none
% 7.76/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.76/1.50  --bmc1_ucm_relax_model                  4
% 7.76/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.76/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.76/1.50  --bmc1_ucm_layered_model                none
% 7.76/1.50  --bmc1_ucm_max_lemma_size               10
% 7.76/1.50  
% 7.76/1.50  ------ AIG Options
% 7.76/1.50  
% 7.76/1.50  --aig_mode                              false
% 7.76/1.50  
% 7.76/1.50  ------ Instantiation Options
% 7.76/1.50  
% 7.76/1.50  --instantiation_flag                    true
% 7.76/1.50  --inst_sos_flag                         true
% 7.76/1.50  --inst_sos_phase                        true
% 7.76/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.76/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.76/1.50  --inst_lit_sel_side                     none
% 7.76/1.50  --inst_solver_per_active                1400
% 7.76/1.50  --inst_solver_calls_frac                1.
% 7.76/1.50  --inst_passive_queue_type               priority_queues
% 7.76/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.76/1.50  --inst_passive_queues_freq              [25;2]
% 7.76/1.50  --inst_dismatching                      true
% 7.76/1.50  --inst_eager_unprocessed_to_passive     true
% 7.76/1.50  --inst_prop_sim_given                   true
% 7.76/1.50  --inst_prop_sim_new                     false
% 7.76/1.50  --inst_subs_new                         false
% 7.76/1.50  --inst_eq_res_simp                      false
% 7.76/1.50  --inst_subs_given                       false
% 7.76/1.50  --inst_orphan_elimination               true
% 7.76/1.50  --inst_learning_loop_flag               true
% 7.76/1.50  --inst_learning_start                   3000
% 7.76/1.50  --inst_learning_factor                  2
% 7.76/1.50  --inst_start_prop_sim_after_learn       3
% 7.76/1.50  --inst_sel_renew                        solver
% 7.76/1.50  --inst_lit_activity_flag                true
% 7.76/1.50  --inst_restr_to_given                   false
% 7.76/1.50  --inst_activity_threshold               500
% 7.76/1.50  --inst_out_proof                        true
% 7.76/1.50  
% 7.76/1.50  ------ Resolution Options
% 7.76/1.50  
% 7.76/1.50  --resolution_flag                       false
% 7.76/1.50  --res_lit_sel                           adaptive
% 7.76/1.50  --res_lit_sel_side                      none
% 7.76/1.50  --res_ordering                          kbo
% 7.76/1.50  --res_to_prop_solver                    active
% 7.76/1.50  --res_prop_simpl_new                    false
% 7.76/1.50  --res_prop_simpl_given                  true
% 7.76/1.50  --res_passive_queue_type                priority_queues
% 7.76/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.76/1.50  --res_passive_queues_freq               [15;5]
% 7.76/1.50  --res_forward_subs                      full
% 7.76/1.50  --res_backward_subs                     full
% 7.76/1.50  --res_forward_subs_resolution           true
% 7.76/1.50  --res_backward_subs_resolution          true
% 7.76/1.50  --res_orphan_elimination                true
% 7.76/1.50  --res_time_limit                        2.
% 7.76/1.50  --res_out_proof                         true
% 7.76/1.50  
% 7.76/1.50  ------ Superposition Options
% 7.76/1.50  
% 7.76/1.50  --superposition_flag                    true
% 7.76/1.50  --sup_passive_queue_type                priority_queues
% 7.76/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.76/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.76/1.50  --demod_completeness_check              fast
% 7.76/1.50  --demod_use_ground                      true
% 7.76/1.50  --sup_to_prop_solver                    passive
% 7.76/1.50  --sup_prop_simpl_new                    true
% 7.76/1.50  --sup_prop_simpl_given                  true
% 7.76/1.50  --sup_fun_splitting                     true
% 7.76/1.50  --sup_smt_interval                      50000
% 7.76/1.50  
% 7.76/1.50  ------ Superposition Simplification Setup
% 7.76/1.50  
% 7.76/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.76/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.76/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.76/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.76/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.76/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.76/1.50  --sup_immed_triv                        [TrivRules]
% 7.76/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.50  --sup_immed_bw_main                     []
% 7.76/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.76/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.76/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.50  --sup_input_bw                          []
% 7.76/1.50  
% 7.76/1.50  ------ Combination Options
% 7.76/1.50  
% 7.76/1.50  --comb_res_mult                         3
% 7.76/1.50  --comb_sup_mult                         2
% 7.76/1.50  --comb_inst_mult                        10
% 7.76/1.50  
% 7.76/1.50  ------ Debug Options
% 7.76/1.50  
% 7.76/1.50  --dbg_backtrace                         false
% 7.76/1.50  --dbg_dump_prop_clauses                 false
% 7.76/1.50  --dbg_dump_prop_clauses_file            -
% 7.76/1.50  --dbg_out_stat                          false
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  % SZS status Theorem for theBenchmark.p
% 7.76/1.50  
% 7.76/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.76/1.50  
% 7.76/1.50  fof(f5,axiom,(
% 7.76/1.50    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f43,plain,(
% 7.76/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f5])).
% 7.76/1.50  
% 7.76/1.50  fof(f7,axiom,(
% 7.76/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f45,plain,(
% 7.76/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.76/1.50    inference(cnf_transformation,[],[f7])).
% 7.76/1.50  
% 7.76/1.50  fof(f72,plain,(
% 7.76/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1)) )),
% 7.76/1.50    inference(definition_unfolding,[],[f43,f45])).
% 7.76/1.50  
% 7.76/1.50  fof(f20,conjecture,(
% 7.76/1.50    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f21,negated_conjecture,(
% 7.76/1.50    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 7.76/1.50    inference(negated_conjecture,[],[f20])).
% 7.76/1.50  
% 7.76/1.50  fof(f26,plain,(
% 7.76/1.50    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 7.76/1.50    inference(ennf_transformation,[],[f21])).
% 7.76/1.50  
% 7.76/1.50  fof(f35,plain,(
% 7.76/1.50    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 7.76/1.50    introduced(choice_axiom,[])).
% 7.76/1.50  
% 7.76/1.50  fof(f36,plain,(
% 7.76/1.50    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 7.76/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f35])).
% 7.76/1.50  
% 7.76/1.50  fof(f65,plain,(
% 7.76/1.50    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 7.76/1.50    inference(cnf_transformation,[],[f36])).
% 7.76/1.50  
% 7.76/1.50  fof(f11,axiom,(
% 7.76/1.50    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f49,plain,(
% 7.76/1.50    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f11])).
% 7.76/1.50  
% 7.76/1.50  fof(f66,plain,(
% 7.76/1.50    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1)) )),
% 7.76/1.50    inference(definition_unfolding,[],[f49,f45])).
% 7.76/1.50  
% 7.76/1.50  fof(f13,axiom,(
% 7.76/1.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f58,plain,(
% 7.76/1.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f13])).
% 7.76/1.50  
% 7.76/1.50  fof(f14,axiom,(
% 7.76/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f59,plain,(
% 7.76/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f14])).
% 7.76/1.50  
% 7.76/1.50  fof(f15,axiom,(
% 7.76/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f60,plain,(
% 7.76/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f15])).
% 7.76/1.50  
% 7.76/1.50  fof(f16,axiom,(
% 7.76/1.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f61,plain,(
% 7.76/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f16])).
% 7.76/1.50  
% 7.76/1.50  fof(f17,axiom,(
% 7.76/1.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f62,plain,(
% 7.76/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f17])).
% 7.76/1.50  
% 7.76/1.50  fof(f18,axiom,(
% 7.76/1.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f63,plain,(
% 7.76/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f18])).
% 7.76/1.50  
% 7.76/1.50  fof(f67,plain,(
% 7.76/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.76/1.50    inference(definition_unfolding,[],[f62,f63])).
% 7.76/1.50  
% 7.76/1.50  fof(f68,plain,(
% 7.76/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.76/1.50    inference(definition_unfolding,[],[f61,f67])).
% 7.76/1.50  
% 7.76/1.50  fof(f69,plain,(
% 7.76/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.76/1.50    inference(definition_unfolding,[],[f60,f68])).
% 7.76/1.50  
% 7.76/1.50  fof(f70,plain,(
% 7.76/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.76/1.50    inference(definition_unfolding,[],[f59,f69])).
% 7.76/1.50  
% 7.76/1.50  fof(f71,plain,(
% 7.76/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.76/1.50    inference(definition_unfolding,[],[f58,f70])).
% 7.76/1.50  
% 7.76/1.50  fof(f88,plain,(
% 7.76/1.50    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = k1_xboole_0),
% 7.76/1.50    inference(definition_unfolding,[],[f65,f66,f71])).
% 7.76/1.50  
% 7.76/1.50  fof(f10,axiom,(
% 7.76/1.50    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f48,plain,(
% 7.76/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f10])).
% 7.76/1.50  
% 7.76/1.50  fof(f1,axiom,(
% 7.76/1.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f37,plain,(
% 7.76/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f1])).
% 7.76/1.50  
% 7.76/1.50  fof(f8,axiom,(
% 7.76/1.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f46,plain,(
% 7.76/1.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.76/1.50    inference(cnf_transformation,[],[f8])).
% 7.76/1.50  
% 7.76/1.50  fof(f3,axiom,(
% 7.76/1.50    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f22,plain,(
% 7.76/1.50    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.76/1.50    inference(rectify,[],[f3])).
% 7.76/1.50  
% 7.76/1.50  fof(f40,plain,(
% 7.76/1.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.76/1.50    inference(cnf_transformation,[],[f22])).
% 7.76/1.50  
% 7.76/1.50  fof(f75,plain,(
% 7.76/1.50    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 7.76/1.50    inference(definition_unfolding,[],[f40,f45])).
% 7.76/1.50  
% 7.76/1.50  fof(f6,axiom,(
% 7.76/1.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f44,plain,(
% 7.76/1.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.76/1.50    inference(cnf_transformation,[],[f6])).
% 7.76/1.50  
% 7.76/1.50  fof(f78,plain,(
% 7.76/1.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.76/1.50    inference(definition_unfolding,[],[f44,f45])).
% 7.76/1.50  
% 7.76/1.50  fof(f12,axiom,(
% 7.76/1.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f25,plain,(
% 7.76/1.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.76/1.50    inference(ennf_transformation,[],[f12])).
% 7.76/1.50  
% 7.76/1.50  fof(f30,plain,(
% 7.76/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.76/1.50    inference(nnf_transformation,[],[f25])).
% 7.76/1.50  
% 7.76/1.50  fof(f31,plain,(
% 7.76/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.76/1.50    inference(flattening,[],[f30])).
% 7.76/1.50  
% 7.76/1.50  fof(f32,plain,(
% 7.76/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.76/1.50    inference(rectify,[],[f31])).
% 7.76/1.50  
% 7.76/1.50  fof(f33,plain,(
% 7.76/1.50    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 7.76/1.50    introduced(choice_axiom,[])).
% 7.76/1.50  
% 7.76/1.50  fof(f34,plain,(
% 7.76/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.76/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 7.76/1.50  
% 7.76/1.50  fof(f52,plain,(
% 7.76/1.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.76/1.50    inference(cnf_transformation,[],[f34])).
% 7.76/1.50  
% 7.76/1.50  fof(f84,plain,(
% 7.76/1.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.76/1.50    inference(definition_unfolding,[],[f52,f70])).
% 7.76/1.50  
% 7.76/1.50  fof(f91,plain,(
% 7.76/1.50    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 7.76/1.50    inference(equality_resolution,[],[f84])).
% 7.76/1.50  
% 7.76/1.50  fof(f92,plain,(
% 7.76/1.50    ( ! [X2,X0,X5] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2))) )),
% 7.76/1.50    inference(equality_resolution,[],[f91])).
% 7.76/1.50  
% 7.76/1.50  fof(f4,axiom,(
% 7.76/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f23,plain,(
% 7.76/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.76/1.50    inference(rectify,[],[f4])).
% 7.76/1.50  
% 7.76/1.50  fof(f24,plain,(
% 7.76/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.76/1.50    inference(ennf_transformation,[],[f23])).
% 7.76/1.50  
% 7.76/1.50  fof(f28,plain,(
% 7.76/1.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 7.76/1.50    introduced(choice_axiom,[])).
% 7.76/1.50  
% 7.76/1.50  fof(f29,plain,(
% 7.76/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.76/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f28])).
% 7.76/1.50  
% 7.76/1.50  fof(f42,plain,(
% 7.76/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.76/1.50    inference(cnf_transformation,[],[f29])).
% 7.76/1.50  
% 7.76/1.50  fof(f76,plain,(
% 7.76/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.76/1.50    inference(definition_unfolding,[],[f42,f45])).
% 7.76/1.50  
% 7.76/1.50  fof(f2,axiom,(
% 7.76/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.76/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f27,plain,(
% 7.76/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.76/1.50    inference(nnf_transformation,[],[f2])).
% 7.76/1.50  
% 7.76/1.50  fof(f39,plain,(
% 7.76/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.76/1.50    inference(cnf_transformation,[],[f27])).
% 7.76/1.50  
% 7.76/1.50  fof(f73,plain,(
% 7.76/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.76/1.50    inference(definition_unfolding,[],[f39,f45])).
% 7.76/1.50  
% 7.76/1.50  cnf(c_0,plain,
% 7.76/1.50      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.76/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_20,negated_conjecture,
% 7.76/1.50      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = k1_xboole_0 ),
% 7.76/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_10,plain,
% 7.76/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.76/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1,plain,
% 7.76/1.50      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.76/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_622,negated_conjecture,
% 7.76/1.50      ( k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))) = k1_xboole_0 ),
% 7.76/1.50      inference(theory_normalisation,[status(thm)],[c_20,c_10,c_1]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_972,plain,
% 7.76/1.50      ( k5_xboole_0(sK4,k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k1_xboole_0 ),
% 7.76/1.50      inference(demodulation,[status(thm)],[c_622,c_0]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1674,plain,
% 7.76/1.50      ( k5_xboole_0(sK4,k5_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_972,c_10]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_8,plain,
% 7.76/1.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.76/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1087,plain,
% 7.76/1.50      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1681,plain,
% 7.76/1.50      ( k5_xboole_0(sK4,k5_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),X0)) = X0 ),
% 7.76/1.50      inference(light_normalisation,[status(thm)],[c_1674,c_1087]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1865,plain,
% 7.76/1.50      ( k4_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k4_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),X0)) = k5_xboole_0(sK4,k4_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),X0)) ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_0,c_1681]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_4,plain,
% 7.76/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 7.76/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_2197,plain,
% 7.76/1.50      ( k5_xboole_0(sK4,k4_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4) ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_1865,c_4]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1553,plain,
% 7.76/1.50      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_7,plain,
% 7.76/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.76/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1554,plain,
% 7.76/1.50      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1560,plain,
% 7.76/1.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.76/1.50      inference(light_normalisation,[status(thm)],[c_1554,c_8]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1556,plain,
% 7.76/1.50      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1558,plain,
% 7.76/1.50      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.76/1.50      inference(light_normalisation,[status(thm)],[c_1556,c_7]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1561,plain,
% 7.76/1.50      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.76/1.50      inference(demodulation,[status(thm)],[c_1560,c_1558]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1562,plain,
% 7.76/1.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.76/1.50      inference(demodulation,[status(thm)],[c_1553,c_1561]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_2200,plain,
% 7.76/1.50      ( k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4) = sK4 ),
% 7.76/1.50      inference(demodulation,[status(thm)],[c_2197,c_8,c_1562]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_986,plain,
% 7.76/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_2722,plain,
% 7.76/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k5_xboole_0(X1,k4_xboole_0(X0,X2)) ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_0,c_986]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_25054,plain,
% 7.76/1.50      ( k5_xboole_0(X0,k4_xboole_0(X1,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,X1)) ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_4,c_2722]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_25219,plain,
% 7.76/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.76/1.50      inference(demodulation,[status(thm)],[c_25054,c_8,c_1562]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_25584,plain,
% 7.76/1.50      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_0,c_25219]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_25927,plain,
% 7.76/1.50      ( k5_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_2200,c_25584]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1866,plain,
% 7.76/1.50      ( k5_xboole_0(sK4,k5_xboole_0(X0,k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = X0 ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_1,c_1681]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1995,plain,
% 7.76/1.50      ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))) = k5_xboole_0(X0,X1) ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_10,c_1866]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_2323,plain,
% 7.76/1.50      ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(X1,sK4))) = k5_xboole_0(X0,X1) ),
% 7.76/1.50      inference(light_normalisation,[status(thm)],[c_1995,c_1995,c_2200]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_2331,plain,
% 7.76/1.50      ( k5_xboole_0(sK4,k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k5_xboole_0(sK4,sK4) ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_1681,c_2323]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_2346,plain,
% 7.76/1.50      ( k5_xboole_0(sK4,sK4) = k1_xboole_0 ),
% 7.76/1.50      inference(light_normalisation,[status(thm)],[c_2331,c_972]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_25988,plain,
% 7.76/1.50      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0 ),
% 7.76/1.50      inference(light_normalisation,
% 7.76/1.50                [status(thm)],
% 7.76/1.50                [c_25927,c_2200,c_2346]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_16,plain,
% 7.76/1.51      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
% 7.76/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_961,plain,
% 7.76/1.51      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) = iProver_top ),
% 7.76/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_26183,plain,
% 7.76/1.51      ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_25988,c_961]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_5,plain,
% 7.76/1.51      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 7.76/1.51      | ~ r1_xboole_0(X1,X2) ),
% 7.76/1.51      inference(cnf_transformation,[],[f76]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_969,plain,
% 7.76/1.51      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 7.76/1.51      | r1_xboole_0(X1,X2) != iProver_top ),
% 7.76/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_24776,plain,
% 7.76/1.51      ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top
% 7.76/1.51      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 7.76/1.51      inference(superposition,[status(thm)],[c_1560,c_969]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_24782,plain,
% 7.76/1.51      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.76/1.51      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 7.76/1.51      inference(demodulation,[status(thm)],[c_24776,c_1562]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_24799,plain,
% 7.76/1.51      ( r2_hidden(sK2,k1_xboole_0) != iProver_top
% 7.76/1.51      | r1_xboole_0(sK2,k1_xboole_0) != iProver_top ),
% 7.76/1.51      inference(instantiation,[status(thm)],[c_24782]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_2,plain,
% 7.76/1.51      ( r1_xboole_0(X0,X1)
% 7.76/1.51      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 7.76/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1005,plain,
% 7.76/1.51      ( r1_xboole_0(X0,k1_xboole_0)
% 7.76/1.51      | k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) != k1_xboole_0 ),
% 7.76/1.51      inference(instantiation,[status(thm)],[c_2]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1006,plain,
% 7.76/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) != k1_xboole_0
% 7.76/1.51      | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.76/1.51      inference(predicate_to_equality,[status(thm)],[c_1005]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_1008,plain,
% 7.76/1.51      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k1_xboole_0
% 7.76/1.51      | r1_xboole_0(sK2,k1_xboole_0) = iProver_top ),
% 7.76/1.51      inference(instantiation,[status(thm)],[c_1006]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(c_43,plain,
% 7.76/1.51      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 7.76/1.51      inference(instantiation,[status(thm)],[c_7]) ).
% 7.76/1.51  
% 7.76/1.51  cnf(contradiction,plain,
% 7.76/1.51      ( $false ),
% 7.76/1.51      inference(minisat,[status(thm)],[c_26183,c_24799,c_1008,c_43]) ).
% 7.76/1.51  
% 7.76/1.51  
% 7.76/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.76/1.51  
% 7.76/1.51  ------                               Statistics
% 7.76/1.51  
% 7.76/1.51  ------ General
% 7.76/1.51  
% 7.76/1.51  abstr_ref_over_cycles:                  0
% 7.76/1.51  abstr_ref_under_cycles:                 0
% 7.76/1.51  gc_basic_clause_elim:                   0
% 7.76/1.51  forced_gc_time:                         0
% 7.76/1.51  parsing_time:                           0.01
% 7.76/1.51  unif_index_cands_time:                  0.
% 7.76/1.51  unif_index_add_time:                    0.
% 7.76/1.51  orderings_time:                         0.
% 7.76/1.51  out_proof_time:                         0.008
% 7.76/1.51  total_time:                             0.827
% 7.76/1.51  num_of_symbols:                         43
% 7.76/1.51  num_of_terms:                           44664
% 7.76/1.51  
% 7.76/1.51  ------ Preprocessing
% 7.76/1.51  
% 7.76/1.51  num_of_splits:                          0
% 7.76/1.51  num_of_split_atoms:                     0
% 7.76/1.51  num_of_reused_defs:                     0
% 7.76/1.51  num_eq_ax_congr_red:                    14
% 7.76/1.51  num_of_sem_filtered_clauses:            1
% 7.76/1.51  num_of_subtypes:                        0
% 7.76/1.51  monotx_restored_types:                  0
% 7.76/1.51  sat_num_of_epr_types:                   0
% 7.76/1.51  sat_num_of_non_cyclic_types:            0
% 7.76/1.51  sat_guarded_non_collapsed_types:        0
% 7.76/1.51  num_pure_diseq_elim:                    0
% 7.76/1.51  simp_replaced_by:                       0
% 7.76/1.51  res_preprocessed:                       80
% 7.76/1.51  prep_upred:                             0
% 7.76/1.51  prep_unflattend:                        32
% 7.76/1.51  smt_new_axioms:                         0
% 7.76/1.51  pred_elim_cands:                        2
% 7.76/1.51  pred_elim:                              0
% 7.76/1.51  pred_elim_cl:                           0
% 7.76/1.51  pred_elim_cycles:                       2
% 7.76/1.51  merged_defs:                            6
% 7.76/1.51  merged_defs_ncl:                        0
% 7.76/1.51  bin_hyper_res:                          6
% 7.76/1.51  prep_cycles:                            3
% 7.76/1.51  pred_elim_time:                         0.006
% 7.76/1.51  splitting_time:                         0.
% 7.76/1.51  sem_filter_time:                        0.
% 7.76/1.51  monotx_time:                            0.
% 7.76/1.51  subtype_inf_time:                       0.
% 7.76/1.51  
% 7.76/1.51  ------ Problem properties
% 7.76/1.51  
% 7.76/1.51  clauses:                                21
% 7.76/1.51  conjectures:                            1
% 7.76/1.51  epr:                                    0
% 7.76/1.51  horn:                                   18
% 7.76/1.51  ground:                                 1
% 7.76/1.51  unary:                                  12
% 7.76/1.51  binary:                                 4
% 7.76/1.51  lits:                                   38
% 7.76/1.51  lits_eq:                                23
% 7.76/1.51  fd_pure:                                0
% 7.76/1.51  fd_pseudo:                              0
% 7.76/1.51  fd_cond:                                0
% 7.76/1.51  fd_pseudo_cond:                         4
% 7.76/1.51  ac_symbols:                             1
% 7.76/1.51  
% 7.76/1.51  ------ Propositional Solver
% 7.76/1.51  
% 7.76/1.51  prop_solver_calls:                      26
% 7.76/1.51  prop_fast_solver_calls:                 589
% 7.76/1.51  smt_solver_calls:                       0
% 7.76/1.51  smt_fast_solver_calls:                  0
% 7.76/1.51  prop_num_of_clauses:                    6145
% 7.76/1.51  prop_preprocess_simplified:             9691
% 7.76/1.51  prop_fo_subsumed:                       0
% 7.76/1.51  prop_solver_time:                       0.
% 7.76/1.51  smt_solver_time:                        0.
% 7.76/1.51  smt_fast_solver_time:                   0.
% 7.76/1.51  prop_fast_solver_time:                  0.
% 7.76/1.51  prop_unsat_core_time:                   0.
% 7.76/1.51  
% 7.76/1.51  ------ QBF
% 7.76/1.51  
% 7.76/1.51  qbf_q_res:                              0
% 7.76/1.51  qbf_num_tautologies:                    0
% 7.76/1.51  qbf_prep_cycles:                        0
% 7.76/1.51  
% 7.76/1.51  ------ BMC1
% 7.76/1.51  
% 7.76/1.51  bmc1_current_bound:                     -1
% 7.76/1.51  bmc1_last_solved_bound:                 -1
% 7.76/1.51  bmc1_unsat_core_size:                   -1
% 7.76/1.51  bmc1_unsat_core_parents_size:           -1
% 7.76/1.51  bmc1_merge_next_fun:                    0
% 7.76/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.76/1.51  
% 7.76/1.51  ------ Instantiation
% 7.76/1.51  
% 7.76/1.51  inst_num_of_clauses:                    1363
% 7.76/1.51  inst_num_in_passive:                    307
% 7.76/1.51  inst_num_in_active:                     536
% 7.76/1.51  inst_num_in_unprocessed:                521
% 7.76/1.51  inst_num_of_loops:                      650
% 7.76/1.51  inst_num_of_learning_restarts:          0
% 7.76/1.51  inst_num_moves_active_passive:          110
% 7.76/1.51  inst_lit_activity:                      0
% 7.76/1.51  inst_lit_activity_moves:                0
% 7.76/1.51  inst_num_tautologies:                   0
% 7.76/1.51  inst_num_prop_implied:                  0
% 7.76/1.51  inst_num_existing_simplified:           0
% 7.76/1.51  inst_num_eq_res_simplified:             0
% 7.76/1.51  inst_num_child_elim:                    0
% 7.76/1.51  inst_num_of_dismatching_blockings:      1816
% 7.76/1.51  inst_num_of_non_proper_insts:           2057
% 7.76/1.51  inst_num_of_duplicates:                 0
% 7.76/1.51  inst_inst_num_from_inst_to_res:         0
% 7.76/1.51  inst_dismatching_checking_time:         0.
% 7.76/1.51  
% 7.76/1.51  ------ Resolution
% 7.76/1.51  
% 7.76/1.51  res_num_of_clauses:                     0
% 7.76/1.51  res_num_in_passive:                     0
% 7.76/1.51  res_num_in_active:                      0
% 7.76/1.51  res_num_of_loops:                       83
% 7.76/1.51  res_forward_subset_subsumed:            1004
% 7.76/1.51  res_backward_subset_subsumed:           6
% 7.76/1.51  res_forward_subsumed:                   0
% 7.76/1.51  res_backward_subsumed:                  0
% 7.76/1.51  res_forward_subsumption_resolution:     1
% 7.76/1.51  res_backward_subsumption_resolution:    0
% 7.76/1.51  res_clause_to_clause_subsumption:       21418
% 7.76/1.51  res_orphan_elimination:                 0
% 7.76/1.51  res_tautology_del:                      131
% 7.76/1.51  res_num_eq_res_simplified:              0
% 7.76/1.51  res_num_sel_changes:                    0
% 7.76/1.51  res_moves_from_active_to_pass:          0
% 7.76/1.51  
% 7.76/1.51  ------ Superposition
% 7.76/1.51  
% 7.76/1.51  sup_time_total:                         0.
% 7.76/1.51  sup_time_generating:                    0.
% 7.76/1.51  sup_time_sim_full:                      0.
% 7.76/1.51  sup_time_sim_immed:                     0.
% 7.76/1.51  
% 7.76/1.51  sup_num_of_clauses:                     1475
% 7.76/1.51  sup_num_in_active:                      117
% 7.76/1.51  sup_num_in_passive:                     1358
% 7.76/1.51  sup_num_of_loops:                       128
% 7.76/1.51  sup_fw_superposition:                   4270
% 7.76/1.51  sup_bw_superposition:                   3739
% 7.76/1.51  sup_immediate_simplified:               4771
% 7.76/1.51  sup_given_eliminated:                   2
% 7.76/1.51  comparisons_done:                       0
% 7.76/1.51  comparisons_avoided:                    6
% 7.76/1.51  
% 7.76/1.51  ------ Simplifications
% 7.76/1.51  
% 7.76/1.51  
% 7.76/1.51  sim_fw_subset_subsumed:                 6
% 7.76/1.51  sim_bw_subset_subsumed:                 0
% 7.76/1.51  sim_fw_subsumed:                        378
% 7.76/1.51  sim_bw_subsumed:                        20
% 7.76/1.51  sim_fw_subsumption_res:                 0
% 7.76/1.51  sim_bw_subsumption_res:                 0
% 7.76/1.51  sim_tautology_del:                      2
% 7.76/1.51  sim_eq_tautology_del:                   541
% 7.76/1.51  sim_eq_res_simp:                        1
% 7.76/1.51  sim_fw_demodulated:                     3810
% 7.76/1.51  sim_bw_demodulated:                     28
% 7.76/1.51  sim_light_normalised:                   1467
% 7.76/1.51  sim_joinable_taut:                      608
% 7.76/1.51  sim_joinable_simp:                      0
% 7.76/1.51  sim_ac_normalised:                      0
% 7.76/1.51  sim_smt_subsumption:                    0
% 7.76/1.51  
%------------------------------------------------------------------------------
