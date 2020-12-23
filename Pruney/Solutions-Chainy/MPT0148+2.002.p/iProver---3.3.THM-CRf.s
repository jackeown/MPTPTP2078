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
% DateTime   : Thu Dec  3 11:26:42 EST 2020

% Result     : Theorem 35.56s
% Output     : CNFRefutation 35.56s
% Verified   : 
% Statistics : Number of formulae       :  103 (5706 expanded)
%              Number of clauses        :   52 ( 525 expanded)
%              Number of leaves         :   14 (1766 expanded)
%              Depth                    :   29
%              Number of atoms          :  296 (22517 expanded)
%              Number of equality atoms :   69 (5856 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f28,f33])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2 ) ),
    inference(definition_unfolding,[],[f25,f33])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
   => k2_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_enumset1(sK5,sK6,sK7,sK8,sK9)) != k6_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    k2_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_enumset1(sK5,sK6,sK7,sK8,sK9)) != k6_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f14,f23])).

fof(f41,plain,(
    k2_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_enumset1(sK5,sK6,sK7,sK8,sK9)) != k6_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f33,f42])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f36,f33,f43])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f37,f33,f44])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f38,f33,f45])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))),k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f39,f33,f46])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X7),k1_tarski(X6))),k1_tarski(X5))),k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f40,f33,f47])).

fof(f55,plain,(
    k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))) ),
    inference(definition_unfolding,[],[f41,f33,f43,f45,f48])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2 ) ),
    inference(definition_unfolding,[],[f26,f33])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2 ) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f29,f33])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f30,f33])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_83,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2257,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k5_xboole_0(X3,k4_xboole_0(X4,X3)))
    | r2_hidden(sK0(X3,X4,X1),X4)
    | r2_hidden(sK0(X3,X4,X1),X1)
    | r2_hidden(sK0(X3,X4,X1),X3)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_2,c_83])).

cnf(c_79,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7873,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k5_xboole_0(X2,k4_xboole_0(X3,X2)))
    | r2_hidden(sK0(X2,X3,X1),X3)
    | r2_hidden(sK0(X2,X3,X1),X1)
    | r2_hidden(sK0(X2,X3,X1),X2) ),
    inference(resolution,[status(thm)],[c_2257,c_79])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2285,plain,
    ( r2_hidden(sK0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3),X3)
    | r2_hidden(sK0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3),X0)
    | r2_hidden(sK0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3),X2)
    | r2_hidden(sK0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3),X1)
    | k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = X3 ),
    inference(resolution,[status(thm)],[c_2,c_5])).

cnf(c_8,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_10927,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2)) ),
    inference(resolution,[status(thm)],[c_2285,c_8])).

cnf(c_1004,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))
    | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2304,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK4))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2241,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2)) ),
    inference(resolution,[status(thm)],[c_2,c_8])).

cnf(c_3021,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2)) ),
    inference(resolution,[status(thm)],[c_2241,c_5])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3028,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3021,c_4])).

cnf(c_3332,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
    inference(resolution,[status(thm)],[c_3028,c_5])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3715,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3332,c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1103,plain,
    ( ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),X0)
    | ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),X2)
    | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(resolution,[status(thm)],[c_1,c_4])).

cnf(c_1101,plain,
    ( ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),X0)
    | ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),X3)
    | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_4000,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK4))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
    inference(resolution,[status(thm)],[c_3715,c_5])).

cnf(c_7589,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK4))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3))
    | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2))
    | k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))) ),
    inference(resolution,[status(thm)],[c_1101,c_4000])).

cnf(c_7600,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK4))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3))
    | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2))
    | k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1103,c_7589])).

cnf(c_8851,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))))
    | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_11363,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10927,c_8,c_1004,c_2304,c_3715,c_7600,c_8851])).

cnf(c_11364,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
    inference(renaming,[status(thm)],[c_11363])).

cnf(c_43460,plain,
    ( r2_hidden(sK0(X0,X1,k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4)))),X1)
    | r2_hidden(sK0(X0,X1,k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4)))),X0)
    | r2_hidden(sK0(X0,X1,k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(X0,k4_xboole_0(X1,X0)))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
    inference(resolution,[status(thm)],[c_7873,c_11364])).

cnf(c_45246,plain,
    ( r2_hidden(sK0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))))
    | r2_hidden(sK0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))))
    | r2_hidden(sK0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4)))),k1_tarski(sK5))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3))
    | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2))
    | k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))) ),
    inference(resolution,[status(thm)],[c_43460,c_1101])).

cnf(c_766,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))))
    | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2))
    | k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_11379,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK4))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
    inference(resolution,[status(thm)],[c_11364,c_5])).

cnf(c_11866,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK5))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK4))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
    inference(resolution,[status(thm)],[c_11379,c_5])).

cnf(c_16557,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))
    | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_16560,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))
    | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6970,plain,
    ( ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),X3)
    | r2_hidden(sK0(X0,X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),k5_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_25831,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))))
    | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5)))) ),
    inference(instantiation,[status(thm)],[c_6970])).

cnf(c_37957,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5)))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_37960,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))))
    | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2291,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),X0)))
    | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_45528,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))) ),
    inference(instantiation,[status(thm)],[c_2291])).

cnf(c_990,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(X0,k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))))
    | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_60407,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))))
    | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))) ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_61956,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45246,c_8,c_766,c_11866,c_16557,c_16560,c_25831,c_37957,c_37960,c_45528,c_60407])).

cnf(c_62230,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))))
    | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3)))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_61956,c_2241])).

cnf(c_63630,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_62230,c_11866,c_16557,c_16560,c_25831,c_37957,c_37960,c_45528,c_60407])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_63642,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))))
    | k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))) ),
    inference(resolution,[status(thm)],[c_63630,c_0])).

cnf(c_343,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))))
    | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))))
    | k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_64395,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_63642,c_8,c_343,c_11866,c_16557,c_16560,c_25831,c_37957,c_37960,c_45528,c_60407])).

cnf(c_65309,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4)))) ),
    inference(resolution,[status(thm)],[c_64395,c_3])).

cnf(c_7026,plain,
    ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))))
    | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_65309,c_63630,c_11364,c_7026,c_343,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.56/4.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.56/4.99  
% 35.56/4.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.56/4.99  
% 35.56/4.99  ------  iProver source info
% 35.56/4.99  
% 35.56/4.99  git: date: 2020-06-30 10:37:57 +0100
% 35.56/4.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.56/4.99  git: non_committed_changes: false
% 35.56/4.99  git: last_make_outside_of_git: false
% 35.56/4.99  
% 35.56/4.99  ------ 
% 35.56/4.99  
% 35.56/4.99  ------ Input Options
% 35.56/4.99  
% 35.56/4.99  --out_options                           all
% 35.56/4.99  --tptp_safe_out                         true
% 35.56/4.99  --problem_path                          ""
% 35.56/4.99  --include_path                          ""
% 35.56/4.99  --clausifier                            res/vclausify_rel
% 35.56/4.99  --clausifier_options                    --mode clausify
% 35.56/4.99  --stdin                                 false
% 35.56/4.99  --stats_out                             sel
% 35.56/4.99  
% 35.56/4.99  ------ General Options
% 35.56/4.99  
% 35.56/4.99  --fof                                   false
% 35.56/4.99  --time_out_real                         604.99
% 35.56/4.99  --time_out_virtual                      -1.
% 35.56/4.99  --symbol_type_check                     false
% 35.56/4.99  --clausify_out                          false
% 35.56/4.99  --sig_cnt_out                           false
% 35.56/4.99  --trig_cnt_out                          false
% 35.56/4.99  --trig_cnt_out_tolerance                1.
% 35.56/4.99  --trig_cnt_out_sk_spl                   false
% 35.56/4.99  --abstr_cl_out                          false
% 35.56/4.99  
% 35.56/4.99  ------ Global Options
% 35.56/4.99  
% 35.56/4.99  --schedule                              none
% 35.56/4.99  --add_important_lit                     false
% 35.56/4.99  --prop_solver_per_cl                    1000
% 35.56/4.99  --min_unsat_core                        false
% 35.56/4.99  --soft_assumptions                      false
% 35.56/4.99  --soft_lemma_size                       3
% 35.56/4.99  --prop_impl_unit_size                   0
% 35.56/4.99  --prop_impl_unit                        []
% 35.56/4.99  --share_sel_clauses                     true
% 35.56/4.99  --reset_solvers                         false
% 35.56/4.99  --bc_imp_inh                            [conj_cone]
% 35.56/4.99  --conj_cone_tolerance                   3.
% 35.56/4.99  --extra_neg_conj                        none
% 35.56/4.99  --large_theory_mode                     true
% 35.56/4.99  --prolific_symb_bound                   200
% 35.56/4.99  --lt_threshold                          2000
% 35.56/4.99  --clause_weak_htbl                      true
% 35.56/4.99  --gc_record_bc_elim                     false
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing Options
% 35.56/4.99  
% 35.56/4.99  --preprocessing_flag                    true
% 35.56/4.99  --time_out_prep_mult                    0.1
% 35.56/4.99  --splitting_mode                        input
% 35.56/4.99  --splitting_grd                         true
% 35.56/4.99  --splitting_cvd                         false
% 35.56/4.99  --splitting_cvd_svl                     false
% 35.56/4.99  --splitting_nvd                         32
% 35.56/4.99  --sub_typing                            true
% 35.56/4.99  --prep_gs_sim                           false
% 35.56/4.99  --prep_unflatten                        true
% 35.56/4.99  --prep_res_sim                          true
% 35.56/4.99  --prep_upred                            true
% 35.56/4.99  --prep_sem_filter                       exhaustive
% 35.56/4.99  --prep_sem_filter_out                   false
% 35.56/4.99  --pred_elim                             false
% 35.56/4.99  --res_sim_input                         true
% 35.56/4.99  --eq_ax_congr_red                       true
% 35.56/4.99  --pure_diseq_elim                       true
% 35.56/4.99  --brand_transform                       false
% 35.56/4.99  --non_eq_to_eq                          false
% 35.56/4.99  --prep_def_merge                        true
% 35.56/4.99  --prep_def_merge_prop_impl              false
% 35.56/4.99  --prep_def_merge_mbd                    true
% 35.56/4.99  --prep_def_merge_tr_red                 false
% 35.56/4.99  --prep_def_merge_tr_cl                  false
% 35.56/4.99  --smt_preprocessing                     true
% 35.56/4.99  --smt_ac_axioms                         fast
% 35.56/4.99  --preprocessed_out                      false
% 35.56/4.99  --preprocessed_stats                    false
% 35.56/4.99  
% 35.56/4.99  ------ Abstraction refinement Options
% 35.56/4.99  
% 35.56/4.99  --abstr_ref                             []
% 35.56/4.99  --abstr_ref_prep                        false
% 35.56/4.99  --abstr_ref_until_sat                   false
% 35.56/4.99  --abstr_ref_sig_restrict                funpre
% 35.56/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.56/4.99  --abstr_ref_under                       []
% 35.56/4.99  
% 35.56/4.99  ------ SAT Options
% 35.56/4.99  
% 35.56/4.99  --sat_mode                              false
% 35.56/4.99  --sat_fm_restart_options                ""
% 35.56/4.99  --sat_gr_def                            false
% 35.56/4.99  --sat_epr_types                         true
% 35.56/4.99  --sat_non_cyclic_types                  false
% 35.56/4.99  --sat_finite_models                     false
% 35.56/4.99  --sat_fm_lemmas                         false
% 35.56/4.99  --sat_fm_prep                           false
% 35.56/4.99  --sat_fm_uc_incr                        true
% 35.56/4.99  --sat_out_model                         small
% 35.56/4.99  --sat_out_clauses                       false
% 35.56/4.99  
% 35.56/4.99  ------ QBF Options
% 35.56/4.99  
% 35.56/4.99  --qbf_mode                              false
% 35.56/4.99  --qbf_elim_univ                         false
% 35.56/4.99  --qbf_dom_inst                          none
% 35.56/4.99  --qbf_dom_pre_inst                      false
% 35.56/4.99  --qbf_sk_in                             false
% 35.56/4.99  --qbf_pred_elim                         true
% 35.56/4.99  --qbf_split                             512
% 35.56/4.99  
% 35.56/4.99  ------ BMC1 Options
% 35.56/4.99  
% 35.56/4.99  --bmc1_incremental                      false
% 35.56/4.99  --bmc1_axioms                           reachable_all
% 35.56/4.99  --bmc1_min_bound                        0
% 35.56/4.99  --bmc1_max_bound                        -1
% 35.56/4.99  --bmc1_max_bound_default                -1
% 35.56/4.99  --bmc1_symbol_reachability              true
% 35.56/4.99  --bmc1_property_lemmas                  false
% 35.56/4.99  --bmc1_k_induction                      false
% 35.56/4.99  --bmc1_non_equiv_states                 false
% 35.56/4.99  --bmc1_deadlock                         false
% 35.56/4.99  --bmc1_ucm                              false
% 35.56/4.99  --bmc1_add_unsat_core                   none
% 35.56/4.99  --bmc1_unsat_core_children              false
% 35.56/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.56/4.99  --bmc1_out_stat                         full
% 35.56/4.99  --bmc1_ground_init                      false
% 35.56/4.99  --bmc1_pre_inst_next_state              false
% 35.56/4.99  --bmc1_pre_inst_state                   false
% 35.56/4.99  --bmc1_pre_inst_reach_state             false
% 35.56/4.99  --bmc1_out_unsat_core                   false
% 35.56/4.99  --bmc1_aig_witness_out                  false
% 35.56/4.99  --bmc1_verbose                          false
% 35.56/4.99  --bmc1_dump_clauses_tptp                false
% 35.56/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.56/4.99  --bmc1_dump_file                        -
% 35.56/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.56/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.56/4.99  --bmc1_ucm_extend_mode                  1
% 35.56/4.99  --bmc1_ucm_init_mode                    2
% 35.56/4.99  --bmc1_ucm_cone_mode                    none
% 35.56/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.56/4.99  --bmc1_ucm_relax_model                  4
% 35.56/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.56/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.56/4.99  --bmc1_ucm_layered_model                none
% 35.56/4.99  --bmc1_ucm_max_lemma_size               10
% 35.56/4.99  
% 35.56/4.99  ------ AIG Options
% 35.56/4.99  
% 35.56/4.99  --aig_mode                              false
% 35.56/4.99  
% 35.56/4.99  ------ Instantiation Options
% 35.56/4.99  
% 35.56/4.99  --instantiation_flag                    true
% 35.56/4.99  --inst_sos_flag                         false
% 35.56/4.99  --inst_sos_phase                        true
% 35.56/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.56/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.56/4.99  --inst_lit_sel_side                     num_symb
% 35.56/4.99  --inst_solver_per_active                1400
% 35.56/4.99  --inst_solver_calls_frac                1.
% 35.56/4.99  --inst_passive_queue_type               priority_queues
% 35.56/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.56/4.99  --inst_passive_queues_freq              [25;2]
% 35.56/4.99  --inst_dismatching                      true
% 35.56/4.99  --inst_eager_unprocessed_to_passive     true
% 35.56/4.99  --inst_prop_sim_given                   true
% 35.56/4.99  --inst_prop_sim_new                     false
% 35.56/4.99  --inst_subs_new                         false
% 35.56/4.99  --inst_eq_res_simp                      false
% 35.56/4.99  --inst_subs_given                       false
% 35.56/4.99  --inst_orphan_elimination               true
% 35.56/4.99  --inst_learning_loop_flag               true
% 35.56/4.99  --inst_learning_start                   3000
% 35.56/4.99  --inst_learning_factor                  2
% 35.56/4.99  --inst_start_prop_sim_after_learn       3
% 35.56/4.99  --inst_sel_renew                        solver
% 35.56/4.99  --inst_lit_activity_flag                true
% 35.56/4.99  --inst_restr_to_given                   false
% 35.56/4.99  --inst_activity_threshold               500
% 35.56/4.99  --inst_out_proof                        true
% 35.56/4.99  
% 35.56/4.99  ------ Resolution Options
% 35.56/4.99  
% 35.56/4.99  --resolution_flag                       true
% 35.56/4.99  --res_lit_sel                           adaptive
% 35.56/4.99  --res_lit_sel_side                      none
% 35.56/4.99  --res_ordering                          kbo
% 35.56/4.99  --res_to_prop_solver                    active
% 35.56/4.99  --res_prop_simpl_new                    false
% 35.56/4.99  --res_prop_simpl_given                  true
% 35.56/4.99  --res_passive_queue_type                priority_queues
% 35.56/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.56/4.99  --res_passive_queues_freq               [15;5]
% 35.56/4.99  --res_forward_subs                      full
% 35.56/4.99  --res_backward_subs                     full
% 35.56/4.99  --res_forward_subs_resolution           true
% 35.56/4.99  --res_backward_subs_resolution          true
% 35.56/4.99  --res_orphan_elimination                true
% 35.56/4.99  --res_time_limit                        2.
% 35.56/4.99  --res_out_proof                         true
% 35.56/4.99  
% 35.56/4.99  ------ Superposition Options
% 35.56/4.99  
% 35.56/4.99  --superposition_flag                    true
% 35.56/4.99  --sup_passive_queue_type                priority_queues
% 35.56/4.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.56/4.99  --sup_passive_queues_freq               [1;4]
% 35.56/4.99  --demod_completeness_check              fast
% 35.56/4.99  --demod_use_ground                      true
% 35.56/4.99  --sup_to_prop_solver                    passive
% 35.56/4.99  --sup_prop_simpl_new                    true
% 35.56/4.99  --sup_prop_simpl_given                  true
% 35.56/4.99  --sup_fun_splitting                     false
% 35.56/4.99  --sup_smt_interval                      50000
% 35.56/4.99  
% 35.56/4.99  ------ Superposition Simplification Setup
% 35.56/4.99  
% 35.56/4.99  --sup_indices_passive                   []
% 35.56/4.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.56/4.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.56/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.56/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.56/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.56/4.99  --sup_full_bw                           [BwDemod]
% 35.56/4.99  --sup_immed_triv                        [TrivRules]
% 35.56/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.56/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.56/4.99  --sup_immed_bw_main                     []
% 35.56/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.56/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.56/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.56/4.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.56/4.99  
% 35.56/4.99  ------ Combination Options
% 35.56/4.99  
% 35.56/4.99  --comb_res_mult                         3
% 35.56/4.99  --comb_sup_mult                         2
% 35.56/4.99  --comb_inst_mult                        10
% 35.56/4.99  
% 35.56/4.99  ------ Debug Options
% 35.56/4.99  
% 35.56/4.99  --dbg_backtrace                         false
% 35.56/4.99  --dbg_dump_prop_clauses                 false
% 35.56/4.99  --dbg_dump_prop_clauses_file            -
% 35.56/4.99  --dbg_out_stat                          false
% 35.56/4.99  ------ Parsing...
% 35.56/4.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.56/4.99  ------ Proving...
% 35.56/4.99  ------ Problem Properties 
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  clauses                                 9
% 35.56/4.99  conjectures                             1
% 35.56/4.99  EPR                                     0
% 35.56/4.99  Horn                                    6
% 35.56/4.99  unary                                   1
% 35.56/4.99  binary                                  2
% 35.56/4.99  lits                                    24
% 35.56/4.99  lits eq                                 6
% 35.56/4.99  fd_pure                                 0
% 35.56/4.99  fd_pseudo                               0
% 35.56/4.99  fd_cond                                 0
% 35.56/4.99  fd_pseudo_cond                          5
% 35.56/4.99  AC symbols                              0
% 35.56/4.99  
% 35.56/4.99  ------ Input Options Time Limit: Unbounded
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  ------ 
% 35.56/4.99  Current options:
% 35.56/4.99  ------ 
% 35.56/4.99  
% 35.56/4.99  ------ Input Options
% 35.56/4.99  
% 35.56/4.99  --out_options                           all
% 35.56/4.99  --tptp_safe_out                         true
% 35.56/4.99  --problem_path                          ""
% 35.56/4.99  --include_path                          ""
% 35.56/4.99  --clausifier                            res/vclausify_rel
% 35.56/4.99  --clausifier_options                    --mode clausify
% 35.56/4.99  --stdin                                 false
% 35.56/4.99  --stats_out                             sel
% 35.56/4.99  
% 35.56/4.99  ------ General Options
% 35.56/4.99  
% 35.56/4.99  --fof                                   false
% 35.56/4.99  --time_out_real                         604.99
% 35.56/4.99  --time_out_virtual                      -1.
% 35.56/4.99  --symbol_type_check                     false
% 35.56/4.99  --clausify_out                          false
% 35.56/4.99  --sig_cnt_out                           false
% 35.56/4.99  --trig_cnt_out                          false
% 35.56/4.99  --trig_cnt_out_tolerance                1.
% 35.56/4.99  --trig_cnt_out_sk_spl                   false
% 35.56/4.99  --abstr_cl_out                          false
% 35.56/4.99  
% 35.56/4.99  ------ Global Options
% 35.56/4.99  
% 35.56/4.99  --schedule                              none
% 35.56/4.99  --add_important_lit                     false
% 35.56/4.99  --prop_solver_per_cl                    1000
% 35.56/4.99  --min_unsat_core                        false
% 35.56/4.99  --soft_assumptions                      false
% 35.56/4.99  --soft_lemma_size                       3
% 35.56/4.99  --prop_impl_unit_size                   0
% 35.56/4.99  --prop_impl_unit                        []
% 35.56/4.99  --share_sel_clauses                     true
% 35.56/4.99  --reset_solvers                         false
% 35.56/4.99  --bc_imp_inh                            [conj_cone]
% 35.56/4.99  --conj_cone_tolerance                   3.
% 35.56/4.99  --extra_neg_conj                        none
% 35.56/4.99  --large_theory_mode                     true
% 35.56/4.99  --prolific_symb_bound                   200
% 35.56/4.99  --lt_threshold                          2000
% 35.56/4.99  --clause_weak_htbl                      true
% 35.56/4.99  --gc_record_bc_elim                     false
% 35.56/4.99  
% 35.56/4.99  ------ Preprocessing Options
% 35.56/4.99  
% 35.56/4.99  --preprocessing_flag                    true
% 35.56/4.99  --time_out_prep_mult                    0.1
% 35.56/4.99  --splitting_mode                        input
% 35.56/4.99  --splitting_grd                         true
% 35.56/4.99  --splitting_cvd                         false
% 35.56/4.99  --splitting_cvd_svl                     false
% 35.56/4.99  --splitting_nvd                         32
% 35.56/4.99  --sub_typing                            true
% 35.56/4.99  --prep_gs_sim                           false
% 35.56/4.99  --prep_unflatten                        true
% 35.56/4.99  --prep_res_sim                          true
% 35.56/4.99  --prep_upred                            true
% 35.56/4.99  --prep_sem_filter                       exhaustive
% 35.56/4.99  --prep_sem_filter_out                   false
% 35.56/4.99  --pred_elim                             false
% 35.56/4.99  --res_sim_input                         true
% 35.56/4.99  --eq_ax_congr_red                       true
% 35.56/4.99  --pure_diseq_elim                       true
% 35.56/4.99  --brand_transform                       false
% 35.56/4.99  --non_eq_to_eq                          false
% 35.56/4.99  --prep_def_merge                        true
% 35.56/4.99  --prep_def_merge_prop_impl              false
% 35.56/4.99  --prep_def_merge_mbd                    true
% 35.56/4.99  --prep_def_merge_tr_red                 false
% 35.56/4.99  --prep_def_merge_tr_cl                  false
% 35.56/4.99  --smt_preprocessing                     true
% 35.56/4.99  --smt_ac_axioms                         fast
% 35.56/4.99  --preprocessed_out                      false
% 35.56/4.99  --preprocessed_stats                    false
% 35.56/4.99  
% 35.56/4.99  ------ Abstraction refinement Options
% 35.56/4.99  
% 35.56/4.99  --abstr_ref                             []
% 35.56/4.99  --abstr_ref_prep                        false
% 35.56/4.99  --abstr_ref_until_sat                   false
% 35.56/4.99  --abstr_ref_sig_restrict                funpre
% 35.56/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.56/4.99  --abstr_ref_under                       []
% 35.56/4.99  
% 35.56/4.99  ------ SAT Options
% 35.56/4.99  
% 35.56/4.99  --sat_mode                              false
% 35.56/4.99  --sat_fm_restart_options                ""
% 35.56/4.99  --sat_gr_def                            false
% 35.56/4.99  --sat_epr_types                         true
% 35.56/4.99  --sat_non_cyclic_types                  false
% 35.56/4.99  --sat_finite_models                     false
% 35.56/4.99  --sat_fm_lemmas                         false
% 35.56/4.99  --sat_fm_prep                           false
% 35.56/4.99  --sat_fm_uc_incr                        true
% 35.56/4.99  --sat_out_model                         small
% 35.56/4.99  --sat_out_clauses                       false
% 35.56/4.99  
% 35.56/4.99  ------ QBF Options
% 35.56/4.99  
% 35.56/4.99  --qbf_mode                              false
% 35.56/4.99  --qbf_elim_univ                         false
% 35.56/4.99  --qbf_dom_inst                          none
% 35.56/4.99  --qbf_dom_pre_inst                      false
% 35.56/4.99  --qbf_sk_in                             false
% 35.56/4.99  --qbf_pred_elim                         true
% 35.56/4.99  --qbf_split                             512
% 35.56/4.99  
% 35.56/4.99  ------ BMC1 Options
% 35.56/4.99  
% 35.56/4.99  --bmc1_incremental                      false
% 35.56/4.99  --bmc1_axioms                           reachable_all
% 35.56/4.99  --bmc1_min_bound                        0
% 35.56/4.99  --bmc1_max_bound                        -1
% 35.56/4.99  --bmc1_max_bound_default                -1
% 35.56/4.99  --bmc1_symbol_reachability              true
% 35.56/4.99  --bmc1_property_lemmas                  false
% 35.56/4.99  --bmc1_k_induction                      false
% 35.56/4.99  --bmc1_non_equiv_states                 false
% 35.56/4.99  --bmc1_deadlock                         false
% 35.56/4.99  --bmc1_ucm                              false
% 35.56/4.99  --bmc1_add_unsat_core                   none
% 35.56/4.99  --bmc1_unsat_core_children              false
% 35.56/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.56/4.99  --bmc1_out_stat                         full
% 35.56/4.99  --bmc1_ground_init                      false
% 35.56/4.99  --bmc1_pre_inst_next_state              false
% 35.56/4.99  --bmc1_pre_inst_state                   false
% 35.56/4.99  --bmc1_pre_inst_reach_state             false
% 35.56/4.99  --bmc1_out_unsat_core                   false
% 35.56/4.99  --bmc1_aig_witness_out                  false
% 35.56/4.99  --bmc1_verbose                          false
% 35.56/4.99  --bmc1_dump_clauses_tptp                false
% 35.56/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.56/4.99  --bmc1_dump_file                        -
% 35.56/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.56/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.56/4.99  --bmc1_ucm_extend_mode                  1
% 35.56/4.99  --bmc1_ucm_init_mode                    2
% 35.56/4.99  --bmc1_ucm_cone_mode                    none
% 35.56/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.56/4.99  --bmc1_ucm_relax_model                  4
% 35.56/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.56/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.56/4.99  --bmc1_ucm_layered_model                none
% 35.56/4.99  --bmc1_ucm_max_lemma_size               10
% 35.56/4.99  
% 35.56/4.99  ------ AIG Options
% 35.56/4.99  
% 35.56/4.99  --aig_mode                              false
% 35.56/4.99  
% 35.56/4.99  ------ Instantiation Options
% 35.56/4.99  
% 35.56/4.99  --instantiation_flag                    true
% 35.56/4.99  --inst_sos_flag                         false
% 35.56/4.99  --inst_sos_phase                        true
% 35.56/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.56/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.56/4.99  --inst_lit_sel_side                     num_symb
% 35.56/4.99  --inst_solver_per_active                1400
% 35.56/4.99  --inst_solver_calls_frac                1.
% 35.56/4.99  --inst_passive_queue_type               priority_queues
% 35.56/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.56/4.99  --inst_passive_queues_freq              [25;2]
% 35.56/4.99  --inst_dismatching                      true
% 35.56/4.99  --inst_eager_unprocessed_to_passive     true
% 35.56/4.99  --inst_prop_sim_given                   true
% 35.56/4.99  --inst_prop_sim_new                     false
% 35.56/4.99  --inst_subs_new                         false
% 35.56/4.99  --inst_eq_res_simp                      false
% 35.56/4.99  --inst_subs_given                       false
% 35.56/4.99  --inst_orphan_elimination               true
% 35.56/4.99  --inst_learning_loop_flag               true
% 35.56/4.99  --inst_learning_start                   3000
% 35.56/4.99  --inst_learning_factor                  2
% 35.56/4.99  --inst_start_prop_sim_after_learn       3
% 35.56/4.99  --inst_sel_renew                        solver
% 35.56/4.99  --inst_lit_activity_flag                true
% 35.56/4.99  --inst_restr_to_given                   false
% 35.56/4.99  --inst_activity_threshold               500
% 35.56/4.99  --inst_out_proof                        true
% 35.56/4.99  
% 35.56/4.99  ------ Resolution Options
% 35.56/4.99  
% 35.56/4.99  --resolution_flag                       true
% 35.56/4.99  --res_lit_sel                           adaptive
% 35.56/4.99  --res_lit_sel_side                      none
% 35.56/4.99  --res_ordering                          kbo
% 35.56/4.99  --res_to_prop_solver                    active
% 35.56/4.99  --res_prop_simpl_new                    false
% 35.56/4.99  --res_prop_simpl_given                  true
% 35.56/4.99  --res_passive_queue_type                priority_queues
% 35.56/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.56/4.99  --res_passive_queues_freq               [15;5]
% 35.56/4.99  --res_forward_subs                      full
% 35.56/4.99  --res_backward_subs                     full
% 35.56/4.99  --res_forward_subs_resolution           true
% 35.56/4.99  --res_backward_subs_resolution          true
% 35.56/4.99  --res_orphan_elimination                true
% 35.56/4.99  --res_time_limit                        2.
% 35.56/4.99  --res_out_proof                         true
% 35.56/4.99  
% 35.56/4.99  ------ Superposition Options
% 35.56/4.99  
% 35.56/4.99  --superposition_flag                    true
% 35.56/4.99  --sup_passive_queue_type                priority_queues
% 35.56/4.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.56/4.99  --sup_passive_queues_freq               [1;4]
% 35.56/4.99  --demod_completeness_check              fast
% 35.56/4.99  --demod_use_ground                      true
% 35.56/4.99  --sup_to_prop_solver                    passive
% 35.56/4.99  --sup_prop_simpl_new                    true
% 35.56/4.99  --sup_prop_simpl_given                  true
% 35.56/4.99  --sup_fun_splitting                     false
% 35.56/4.99  --sup_smt_interval                      50000
% 35.56/4.99  
% 35.56/4.99  ------ Superposition Simplification Setup
% 35.56/4.99  
% 35.56/4.99  --sup_indices_passive                   []
% 35.56/4.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.56/4.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.56/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.56/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.56/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.56/4.99  --sup_full_bw                           [BwDemod]
% 35.56/4.99  --sup_immed_triv                        [TrivRules]
% 35.56/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.56/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.56/4.99  --sup_immed_bw_main                     []
% 35.56/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.56/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.56/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.56/4.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.56/4.99  
% 35.56/4.99  ------ Combination Options
% 35.56/4.99  
% 35.56/4.99  --comb_res_mult                         3
% 35.56/4.99  --comb_sup_mult                         2
% 35.56/4.99  --comb_inst_mult                        10
% 35.56/4.99  
% 35.56/4.99  ------ Debug Options
% 35.56/4.99  
% 35.56/4.99  --dbg_backtrace                         false
% 35.56/4.99  --dbg_dump_prop_clauses                 false
% 35.56/4.99  --dbg_dump_prop_clauses_file            -
% 35.56/4.99  --dbg_out_stat                          false
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  ------ Proving...
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  % SZS status Theorem for theBenchmark.p
% 35.56/4.99  
% 35.56/4.99  % SZS output start CNFRefutation for theBenchmark.p
% 35.56/4.99  
% 35.56/4.99  fof(f1,axiom,(
% 35.56/4.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 35.56/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.56/4.99  
% 35.56/4.99  fof(f15,plain,(
% 35.56/4.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 35.56/4.99    inference(nnf_transformation,[],[f1])).
% 35.56/4.99  
% 35.56/4.99  fof(f16,plain,(
% 35.56/4.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 35.56/4.99    inference(flattening,[],[f15])).
% 35.56/4.99  
% 35.56/4.99  fof(f17,plain,(
% 35.56/4.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 35.56/4.99    inference(rectify,[],[f16])).
% 35.56/4.99  
% 35.56/4.99  fof(f18,plain,(
% 35.56/4.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 35.56/4.99    introduced(choice_axiom,[])).
% 35.56/4.99  
% 35.56/4.99  fof(f19,plain,(
% 35.56/4.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 35.56/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 35.56/4.99  
% 35.56/4.99  fof(f28,plain,(
% 35.56/4.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 35.56/4.99    inference(cnf_transformation,[],[f19])).
% 35.56/4.99  
% 35.56/4.99  fof(f3,axiom,(
% 35.56/4.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 35.56/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.56/4.99  
% 35.56/4.99  fof(f33,plain,(
% 35.56/4.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 35.56/4.99    inference(cnf_transformation,[],[f3])).
% 35.56/4.99  
% 35.56/4.99  fof(f51,plain,(
% 35.56/4.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 35.56/4.99    inference(definition_unfolding,[],[f28,f33])).
% 35.56/4.99  
% 35.56/4.99  fof(f25,plain,(
% 35.56/4.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 35.56/4.99    inference(cnf_transformation,[],[f19])).
% 35.56/4.99  
% 35.56/4.99  fof(f54,plain,(
% 35.56/4.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2) )),
% 35.56/4.99    inference(definition_unfolding,[],[f25,f33])).
% 35.56/4.99  
% 35.56/4.99  fof(f58,plain,(
% 35.56/4.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 35.56/4.99    inference(equality_resolution,[],[f54])).
% 35.56/4.99  
% 35.56/4.99  fof(f11,conjecture,(
% 35.56/4.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 35.56/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.56/4.99  
% 35.56/4.99  fof(f12,negated_conjecture,(
% 35.56/4.99    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 35.56/4.99    inference(negated_conjecture,[],[f11])).
% 35.56/4.99  
% 35.56/4.99  fof(f14,plain,(
% 35.56/4.99    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 35.56/4.99    inference(ennf_transformation,[],[f12])).
% 35.56/4.99  
% 35.56/4.99  fof(f23,plain,(
% 35.56/4.99    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) => k2_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_enumset1(sK5,sK6,sK7,sK8,sK9)) != k6_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),
% 35.56/4.99    introduced(choice_axiom,[])).
% 35.56/4.99  
% 35.56/4.99  fof(f24,plain,(
% 35.56/4.99    k2_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_enumset1(sK5,sK6,sK7,sK8,sK9)) != k6_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),
% 35.56/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f14,f23])).
% 35.56/4.99  
% 35.56/4.99  fof(f41,plain,(
% 35.56/4.99    k2_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_enumset1(sK5,sK6,sK7,sK8,sK9)) != k6_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9)),
% 35.56/4.99    inference(cnf_transformation,[],[f24])).
% 35.56/4.99  
% 35.56/4.99  fof(f10,axiom,(
% 35.56/4.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 35.56/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.56/4.99  
% 35.56/4.99  fof(f40,plain,(
% 35.56/4.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 35.56/4.99    inference(cnf_transformation,[],[f10])).
% 35.56/4.99  
% 35.56/4.99  fof(f9,axiom,(
% 35.56/4.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 35.56/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.56/4.99  
% 35.56/4.99  fof(f39,plain,(
% 35.56/4.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 35.56/4.99    inference(cnf_transformation,[],[f9])).
% 35.56/4.99  
% 35.56/4.99  fof(f8,axiom,(
% 35.56/4.99    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 35.56/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.56/4.99  
% 35.56/4.99  fof(f38,plain,(
% 35.56/4.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 35.56/4.99    inference(cnf_transformation,[],[f8])).
% 35.56/4.99  
% 35.56/4.99  fof(f7,axiom,(
% 35.56/4.99    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 35.56/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.56/4.99  
% 35.56/4.99  fof(f37,plain,(
% 35.56/4.99    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 35.56/4.99    inference(cnf_transformation,[],[f7])).
% 35.56/4.99  
% 35.56/4.99  fof(f6,axiom,(
% 35.56/4.99    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 35.56/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.56/4.99  
% 35.56/4.99  fof(f36,plain,(
% 35.56/4.99    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 35.56/4.99    inference(cnf_transformation,[],[f6])).
% 35.56/4.99  
% 35.56/4.99  fof(f5,axiom,(
% 35.56/4.99    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 35.56/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.56/4.99  
% 35.56/4.99  fof(f35,plain,(
% 35.56/4.99    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 35.56/4.99    inference(cnf_transformation,[],[f5])).
% 35.56/4.99  
% 35.56/4.99  fof(f4,axiom,(
% 35.56/4.99    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 35.56/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.56/4.99  
% 35.56/4.99  fof(f34,plain,(
% 35.56/4.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 35.56/4.99    inference(cnf_transformation,[],[f4])).
% 35.56/4.99  
% 35.56/4.99  fof(f42,plain,(
% 35.56/4.99    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1)) )),
% 35.56/4.99    inference(definition_unfolding,[],[f34,f33])).
% 35.56/4.99  
% 35.56/4.99  fof(f43,plain,(
% 35.56/4.99    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) = k1_enumset1(X0,X1,X2)) )),
% 35.56/4.99    inference(definition_unfolding,[],[f35,f33,f42])).
% 35.56/4.99  
% 35.56/4.99  fof(f44,plain,(
% 35.56/4.99    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) = k2_enumset1(X0,X1,X2,X3)) )),
% 35.56/4.99    inference(definition_unfolding,[],[f36,f33,f43])).
% 35.56/4.99  
% 35.56/4.99  fof(f45,plain,(
% 35.56/4.99    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 35.56/4.99    inference(definition_unfolding,[],[f37,f33,f44])).
% 35.56/4.99  
% 35.56/4.99  fof(f46,plain,(
% 35.56/4.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 35.56/4.99    inference(definition_unfolding,[],[f38,f33,f45])).
% 35.56/4.99  
% 35.56/4.99  fof(f47,plain,(
% 35.56/4.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))),k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 35.56/4.99    inference(definition_unfolding,[],[f39,f33,f46])).
% 35.56/4.99  
% 35.56/4.99  fof(f48,plain,(
% 35.56/4.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X7),k1_tarski(X6))),k1_tarski(X5))),k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 35.56/4.99    inference(definition_unfolding,[],[f40,f33,f47])).
% 35.56/4.99  
% 35.56/4.99  fof(f55,plain,(
% 35.56/4.99    k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),
% 35.56/4.99    inference(definition_unfolding,[],[f41,f33,f43,f45,f48])).
% 35.56/4.99  
% 35.56/4.99  fof(f26,plain,(
% 35.56/4.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 35.56/4.99    inference(cnf_transformation,[],[f19])).
% 35.56/4.99  
% 35.56/4.99  fof(f53,plain,(
% 35.56/4.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2) )),
% 35.56/4.99    inference(definition_unfolding,[],[f26,f33])).
% 35.56/4.99  
% 35.56/4.99  fof(f57,plain,(
% 35.56/4.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0))) | ~r2_hidden(X4,X0)) )),
% 35.56/4.99    inference(equality_resolution,[],[f53])).
% 35.56/4.99  
% 35.56/4.99  fof(f27,plain,(
% 35.56/4.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 35.56/4.99    inference(cnf_transformation,[],[f19])).
% 35.56/4.99  
% 35.56/4.99  fof(f52,plain,(
% 35.56/4.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2) )),
% 35.56/4.99    inference(definition_unfolding,[],[f27,f33])).
% 35.56/4.99  
% 35.56/4.99  fof(f56,plain,(
% 35.56/4.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0))) | ~r2_hidden(X4,X1)) )),
% 35.56/4.99    inference(equality_resolution,[],[f52])).
% 35.56/4.99  
% 35.56/4.99  fof(f29,plain,(
% 35.56/4.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 35.56/4.99    inference(cnf_transformation,[],[f19])).
% 35.56/4.99  
% 35.56/4.99  fof(f50,plain,(
% 35.56/4.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 35.56/4.99    inference(definition_unfolding,[],[f29,f33])).
% 35.56/4.99  
% 35.56/4.99  fof(f30,plain,(
% 35.56/4.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 35.56/4.99    inference(cnf_transformation,[],[f19])).
% 35.56/4.99  
% 35.56/4.99  fof(f49,plain,(
% 35.56/4.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 35.56/4.99    inference(definition_unfolding,[],[f30,f33])).
% 35.56/4.99  
% 35.56/4.99  cnf(c_2,plain,
% 35.56/4.99      ( r2_hidden(sK0(X0,X1,X2),X1)
% 35.56/4.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 35.56/4.99      | r2_hidden(sK0(X0,X1,X2),X0)
% 35.56/4.99      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 ),
% 35.56/4.99      inference(cnf_transformation,[],[f51]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_83,plain,
% 35.56/4.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.56/4.99      theory(equality) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_2257,plain,
% 35.56/4.99      ( ~ r2_hidden(X0,X1)
% 35.56/4.99      | r2_hidden(X2,k5_xboole_0(X3,k4_xboole_0(X4,X3)))
% 35.56/4.99      | r2_hidden(sK0(X3,X4,X1),X4)
% 35.56/4.99      | r2_hidden(sK0(X3,X4,X1),X1)
% 35.56/4.99      | r2_hidden(sK0(X3,X4,X1),X3)
% 35.56/4.99      | X2 != X0 ),
% 35.56/4.99      inference(resolution,[status(thm)],[c_2,c_83]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_79,plain,( X0 = X0 ),theory(equality) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_7873,plain,
% 35.56/4.99      ( ~ r2_hidden(X0,X1)
% 35.56/4.99      | r2_hidden(X0,k5_xboole_0(X2,k4_xboole_0(X3,X2)))
% 35.56/4.99      | r2_hidden(sK0(X2,X3,X1),X3)
% 35.56/4.99      | r2_hidden(sK0(X2,X3,X1),X1)
% 35.56/4.99      | r2_hidden(sK0(X2,X3,X1),X2) ),
% 35.56/4.99      inference(resolution,[status(thm)],[c_2257,c_79]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_5,plain,
% 35.56/4.99      ( r2_hidden(X0,X1)
% 35.56/4.99      | r2_hidden(X0,X2)
% 35.56/4.99      | ~ r2_hidden(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
% 35.56/4.99      inference(cnf_transformation,[],[f58]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_2285,plain,
% 35.56/4.99      ( r2_hidden(sK0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3),X3)
% 35.56/4.99      | r2_hidden(sK0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3),X0)
% 35.56/4.99      | r2_hidden(sK0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3),X2)
% 35.56/4.99      | r2_hidden(sK0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3),X1)
% 35.56/4.99      | k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = X3 ),
% 35.56/4.99      inference(resolution,[status(thm)],[c_2,c_5]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_8,negated_conjecture,
% 35.56/4.99      ( k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))) ),
% 35.56/4.99      inference(cnf_transformation,[],[f55]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_10927,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2)) ),
% 35.56/4.99      inference(resolution,[status(thm)],[c_2285,c_8]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_1004,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))
% 35.56/4.99      | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2)) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_5]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_2304,plain,
% 35.56/4.99      ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK4))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_5]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_2241,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2)) ),
% 35.56/4.99      inference(resolution,[status(thm)],[c_2,c_8]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_3021,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2)) ),
% 35.56/4.99      inference(resolution,[status(thm)],[c_2241,c_5]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_4,plain,
% 35.56/4.99      ( ~ r2_hidden(X0,X1)
% 35.56/4.99      | r2_hidden(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
% 35.56/4.99      inference(cnf_transformation,[],[f57]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_3028,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))) ),
% 35.56/4.99      inference(forward_subsumption_resolution,
% 35.56/4.99                [status(thm)],
% 35.56/4.99                [c_3021,c_4]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_3332,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
% 35.56/4.99      inference(resolution,[status(thm)],[c_3028,c_5]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_3,plain,
% 35.56/4.99      ( ~ r2_hidden(X0,X1)
% 35.56/4.99      | r2_hidden(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
% 35.56/4.99      inference(cnf_transformation,[],[f56]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_3715,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
% 35.56/4.99      inference(forward_subsumption_resolution,
% 35.56/4.99                [status(thm)],
% 35.56/4.99                [c_3332,c_3]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_1,plain,
% 35.56/4.99      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 35.56/4.99      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 35.56/4.99      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 ),
% 35.56/4.99      inference(cnf_transformation,[],[f50]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_1103,plain,
% 35.56/4.99      ( ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),X0)
% 35.56/4.99      | ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),X2)
% 35.56/4.99      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X2,k4_xboole_0(X3,X2)) ),
% 35.56/4.99      inference(resolution,[status(thm)],[c_1,c_4]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_1101,plain,
% 35.56/4.99      ( ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),X0)
% 35.56/4.99      | ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),X3)
% 35.56/4.99      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X2,k4_xboole_0(X3,X2)) ),
% 35.56/4.99      inference(resolution,[status(thm)],[c_1,c_3]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_4000,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK4))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
% 35.56/4.99      inference(resolution,[status(thm)],[c_3715,c_5]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_7589,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK4))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3))
% 35.56/4.99      | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2))
% 35.56/4.99      | k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))) ),
% 35.56/4.99      inference(resolution,[status(thm)],[c_1101,c_4000]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_7600,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK4))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3))
% 35.56/4.99      | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2))
% 35.56/4.99      | k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))) ),
% 35.56/4.99      inference(backward_subsumption_resolution,
% 35.56/4.99                [status(thm)],
% 35.56/4.99                [c_1103,c_7589]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_8851,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))))
% 35.56/4.99      | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK4)) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_4]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_11363,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4)))) ),
% 35.56/4.99      inference(global_propositional_subsumption,
% 35.56/4.99                [status(thm)],
% 35.56/4.99                [c_10927,c_8,c_1004,c_2304,c_3715,c_7600,c_8851]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_11364,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
% 35.56/4.99      inference(renaming,[status(thm)],[c_11363]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_43460,plain,
% 35.56/4.99      ( r2_hidden(sK0(X0,X1,k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4)))),X1)
% 35.56/4.99      | r2_hidden(sK0(X0,X1,k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4)))),X0)
% 35.56/4.99      | r2_hidden(sK0(X0,X1,k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(X0,k4_xboole_0(X1,X0)))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
% 35.56/4.99      inference(resolution,[status(thm)],[c_7873,c_11364]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_45246,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4)))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4)))),k1_tarski(sK5))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3))
% 35.56/4.99      | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2))
% 35.56/4.99      | k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))) ),
% 35.56/4.99      inference(resolution,[status(thm)],[c_43460,c_1101]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_766,plain,
% 35.56/4.99      ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))))
% 35.56/4.99      | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2))
% 35.56/4.99      | k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_1]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_11379,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK4))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
% 35.56/4.99      inference(resolution,[status(thm)],[c_11364,c_5]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_11866,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK5))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK4))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
% 35.56/4.99      inference(resolution,[status(thm)],[c_11379,c_5]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_16557,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))
% 35.56/4.99      | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK4)) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_3]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_16560,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))
% 35.56/4.99      | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_4]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_6970,plain,
% 35.56/4.99      ( ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),X3)
% 35.56/4.99      | r2_hidden(sK0(X0,X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),k5_xboole_0(X2,k4_xboole_0(X3,X2))) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_3]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_25831,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))))
% 35.56/4.99      | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5)))) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_6970]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_37957,plain,
% 35.56/4.99      ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5)))) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_3]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_37960,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))))
% 35.56/4.99      | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK5)) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_4]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_2291,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),X0)))
% 35.56/4.99      | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3)))) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_3]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_45528,plain,
% 35.56/4.99      ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_2291]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_990,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(X0,k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))))
% 35.56/4.99      | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_4]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_60407,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))))
% 35.56/4.99      | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_990]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_61956,plain,
% 35.56/4.99      ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK2)) ),
% 35.56/4.99      inference(global_propositional_subsumption,
% 35.56/4.99                [status(thm)],
% 35.56/4.99                [c_45246,c_8,c_766,c_11866,c_16557,c_16560,c_25831,
% 35.56/4.99                 c_37957,c_37960,c_45528,c_60407]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_62230,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))))
% 35.56/4.99      | r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3)))) ),
% 35.56/4.99      inference(backward_subsumption_resolution,
% 35.56/4.99                [status(thm)],
% 35.56/4.99                [c_61956,c_2241]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_63630,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))) ),
% 35.56/4.99      inference(global_propositional_subsumption,
% 35.56/4.99                [status(thm)],
% 35.56/4.99                [c_62230,c_11866,c_16557,c_16560,c_25831,c_37957,c_37960,
% 35.56/4.99                 c_45528,c_60407]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_0,plain,
% 35.56/4.99      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 35.56/4.99      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 35.56/4.99      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 ),
% 35.56/4.99      inference(cnf_transformation,[],[f49]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_63642,plain,
% 35.56/4.99      ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))))
% 35.56/4.99      | k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))) ),
% 35.56/4.99      inference(resolution,[status(thm)],[c_63630,c_0]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_343,plain,
% 35.56/4.99      ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))))
% 35.56/4.99      | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))))
% 35.56/4.99      | k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))))) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_0]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_64395,plain,
% 35.56/4.99      ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3)))) ),
% 35.56/4.99      inference(global_propositional_subsumption,
% 35.56/4.99                [status(thm)],
% 35.56/4.99                [c_63642,c_8,c_343,c_11866,c_16557,c_16560,c_25831,
% 35.56/4.99                 c_37957,c_37960,c_45528,c_60407]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_65309,plain,
% 35.56/4.99      ( ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4)))) ),
% 35.56/4.99      inference(resolution,[status(thm)],[c_64395,c_3]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(c_7026,plain,
% 35.56/4.99      ( r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))))
% 35.56/4.99      | ~ r2_hidden(sK0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k1_tarski(sK4))),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k5_xboole_0(k1_tarski(sK7),k4_xboole_0(k5_xboole_0(k1_tarski(sK8),k4_xboole_0(k1_tarski(sK9),k1_tarski(sK8))),k1_tarski(sK7))),k1_tarski(sK6))),k1_tarski(sK5))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2)))))),k1_tarski(sK3)) ),
% 35.56/4.99      inference(instantiation,[status(thm)],[c_4]) ).
% 35.56/4.99  
% 35.56/4.99  cnf(contradiction,plain,
% 35.56/4.99      ( $false ),
% 35.56/4.99      inference(minisat,
% 35.56/4.99                [status(thm)],
% 35.56/4.99                [c_65309,c_63630,c_11364,c_7026,c_343,c_8]) ).
% 35.56/4.99  
% 35.56/4.99  
% 35.56/4.99  % SZS output end CNFRefutation for theBenchmark.p
% 35.56/4.99  
% 35.56/4.99  ------                               Statistics
% 35.56/4.99  
% 35.56/4.99  ------ Selected
% 35.56/4.99  
% 35.56/4.99  total_time:                             4.099
% 35.56/4.99  
%------------------------------------------------------------------------------
