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
% DateTime   : Thu Dec  3 11:36:09 EST 2020

% Result     : Theorem 7.55s
% Output     : CNFRefutation 7.55s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 900 expanded)
%              Number of clauses        :   70 ( 297 expanded)
%              Number of leaves         :   25 ( 242 expanded)
%              Depth                    :   21
%              Number of atoms          :  352 (1382 expanded)
%              Number of equality atoms :  200 ( 980 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
        & ( r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) )
   => ( ( ~ r2_hidden(sK2,sK3)
        | k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0 )
      & ( r2_hidden(sK2,sK3)
        | k4_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ~ r2_hidden(sK2,sK3)
      | k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0 )
    & ( r2_hidden(sK2,sK3)
      | k4_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f42])).

fof(f77,plain,
    ( r2_hidden(sK2,sK3)
    | k4_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f79,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f54,f61])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f80])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f70,f81])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f82])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f83])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f67,f84])).

fof(f101,plain,
    ( r2_hidden(sK2,sK3)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f77,f79,f85])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f85])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f47,f79])).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f46,f79])).

fof(f103,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) ) ),
    inference(equality_resolution,[],[f91])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f86,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f62,f79])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f92,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f45,f79])).

fof(f104,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) ) ),
    inference(equality_resolution,[],[f92])).

fof(f23,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f99,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f76,f85])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f98,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f75,f84])).

fof(f78,plain,
    ( ~ r2_hidden(sK2,sK3)
    | k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

fof(f100,plain,
    ( ~ r2_hidden(sK2,sK3)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f78,f79,f85])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f64,f85])).

fof(f107,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f95])).

fof(f108,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f107])).

cnf(c_16,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_15,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1265,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_16,c_15])).

cnf(c_13,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1155,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_13,c_1])).

cnf(c_1290,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1265,c_1155])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK2,sK3)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_437,negated_conjecture,
    ( r2_hidden(sK2,sK3)
    | k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_25,c_15,c_1])).

cnf(c_892,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) = k1_xboole_0
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_1516,plain,
    ( k5_xboole_0(sK3,k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1290,c_892])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X1 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_894,plain,
    ( k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2202,plain,
    ( k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK3
    | k5_xboole_0(sK3,k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1516,c_894])).

cnf(c_1537,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_15,c_1290])).

cnf(c_2988,plain,
    ( k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X0,k1_xboole_0))
    | k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_2202,c_1537])).

cnf(c_3019,plain,
    ( k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k5_xboole_0(k5_xboole_0(X0,sK3),X0)
    | k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_2988,c_13])).

cnf(c_1534,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_1290])).

cnf(c_1711,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_1534,c_1534])).

cnf(c_3020,plain,
    ( k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_3019,c_1711])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_441,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))) ),
    inference(theory_normalisation,[status(thm)],[c_5,c_15,c_1])).

cnf(c_906,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_1025,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_15,c_1])).

cnf(c_2225,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_1711,c_1025])).

cnf(c_2265,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
    inference(light_normalisation,[status(thm)],[c_2225,c_15])).

cnf(c_33524,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(k2_xboole_0(X1,X2),X2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_906,c_2265])).

cnf(c_33554,plain,
    ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(sK3,sK3)) = iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3020,c_33524])).

cnf(c_33639,plain,
    ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_33554,c_16])).

cnf(c_33757,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top
    | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_33639])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_440,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k2_xboole_0(X2,X1))))) ),
    inference(theory_normalisation,[status(thm)],[c_6,c_15,c_1])).

cnf(c_905,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k2_xboole_0(X2,X1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_440])).

cnf(c_29299,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k2_xboole_0(X2,X1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_905,c_1290])).

cnf(c_29315,plain,
    ( r2_hidden(X0,k5_xboole_0(sK3,sK3)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3020,c_29299])).

cnf(c_29354,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29315,c_16])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_445,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X1,X0))))) = k2_xboole_0(X0,X1) ),
    inference(theory_normalisation,[status(thm)],[c_0,c_15,c_1])).

cnf(c_1518,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1290,c_445])).

cnf(c_7153,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1518,c_1290])).

cnf(c_14,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_899,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7396,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7153,c_899])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_900,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_18929,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_7396,c_900])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_439,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))) ),
    inference(theory_normalisation,[status(thm)],[c_7,c_15,c_1])).

cnf(c_904,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_25379,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(k2_xboole_0(X1,X2),X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_904,c_2265])).

cnf(c_25415,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18929,c_25379])).

cnf(c_25439,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_25415,c_16])).

cnf(c_23,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_22,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1414,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_23,c_22])).

cnf(c_29316,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1414,c_29299])).

cnf(c_29349,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29316,c_16])).

cnf(c_32271,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29354,c_25439,c_29349])).

cnf(c_32274,plain,
    ( r2_hidden(sK2,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_32271])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(sK2,sK3)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_438,negated_conjecture,
    ( ~ r2_hidden(sK2,sK3)
    | k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_24,c_15,c_1])).

cnf(c_893,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_1517,plain,
    ( k5_xboole_0(sK3,k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_xboole_0
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1290,c_893])).

cnf(c_3393,plain,
    ( k5_xboole_0(sK3,sK3) != k1_xboole_0
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3020,c_1517])).

cnf(c_3396,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3393,c_16])).

cnf(c_3397,plain,
    ( r2_hidden(sK2,sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3396])).

cnf(c_19,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_36,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_38,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33757,c_32274,c_3397,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:25:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 7.55/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.55/1.49  
% 7.55/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.55/1.49  
% 7.55/1.49  ------  iProver source info
% 7.55/1.49  
% 7.55/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.55/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.55/1.49  git: non_committed_changes: false
% 7.55/1.49  git: last_make_outside_of_git: false
% 7.55/1.49  
% 7.55/1.49  ------ 
% 7.55/1.49  
% 7.55/1.49  ------ Input Options
% 7.55/1.49  
% 7.55/1.49  --out_options                           all
% 7.55/1.49  --tptp_safe_out                         true
% 7.55/1.49  --problem_path                          ""
% 7.55/1.49  --include_path                          ""
% 7.55/1.49  --clausifier                            res/vclausify_rel
% 7.55/1.49  --clausifier_options                    --mode clausify
% 7.55/1.49  --stdin                                 false
% 7.55/1.49  --stats_out                             all
% 7.55/1.49  
% 7.55/1.49  ------ General Options
% 7.55/1.49  
% 7.55/1.49  --fof                                   false
% 7.55/1.49  --time_out_real                         305.
% 7.55/1.49  --time_out_virtual                      -1.
% 7.55/1.49  --symbol_type_check                     false
% 7.55/1.49  --clausify_out                          false
% 7.55/1.49  --sig_cnt_out                           false
% 7.55/1.49  --trig_cnt_out                          false
% 7.55/1.49  --trig_cnt_out_tolerance                1.
% 7.55/1.49  --trig_cnt_out_sk_spl                   false
% 7.55/1.49  --abstr_cl_out                          false
% 7.55/1.49  
% 7.55/1.49  ------ Global Options
% 7.55/1.49  
% 7.55/1.49  --schedule                              default
% 7.55/1.49  --add_important_lit                     false
% 7.55/1.49  --prop_solver_per_cl                    1000
% 7.55/1.49  --min_unsat_core                        false
% 7.55/1.49  --soft_assumptions                      false
% 7.55/1.49  --soft_lemma_size                       3
% 7.55/1.49  --prop_impl_unit_size                   0
% 7.55/1.49  --prop_impl_unit                        []
% 7.55/1.49  --share_sel_clauses                     true
% 7.55/1.49  --reset_solvers                         false
% 7.55/1.49  --bc_imp_inh                            [conj_cone]
% 7.55/1.49  --conj_cone_tolerance                   3.
% 7.55/1.49  --extra_neg_conj                        none
% 7.55/1.49  --large_theory_mode                     true
% 7.55/1.49  --prolific_symb_bound                   200
% 7.55/1.49  --lt_threshold                          2000
% 7.55/1.49  --clause_weak_htbl                      true
% 7.55/1.49  --gc_record_bc_elim                     false
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing Options
% 7.55/1.49  
% 7.55/1.49  --preprocessing_flag                    true
% 7.55/1.49  --time_out_prep_mult                    0.1
% 7.55/1.49  --splitting_mode                        input
% 7.55/1.49  --splitting_grd                         true
% 7.55/1.49  --splitting_cvd                         false
% 7.55/1.49  --splitting_cvd_svl                     false
% 7.55/1.49  --splitting_nvd                         32
% 7.55/1.49  --sub_typing                            true
% 7.55/1.49  --prep_gs_sim                           true
% 7.55/1.49  --prep_unflatten                        true
% 7.55/1.49  --prep_res_sim                          true
% 7.55/1.49  --prep_upred                            true
% 7.55/1.49  --prep_sem_filter                       exhaustive
% 7.55/1.49  --prep_sem_filter_out                   false
% 7.55/1.49  --pred_elim                             true
% 7.55/1.49  --res_sim_input                         true
% 7.55/1.49  --eq_ax_congr_red                       true
% 7.55/1.49  --pure_diseq_elim                       true
% 7.55/1.49  --brand_transform                       false
% 7.55/1.49  --non_eq_to_eq                          false
% 7.55/1.49  --prep_def_merge                        true
% 7.55/1.49  --prep_def_merge_prop_impl              false
% 7.55/1.49  --prep_def_merge_mbd                    true
% 7.55/1.49  --prep_def_merge_tr_red                 false
% 7.55/1.49  --prep_def_merge_tr_cl                  false
% 7.55/1.49  --smt_preprocessing                     true
% 7.55/1.49  --smt_ac_axioms                         fast
% 7.55/1.49  --preprocessed_out                      false
% 7.55/1.49  --preprocessed_stats                    false
% 7.55/1.49  
% 7.55/1.49  ------ Abstraction refinement Options
% 7.55/1.49  
% 7.55/1.49  --abstr_ref                             []
% 7.55/1.49  --abstr_ref_prep                        false
% 7.55/1.49  --abstr_ref_until_sat                   false
% 7.55/1.49  --abstr_ref_sig_restrict                funpre
% 7.55/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.55/1.49  --abstr_ref_under                       []
% 7.55/1.49  
% 7.55/1.49  ------ SAT Options
% 7.55/1.49  
% 7.55/1.49  --sat_mode                              false
% 7.55/1.49  --sat_fm_restart_options                ""
% 7.55/1.49  --sat_gr_def                            false
% 7.55/1.49  --sat_epr_types                         true
% 7.55/1.49  --sat_non_cyclic_types                  false
% 7.55/1.49  --sat_finite_models                     false
% 7.55/1.49  --sat_fm_lemmas                         false
% 7.55/1.49  --sat_fm_prep                           false
% 7.55/1.49  --sat_fm_uc_incr                        true
% 7.55/1.49  --sat_out_model                         small
% 7.55/1.49  --sat_out_clauses                       false
% 7.55/1.49  
% 7.55/1.49  ------ QBF Options
% 7.55/1.49  
% 7.55/1.49  --qbf_mode                              false
% 7.55/1.49  --qbf_elim_univ                         false
% 7.55/1.49  --qbf_dom_inst                          none
% 7.55/1.49  --qbf_dom_pre_inst                      false
% 7.55/1.49  --qbf_sk_in                             false
% 7.55/1.49  --qbf_pred_elim                         true
% 7.55/1.49  --qbf_split                             512
% 7.55/1.49  
% 7.55/1.49  ------ BMC1 Options
% 7.55/1.49  
% 7.55/1.49  --bmc1_incremental                      false
% 7.55/1.49  --bmc1_axioms                           reachable_all
% 7.55/1.49  --bmc1_min_bound                        0
% 7.55/1.49  --bmc1_max_bound                        -1
% 7.55/1.49  --bmc1_max_bound_default                -1
% 7.55/1.49  --bmc1_symbol_reachability              true
% 7.55/1.49  --bmc1_property_lemmas                  false
% 7.55/1.49  --bmc1_k_induction                      false
% 7.55/1.49  --bmc1_non_equiv_states                 false
% 7.55/1.49  --bmc1_deadlock                         false
% 7.55/1.49  --bmc1_ucm                              false
% 7.55/1.49  --bmc1_add_unsat_core                   none
% 7.55/1.49  --bmc1_unsat_core_children              false
% 7.55/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.55/1.49  --bmc1_out_stat                         full
% 7.55/1.49  --bmc1_ground_init                      false
% 7.55/1.49  --bmc1_pre_inst_next_state              false
% 7.55/1.49  --bmc1_pre_inst_state                   false
% 7.55/1.49  --bmc1_pre_inst_reach_state             false
% 7.55/1.49  --bmc1_out_unsat_core                   false
% 7.55/1.49  --bmc1_aig_witness_out                  false
% 7.55/1.49  --bmc1_verbose                          false
% 7.55/1.49  --bmc1_dump_clauses_tptp                false
% 7.55/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.55/1.49  --bmc1_dump_file                        -
% 7.55/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.55/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.55/1.49  --bmc1_ucm_extend_mode                  1
% 7.55/1.49  --bmc1_ucm_init_mode                    2
% 7.55/1.49  --bmc1_ucm_cone_mode                    none
% 7.55/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.55/1.49  --bmc1_ucm_relax_model                  4
% 7.55/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.55/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.55/1.49  --bmc1_ucm_layered_model                none
% 7.55/1.49  --bmc1_ucm_max_lemma_size               10
% 7.55/1.49  
% 7.55/1.49  ------ AIG Options
% 7.55/1.49  
% 7.55/1.49  --aig_mode                              false
% 7.55/1.49  
% 7.55/1.49  ------ Instantiation Options
% 7.55/1.49  
% 7.55/1.49  --instantiation_flag                    true
% 7.55/1.49  --inst_sos_flag                         false
% 7.55/1.49  --inst_sos_phase                        true
% 7.55/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.55/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.55/1.49  --inst_lit_sel_side                     num_symb
% 7.55/1.49  --inst_solver_per_active                1400
% 7.55/1.49  --inst_solver_calls_frac                1.
% 7.55/1.49  --inst_passive_queue_type               priority_queues
% 7.55/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.55/1.49  --inst_passive_queues_freq              [25;2]
% 7.55/1.49  --inst_dismatching                      true
% 7.55/1.49  --inst_eager_unprocessed_to_passive     true
% 7.55/1.49  --inst_prop_sim_given                   true
% 7.55/1.49  --inst_prop_sim_new                     false
% 7.55/1.49  --inst_subs_new                         false
% 7.55/1.49  --inst_eq_res_simp                      false
% 7.55/1.49  --inst_subs_given                       false
% 7.55/1.49  --inst_orphan_elimination               true
% 7.55/1.49  --inst_learning_loop_flag               true
% 7.55/1.49  --inst_learning_start                   3000
% 7.55/1.49  --inst_learning_factor                  2
% 7.55/1.49  --inst_start_prop_sim_after_learn       3
% 7.55/1.49  --inst_sel_renew                        solver
% 7.55/1.49  --inst_lit_activity_flag                true
% 7.55/1.49  --inst_restr_to_given                   false
% 7.55/1.49  --inst_activity_threshold               500
% 7.55/1.49  --inst_out_proof                        true
% 7.55/1.49  
% 7.55/1.49  ------ Resolution Options
% 7.55/1.49  
% 7.55/1.49  --resolution_flag                       true
% 7.55/1.49  --res_lit_sel                           adaptive
% 7.55/1.49  --res_lit_sel_side                      none
% 7.55/1.49  --res_ordering                          kbo
% 7.55/1.49  --res_to_prop_solver                    active
% 7.55/1.49  --res_prop_simpl_new                    false
% 7.55/1.49  --res_prop_simpl_given                  true
% 7.55/1.49  --res_passive_queue_type                priority_queues
% 7.55/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.55/1.49  --res_passive_queues_freq               [15;5]
% 7.55/1.49  --res_forward_subs                      full
% 7.55/1.49  --res_backward_subs                     full
% 7.55/1.49  --res_forward_subs_resolution           true
% 7.55/1.49  --res_backward_subs_resolution          true
% 7.55/1.49  --res_orphan_elimination                true
% 7.55/1.49  --res_time_limit                        2.
% 7.55/1.49  --res_out_proof                         true
% 7.55/1.49  
% 7.55/1.49  ------ Superposition Options
% 7.55/1.49  
% 7.55/1.49  --superposition_flag                    true
% 7.55/1.49  --sup_passive_queue_type                priority_queues
% 7.55/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.55/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.55/1.49  --demod_completeness_check              fast
% 7.55/1.49  --demod_use_ground                      true
% 7.55/1.49  --sup_to_prop_solver                    passive
% 7.55/1.49  --sup_prop_simpl_new                    true
% 7.55/1.49  --sup_prop_simpl_given                  true
% 7.55/1.49  --sup_fun_splitting                     false
% 7.55/1.49  --sup_smt_interval                      50000
% 7.55/1.49  
% 7.55/1.49  ------ Superposition Simplification Setup
% 7.55/1.49  
% 7.55/1.49  --sup_indices_passive                   []
% 7.55/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.55/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.49  --sup_full_bw                           [BwDemod]
% 7.55/1.49  --sup_immed_triv                        [TrivRules]
% 7.55/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.55/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.49  --sup_immed_bw_main                     []
% 7.55/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.55/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.49  
% 7.55/1.49  ------ Combination Options
% 7.55/1.49  
% 7.55/1.49  --comb_res_mult                         3
% 7.55/1.49  --comb_sup_mult                         2
% 7.55/1.49  --comb_inst_mult                        10
% 7.55/1.49  
% 7.55/1.49  ------ Debug Options
% 7.55/1.49  
% 7.55/1.49  --dbg_backtrace                         false
% 7.55/1.49  --dbg_dump_prop_clauses                 false
% 7.55/1.49  --dbg_dump_prop_clauses_file            -
% 7.55/1.49  --dbg_out_stat                          false
% 7.55/1.49  ------ Parsing...
% 7.55/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.55/1.49  ------ Proving...
% 7.55/1.49  ------ Problem Properties 
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  clauses                                 25
% 7.55/1.49  conjectures                             2
% 7.55/1.49  EPR                                     2
% 7.55/1.49  Horn                                    19
% 7.55/1.49  unary                                   10
% 7.55/1.49  binary                                  8
% 7.55/1.49  lits                                    48
% 7.55/1.49  lits eq                                 20
% 7.55/1.49  fd_pure                                 0
% 7.55/1.49  fd_pseudo                               0
% 7.55/1.49  fd_cond                                 0
% 7.55/1.49  fd_pseudo_cond                          6
% 7.55/1.49  AC symbols                              1
% 7.55/1.49  
% 7.55/1.49  ------ Schedule dynamic 5 is on 
% 7.55/1.49  
% 7.55/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  ------ 
% 7.55/1.49  Current options:
% 7.55/1.49  ------ 
% 7.55/1.49  
% 7.55/1.49  ------ Input Options
% 7.55/1.49  
% 7.55/1.49  --out_options                           all
% 7.55/1.49  --tptp_safe_out                         true
% 7.55/1.49  --problem_path                          ""
% 7.55/1.49  --include_path                          ""
% 7.55/1.49  --clausifier                            res/vclausify_rel
% 7.55/1.49  --clausifier_options                    --mode clausify
% 7.55/1.49  --stdin                                 false
% 7.55/1.49  --stats_out                             all
% 7.55/1.49  
% 7.55/1.49  ------ General Options
% 7.55/1.49  
% 7.55/1.49  --fof                                   false
% 7.55/1.49  --time_out_real                         305.
% 7.55/1.49  --time_out_virtual                      -1.
% 7.55/1.49  --symbol_type_check                     false
% 7.55/1.49  --clausify_out                          false
% 7.55/1.49  --sig_cnt_out                           false
% 7.55/1.49  --trig_cnt_out                          false
% 7.55/1.49  --trig_cnt_out_tolerance                1.
% 7.55/1.49  --trig_cnt_out_sk_spl                   false
% 7.55/1.49  --abstr_cl_out                          false
% 7.55/1.49  
% 7.55/1.49  ------ Global Options
% 7.55/1.49  
% 7.55/1.49  --schedule                              default
% 7.55/1.49  --add_important_lit                     false
% 7.55/1.49  --prop_solver_per_cl                    1000
% 7.55/1.49  --min_unsat_core                        false
% 7.55/1.49  --soft_assumptions                      false
% 7.55/1.49  --soft_lemma_size                       3
% 7.55/1.49  --prop_impl_unit_size                   0
% 7.55/1.49  --prop_impl_unit                        []
% 7.55/1.49  --share_sel_clauses                     true
% 7.55/1.49  --reset_solvers                         false
% 7.55/1.49  --bc_imp_inh                            [conj_cone]
% 7.55/1.49  --conj_cone_tolerance                   3.
% 7.55/1.49  --extra_neg_conj                        none
% 7.55/1.49  --large_theory_mode                     true
% 7.55/1.49  --prolific_symb_bound                   200
% 7.55/1.49  --lt_threshold                          2000
% 7.55/1.49  --clause_weak_htbl                      true
% 7.55/1.49  --gc_record_bc_elim                     false
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing Options
% 7.55/1.49  
% 7.55/1.49  --preprocessing_flag                    true
% 7.55/1.49  --time_out_prep_mult                    0.1
% 7.55/1.49  --splitting_mode                        input
% 7.55/1.49  --splitting_grd                         true
% 7.55/1.49  --splitting_cvd                         false
% 7.55/1.49  --splitting_cvd_svl                     false
% 7.55/1.49  --splitting_nvd                         32
% 7.55/1.49  --sub_typing                            true
% 7.55/1.49  --prep_gs_sim                           true
% 7.55/1.49  --prep_unflatten                        true
% 7.55/1.49  --prep_res_sim                          true
% 7.55/1.49  --prep_upred                            true
% 7.55/1.49  --prep_sem_filter                       exhaustive
% 7.55/1.49  --prep_sem_filter_out                   false
% 7.55/1.49  --pred_elim                             true
% 7.55/1.49  --res_sim_input                         true
% 7.55/1.49  --eq_ax_congr_red                       true
% 7.55/1.49  --pure_diseq_elim                       true
% 7.55/1.49  --brand_transform                       false
% 7.55/1.49  --non_eq_to_eq                          false
% 7.55/1.49  --prep_def_merge                        true
% 7.55/1.49  --prep_def_merge_prop_impl              false
% 7.55/1.49  --prep_def_merge_mbd                    true
% 7.55/1.49  --prep_def_merge_tr_red                 false
% 7.55/1.49  --prep_def_merge_tr_cl                  false
% 7.55/1.49  --smt_preprocessing                     true
% 7.55/1.49  --smt_ac_axioms                         fast
% 7.55/1.49  --preprocessed_out                      false
% 7.55/1.49  --preprocessed_stats                    false
% 7.55/1.49  
% 7.55/1.49  ------ Abstraction refinement Options
% 7.55/1.49  
% 7.55/1.49  --abstr_ref                             []
% 7.55/1.49  --abstr_ref_prep                        false
% 7.55/1.49  --abstr_ref_until_sat                   false
% 7.55/1.49  --abstr_ref_sig_restrict                funpre
% 7.55/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.55/1.49  --abstr_ref_under                       []
% 7.55/1.49  
% 7.55/1.49  ------ SAT Options
% 7.55/1.49  
% 7.55/1.49  --sat_mode                              false
% 7.55/1.49  --sat_fm_restart_options                ""
% 7.55/1.49  --sat_gr_def                            false
% 7.55/1.49  --sat_epr_types                         true
% 7.55/1.49  --sat_non_cyclic_types                  false
% 7.55/1.49  --sat_finite_models                     false
% 7.55/1.49  --sat_fm_lemmas                         false
% 7.55/1.49  --sat_fm_prep                           false
% 7.55/1.49  --sat_fm_uc_incr                        true
% 7.55/1.49  --sat_out_model                         small
% 7.55/1.49  --sat_out_clauses                       false
% 7.55/1.49  
% 7.55/1.49  ------ QBF Options
% 7.55/1.49  
% 7.55/1.49  --qbf_mode                              false
% 7.55/1.49  --qbf_elim_univ                         false
% 7.55/1.49  --qbf_dom_inst                          none
% 7.55/1.49  --qbf_dom_pre_inst                      false
% 7.55/1.49  --qbf_sk_in                             false
% 7.55/1.49  --qbf_pred_elim                         true
% 7.55/1.49  --qbf_split                             512
% 7.55/1.49  
% 7.55/1.49  ------ BMC1 Options
% 7.55/1.49  
% 7.55/1.49  --bmc1_incremental                      false
% 7.55/1.49  --bmc1_axioms                           reachable_all
% 7.55/1.49  --bmc1_min_bound                        0
% 7.55/1.49  --bmc1_max_bound                        -1
% 7.55/1.49  --bmc1_max_bound_default                -1
% 7.55/1.49  --bmc1_symbol_reachability              true
% 7.55/1.49  --bmc1_property_lemmas                  false
% 7.55/1.49  --bmc1_k_induction                      false
% 7.55/1.49  --bmc1_non_equiv_states                 false
% 7.55/1.49  --bmc1_deadlock                         false
% 7.55/1.49  --bmc1_ucm                              false
% 7.55/1.49  --bmc1_add_unsat_core                   none
% 7.55/1.49  --bmc1_unsat_core_children              false
% 7.55/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.55/1.49  --bmc1_out_stat                         full
% 7.55/1.49  --bmc1_ground_init                      false
% 7.55/1.49  --bmc1_pre_inst_next_state              false
% 7.55/1.49  --bmc1_pre_inst_state                   false
% 7.55/1.49  --bmc1_pre_inst_reach_state             false
% 7.55/1.49  --bmc1_out_unsat_core                   false
% 7.55/1.49  --bmc1_aig_witness_out                  false
% 7.55/1.49  --bmc1_verbose                          false
% 7.55/1.49  --bmc1_dump_clauses_tptp                false
% 7.55/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.55/1.49  --bmc1_dump_file                        -
% 7.55/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.55/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.55/1.49  --bmc1_ucm_extend_mode                  1
% 7.55/1.49  --bmc1_ucm_init_mode                    2
% 7.55/1.49  --bmc1_ucm_cone_mode                    none
% 7.55/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.55/1.49  --bmc1_ucm_relax_model                  4
% 7.55/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.55/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.55/1.49  --bmc1_ucm_layered_model                none
% 7.55/1.49  --bmc1_ucm_max_lemma_size               10
% 7.55/1.49  
% 7.55/1.49  ------ AIG Options
% 7.55/1.49  
% 7.55/1.49  --aig_mode                              false
% 7.55/1.49  
% 7.55/1.49  ------ Instantiation Options
% 7.55/1.49  
% 7.55/1.49  --instantiation_flag                    true
% 7.55/1.49  --inst_sos_flag                         false
% 7.55/1.49  --inst_sos_phase                        true
% 7.55/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.55/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.55/1.49  --inst_lit_sel_side                     none
% 7.55/1.49  --inst_solver_per_active                1400
% 7.55/1.49  --inst_solver_calls_frac                1.
% 7.55/1.49  --inst_passive_queue_type               priority_queues
% 7.55/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.55/1.49  --inst_passive_queues_freq              [25;2]
% 7.55/1.49  --inst_dismatching                      true
% 7.55/1.49  --inst_eager_unprocessed_to_passive     true
% 7.55/1.49  --inst_prop_sim_given                   true
% 7.55/1.49  --inst_prop_sim_new                     false
% 7.55/1.49  --inst_subs_new                         false
% 7.55/1.49  --inst_eq_res_simp                      false
% 7.55/1.49  --inst_subs_given                       false
% 7.55/1.49  --inst_orphan_elimination               true
% 7.55/1.49  --inst_learning_loop_flag               true
% 7.55/1.49  --inst_learning_start                   3000
% 7.55/1.49  --inst_learning_factor                  2
% 7.55/1.49  --inst_start_prop_sim_after_learn       3
% 7.55/1.49  --inst_sel_renew                        solver
% 7.55/1.49  --inst_lit_activity_flag                true
% 7.55/1.49  --inst_restr_to_given                   false
% 7.55/1.49  --inst_activity_threshold               500
% 7.55/1.49  --inst_out_proof                        true
% 7.55/1.49  
% 7.55/1.49  ------ Resolution Options
% 7.55/1.49  
% 7.55/1.49  --resolution_flag                       false
% 7.55/1.49  --res_lit_sel                           adaptive
% 7.55/1.49  --res_lit_sel_side                      none
% 7.55/1.49  --res_ordering                          kbo
% 7.55/1.49  --res_to_prop_solver                    active
% 7.55/1.49  --res_prop_simpl_new                    false
% 7.55/1.49  --res_prop_simpl_given                  true
% 7.55/1.49  --res_passive_queue_type                priority_queues
% 7.55/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.55/1.49  --res_passive_queues_freq               [15;5]
% 7.55/1.49  --res_forward_subs                      full
% 7.55/1.49  --res_backward_subs                     full
% 7.55/1.49  --res_forward_subs_resolution           true
% 7.55/1.49  --res_backward_subs_resolution          true
% 7.55/1.49  --res_orphan_elimination                true
% 7.55/1.49  --res_time_limit                        2.
% 7.55/1.49  --res_out_proof                         true
% 7.55/1.49  
% 7.55/1.49  ------ Superposition Options
% 7.55/1.49  
% 7.55/1.49  --superposition_flag                    true
% 7.55/1.49  --sup_passive_queue_type                priority_queues
% 7.55/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.55/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.55/1.49  --demod_completeness_check              fast
% 7.55/1.49  --demod_use_ground                      true
% 7.55/1.49  --sup_to_prop_solver                    passive
% 7.55/1.49  --sup_prop_simpl_new                    true
% 7.55/1.49  --sup_prop_simpl_given                  true
% 7.55/1.49  --sup_fun_splitting                     false
% 7.55/1.49  --sup_smt_interval                      50000
% 7.55/1.49  
% 7.55/1.49  ------ Superposition Simplification Setup
% 7.55/1.49  
% 7.55/1.49  --sup_indices_passive                   []
% 7.55/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.55/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.49  --sup_full_bw                           [BwDemod]
% 7.55/1.49  --sup_immed_triv                        [TrivRules]
% 7.55/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.55/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.49  --sup_immed_bw_main                     []
% 7.55/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.55/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.49  
% 7.55/1.49  ------ Combination Options
% 7.55/1.49  
% 7.55/1.49  --comb_res_mult                         3
% 7.55/1.49  --comb_sup_mult                         2
% 7.55/1.49  --comb_inst_mult                        10
% 7.55/1.49  
% 7.55/1.49  ------ Debug Options
% 7.55/1.49  
% 7.55/1.49  --dbg_backtrace                         false
% 7.55/1.49  --dbg_dump_prop_clauses                 false
% 7.55/1.49  --dbg_dump_prop_clauses_file            -
% 7.55/1.49  --dbg_out_stat                          false
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  ------ Proving...
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  % SZS status Theorem for theBenchmark.p
% 7.55/1.49  
% 7.55/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.55/1.49  
% 7.55/1.49  fof(f10,axiom,(
% 7.55/1.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f60,plain,(
% 7.55/1.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.55/1.49    inference(cnf_transformation,[],[f10])).
% 7.55/1.49  
% 7.55/1.49  fof(f9,axiom,(
% 7.55/1.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f59,plain,(
% 7.55/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f9])).
% 7.55/1.49  
% 7.55/1.49  fof(f7,axiom,(
% 7.55/1.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f57,plain,(
% 7.55/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.55/1.49    inference(cnf_transformation,[],[f7])).
% 7.55/1.49  
% 7.55/1.49  fof(f1,axiom,(
% 7.55/1.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f44,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f1])).
% 7.55/1.49  
% 7.55/1.49  fof(f24,conjecture,(
% 7.55/1.49    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f25,negated_conjecture,(
% 7.55/1.49    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 7.55/1.49    inference(negated_conjecture,[],[f24])).
% 7.55/1.49  
% 7.55/1.49  fof(f29,plain,(
% 7.55/1.49    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <~> r2_hidden(X0,X1))),
% 7.55/1.49    inference(ennf_transformation,[],[f25])).
% 7.55/1.49  
% 7.55/1.49  fof(f41,plain,(
% 7.55/1.49    ? [X0,X1] : ((~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0))),
% 7.55/1.49    inference(nnf_transformation,[],[f29])).
% 7.55/1.49  
% 7.55/1.49  fof(f42,plain,(
% 7.55/1.49    ? [X0,X1] : ((~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)) => ((~r2_hidden(sK2,sK3) | k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0) & (r2_hidden(sK2,sK3) | k4_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0))),
% 7.55/1.49    introduced(choice_axiom,[])).
% 7.55/1.49  
% 7.55/1.49  fof(f43,plain,(
% 7.55/1.49    (~r2_hidden(sK2,sK3) | k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0) & (r2_hidden(sK2,sK3) | k4_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0)),
% 7.55/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f42])).
% 7.55/1.49  
% 7.55/1.49  fof(f77,plain,(
% 7.55/1.49    r2_hidden(sK2,sK3) | k4_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0),
% 7.55/1.49    inference(cnf_transformation,[],[f43])).
% 7.55/1.49  
% 7.55/1.49  fof(f4,axiom,(
% 7.55/1.49    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f54,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f4])).
% 7.55/1.49  
% 7.55/1.49  fof(f11,axiom,(
% 7.55/1.49    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f61,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f11])).
% 7.55/1.49  
% 7.55/1.49  fof(f79,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k4_xboole_0(X0,X1)) )),
% 7.55/1.49    inference(definition_unfolding,[],[f54,f61])).
% 7.55/1.49  
% 7.55/1.49  fof(f14,axiom,(
% 7.55/1.49    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f67,plain,(
% 7.55/1.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f14])).
% 7.55/1.49  
% 7.55/1.49  fof(f15,axiom,(
% 7.55/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f68,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f15])).
% 7.55/1.49  
% 7.55/1.49  fof(f16,axiom,(
% 7.55/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f69,plain,(
% 7.55/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f16])).
% 7.55/1.49  
% 7.55/1.49  fof(f17,axiom,(
% 7.55/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f70,plain,(
% 7.55/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f17])).
% 7.55/1.49  
% 7.55/1.49  fof(f18,axiom,(
% 7.55/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f71,plain,(
% 7.55/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f18])).
% 7.55/1.49  
% 7.55/1.49  fof(f19,axiom,(
% 7.55/1.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f72,plain,(
% 7.55/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f19])).
% 7.55/1.49  
% 7.55/1.49  fof(f20,axiom,(
% 7.55/1.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f73,plain,(
% 7.55/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f20])).
% 7.55/1.49  
% 7.55/1.49  fof(f80,plain,(
% 7.55/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.55/1.49    inference(definition_unfolding,[],[f72,f73])).
% 7.55/1.49  
% 7.55/1.49  fof(f81,plain,(
% 7.55/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.55/1.49    inference(definition_unfolding,[],[f71,f80])).
% 7.55/1.49  
% 7.55/1.49  fof(f82,plain,(
% 7.55/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.55/1.49    inference(definition_unfolding,[],[f70,f81])).
% 7.55/1.49  
% 7.55/1.49  fof(f83,plain,(
% 7.55/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.55/1.49    inference(definition_unfolding,[],[f69,f82])).
% 7.55/1.49  
% 7.55/1.49  fof(f84,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.55/1.49    inference(definition_unfolding,[],[f68,f83])).
% 7.55/1.49  
% 7.55/1.49  fof(f85,plain,(
% 7.55/1.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.55/1.49    inference(definition_unfolding,[],[f67,f84])).
% 7.55/1.49  
% 7.55/1.49  fof(f101,plain,(
% 7.55/1.49    r2_hidden(sK2,sK3) | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0),
% 7.55/1.49    inference(definition_unfolding,[],[f77,f79,f85])).
% 7.55/1.49  
% 7.55/1.49  fof(f21,axiom,(
% 7.55/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f28,plain,(
% 7.55/1.49    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 7.55/1.49    inference(ennf_transformation,[],[f21])).
% 7.55/1.49  
% 7.55/1.49  fof(f74,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f28])).
% 7.55/1.49  
% 7.55/1.49  fof(f97,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 7.55/1.49    inference(definition_unfolding,[],[f74,f85])).
% 7.55/1.49  
% 7.55/1.49  fof(f2,axiom,(
% 7.55/1.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f30,plain,(
% 7.55/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.55/1.49    inference(nnf_transformation,[],[f2])).
% 7.55/1.49  
% 7.55/1.49  fof(f31,plain,(
% 7.55/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.55/1.49    inference(flattening,[],[f30])).
% 7.55/1.49  
% 7.55/1.49  fof(f32,plain,(
% 7.55/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.55/1.49    inference(rectify,[],[f31])).
% 7.55/1.49  
% 7.55/1.49  fof(f33,plain,(
% 7.55/1.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.55/1.49    introduced(choice_axiom,[])).
% 7.55/1.49  
% 7.55/1.49  fof(f34,plain,(
% 7.55/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.55/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 7.55/1.49  
% 7.55/1.49  fof(f47,plain,(
% 7.55/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 7.55/1.49    inference(cnf_transformation,[],[f34])).
% 7.55/1.49  
% 7.55/1.49  fof(f90,plain,(
% 7.55/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2) )),
% 7.55/1.49    inference(definition_unfolding,[],[f47,f79])).
% 7.55/1.49  
% 7.55/1.49  fof(f102,plain,(
% 7.55/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.55/1.49    inference(equality_resolution,[],[f90])).
% 7.55/1.49  
% 7.55/1.49  fof(f46,plain,(
% 7.55/1.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.55/1.49    inference(cnf_transformation,[],[f34])).
% 7.55/1.49  
% 7.55/1.49  fof(f91,plain,(
% 7.55/1.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2) )),
% 7.55/1.49    inference(definition_unfolding,[],[f46,f79])).
% 7.55/1.49  
% 7.55/1.49  fof(f103,plain,(
% 7.55/1.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))))) )),
% 7.55/1.49    inference(equality_resolution,[],[f91])).
% 7.55/1.49  
% 7.55/1.49  fof(f12,axiom,(
% 7.55/1.49    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f62,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f12])).
% 7.55/1.49  
% 7.55/1.49  fof(f86,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1)) )),
% 7.55/1.49    inference(definition_unfolding,[],[f62,f79])).
% 7.55/1.49  
% 7.55/1.49  fof(f8,axiom,(
% 7.55/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f58,plain,(
% 7.55/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.55/1.49    inference(cnf_transformation,[],[f8])).
% 7.55/1.49  
% 7.55/1.49  fof(f6,axiom,(
% 7.55/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f27,plain,(
% 7.55/1.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.55/1.49    inference(ennf_transformation,[],[f6])).
% 7.55/1.49  
% 7.55/1.49  fof(f56,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f27])).
% 7.55/1.49  
% 7.55/1.49  fof(f45,plain,(
% 7.55/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.55/1.49    inference(cnf_transformation,[],[f34])).
% 7.55/1.49  
% 7.55/1.49  fof(f92,plain,(
% 7.55/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2) )),
% 7.55/1.49    inference(definition_unfolding,[],[f45,f79])).
% 7.55/1.49  
% 7.55/1.49  fof(f104,plain,(
% 7.55/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))))) )),
% 7.55/1.49    inference(equality_resolution,[],[f92])).
% 7.55/1.49  
% 7.55/1.49  fof(f23,axiom,(
% 7.55/1.49    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f76,plain,(
% 7.55/1.49    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 7.55/1.49    inference(cnf_transformation,[],[f23])).
% 7.55/1.49  
% 7.55/1.49  fof(f99,plain,(
% 7.55/1.49    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 7.55/1.49    inference(definition_unfolding,[],[f76,f85])).
% 7.55/1.49  
% 7.55/1.49  fof(f22,axiom,(
% 7.55/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f75,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.55/1.49    inference(cnf_transformation,[],[f22])).
% 7.55/1.49  
% 7.55/1.49  fof(f98,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.55/1.49    inference(definition_unfolding,[],[f75,f84])).
% 7.55/1.49  
% 7.55/1.49  fof(f78,plain,(
% 7.55/1.49    ~r2_hidden(sK2,sK3) | k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0),
% 7.55/1.49    inference(cnf_transformation,[],[f43])).
% 7.55/1.49  
% 7.55/1.49  fof(f100,plain,(
% 7.55/1.49    ~r2_hidden(sK2,sK3) | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) != k1_xboole_0),
% 7.55/1.49    inference(definition_unfolding,[],[f78,f79,f85])).
% 7.55/1.49  
% 7.55/1.49  fof(f13,axiom,(
% 7.55/1.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f37,plain,(
% 7.55/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.55/1.49    inference(nnf_transformation,[],[f13])).
% 7.55/1.49  
% 7.55/1.49  fof(f38,plain,(
% 7.55/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.55/1.49    inference(rectify,[],[f37])).
% 7.55/1.49  
% 7.55/1.49  fof(f39,plain,(
% 7.55/1.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 7.55/1.49    introduced(choice_axiom,[])).
% 7.55/1.49  
% 7.55/1.49  fof(f40,plain,(
% 7.55/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.55/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 7.55/1.49  
% 7.55/1.49  fof(f64,plain,(
% 7.55/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.55/1.49    inference(cnf_transformation,[],[f40])).
% 7.55/1.49  
% 7.55/1.49  fof(f95,plain,(
% 7.55/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.55/1.49    inference(definition_unfolding,[],[f64,f85])).
% 7.55/1.49  
% 7.55/1.49  fof(f107,plain,(
% 7.55/1.49    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 7.55/1.49    inference(equality_resolution,[],[f95])).
% 7.55/1.49  
% 7.55/1.49  fof(f108,plain,(
% 7.55/1.49    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 7.55/1.49    inference(equality_resolution,[],[f107])).
% 7.55/1.49  
% 7.55/1.49  cnf(c_16,plain,
% 7.55/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.55/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_15,plain,
% 7.55/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.55/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1265,plain,
% 7.55/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_16,c_15]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_13,plain,
% 7.55/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.55/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1,plain,
% 7.55/1.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.55/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1155,plain,
% 7.55/1.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_13,c_1]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1290,plain,
% 7.55/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_1265,c_1155]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_25,negated_conjecture,
% 7.55/1.49      ( r2_hidden(sK2,sK3)
% 7.55/1.49      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
% 7.55/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_437,negated_conjecture,
% 7.55/1.49      ( r2_hidden(sK2,sK3)
% 7.55/1.49      | k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) = k1_xboole_0 ),
% 7.55/1.49      inference(theory_normalisation,[status(thm)],[c_25,c_15,c_1]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_892,plain,
% 7.55/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) = k1_xboole_0
% 7.55/1.49      | r2_hidden(sK2,sK3) = iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1516,plain,
% 7.55/1.49      ( k5_xboole_0(sK3,k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0
% 7.55/1.49      | r2_hidden(sK2,sK3) = iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_1290,c_892]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_21,plain,
% 7.55/1.49      ( ~ r2_hidden(X0,X1)
% 7.55/1.49      | k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X1 ),
% 7.55/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_894,plain,
% 7.55/1.49      ( k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X1
% 7.55/1.49      | r2_hidden(X0,X1) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2202,plain,
% 7.55/1.49      ( k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK3
% 7.55/1.49      | k5_xboole_0(sK3,k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1516,c_894]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1537,plain,
% 7.55/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_15,c_1290]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2988,plain,
% 7.55/1.49      ( k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X0,k1_xboole_0))
% 7.55/1.49      | k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK3 ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_2202,c_1537]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_3019,plain,
% 7.55/1.49      ( k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k5_xboole_0(k5_xboole_0(X0,sK3),X0)
% 7.55/1.49      | k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK3 ),
% 7.55/1.49      inference(light_normalisation,[status(thm)],[c_2988,c_13]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1534,plain,
% 7.55/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1,c_1290]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1711,plain,
% 7.55/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1534,c_1534]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_3020,plain,
% 7.55/1.49      ( k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK3 ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_3019,c_1711]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_5,plain,
% 7.55/1.49      ( ~ r2_hidden(X0,X1)
% 7.55/1.49      | r2_hidden(X0,X2)
% 7.55/1.49      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))) ),
% 7.55/1.49      inference(cnf_transformation,[],[f102]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_441,plain,
% 7.55/1.49      ( ~ r2_hidden(X0,X1)
% 7.55/1.49      | r2_hidden(X0,X2)
% 7.55/1.49      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))) ),
% 7.55/1.49      inference(theory_normalisation,[status(thm)],[c_5,c_15,c_1]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_906,plain,
% 7.55/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.55/1.49      | r2_hidden(X0,X2) = iProver_top
% 7.55/1.49      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))) = iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1025,plain,
% 7.55/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_15,c_1]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2225,plain,
% 7.55/1.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,X1) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1711,c_1025]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2265,plain,
% 7.55/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
% 7.55/1.49      inference(light_normalisation,[status(thm)],[c_2225,c_15]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_33524,plain,
% 7.55/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.55/1.49      | r2_hidden(X0,X2) = iProver_top
% 7.55/1.49      | r2_hidden(X0,k5_xboole_0(k2_xboole_0(X1,X2),X2)) = iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_906,c_2265]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_33554,plain,
% 7.55/1.49      ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 7.55/1.49      | r2_hidden(X0,k5_xboole_0(sK3,sK3)) = iProver_top
% 7.55/1.49      | r2_hidden(X0,sK3) = iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_3020,c_33524]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_33639,plain,
% 7.55/1.49      ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 7.55/1.49      | r2_hidden(X0,sK3) = iProver_top
% 7.55/1.49      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_33554,c_16]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_33757,plain,
% 7.55/1.49      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 7.55/1.49      | r2_hidden(sK2,sK3) = iProver_top
% 7.55/1.49      | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_33639]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_6,plain,
% 7.55/1.49      ( ~ r2_hidden(X0,X1)
% 7.55/1.49      | ~ r2_hidden(X0,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)))) ),
% 7.55/1.49      inference(cnf_transformation,[],[f103]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_440,plain,
% 7.55/1.49      ( ~ r2_hidden(X0,X1)
% 7.55/1.49      | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k2_xboole_0(X2,X1))))) ),
% 7.55/1.49      inference(theory_normalisation,[status(thm)],[c_6,c_15,c_1]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_905,plain,
% 7.55/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.55/1.49      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k2_xboole_0(X2,X1))))) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_440]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_29299,plain,
% 7.55/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.55/1.49      | r2_hidden(X0,k5_xboole_0(X1,k2_xboole_0(X2,X1))) != iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_905,c_1290]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_29315,plain,
% 7.55/1.49      ( r2_hidden(X0,k5_xboole_0(sK3,sK3)) != iProver_top
% 7.55/1.49      | r2_hidden(X0,sK3) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_3020,c_29299]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_29354,plain,
% 7.55/1.49      ( r2_hidden(X0,sK3) != iProver_top
% 7.55/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_29315,c_16]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_0,plain,
% 7.55/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1) ),
% 7.55/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_445,plain,
% 7.55/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X1,X0))))) = k2_xboole_0(X0,X1) ),
% 7.55/1.49      inference(theory_normalisation,[status(thm)],[c_0,c_15,c_1]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1518,plain,
% 7.55/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_1290,c_445]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_7153,plain,
% 7.55/1.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1518,c_1290]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_14,plain,
% 7.55/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.55/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_899,plain,
% 7.55/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_7396,plain,
% 7.55/1.49      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_7153,c_899]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_12,plain,
% 7.55/1.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.55/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_900,plain,
% 7.55/1.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_18929,plain,
% 7.55/1.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_7396,c_900]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_7,plain,
% 7.55/1.49      ( r2_hidden(X0,X1)
% 7.55/1.49      | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))) ),
% 7.55/1.49      inference(cnf_transformation,[],[f104]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_439,plain,
% 7.55/1.49      ( r2_hidden(X0,X1)
% 7.55/1.49      | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))) ),
% 7.55/1.49      inference(theory_normalisation,[status(thm)],[c_7,c_15,c_1]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_904,plain,
% 7.55/1.49      ( r2_hidden(X0,X1) = iProver_top
% 7.55/1.49      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_25379,plain,
% 7.55/1.49      ( r2_hidden(X0,X1) = iProver_top
% 7.55/1.49      | r2_hidden(X0,k5_xboole_0(k2_xboole_0(X1,X2),X2)) != iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_904,c_2265]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_25415,plain,
% 7.55/1.49      ( r2_hidden(X0,X1) = iProver_top
% 7.55/1.49      | r2_hidden(X0,k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X2,X1))) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_18929,c_25379]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_25439,plain,
% 7.55/1.49      ( r2_hidden(X0,X1) = iProver_top
% 7.55/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_25415,c_16]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_23,plain,
% 7.55/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 7.55/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_22,plain,
% 7.55/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.55/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1414,plain,
% 7.55/1.49      ( k2_xboole_0(X0,X0) = X0 ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_23,c_22]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_29316,plain,
% 7.55/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.55/1.49      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1414,c_29299]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_29349,plain,
% 7.55/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.55/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_29316,c_16]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_32271,plain,
% 7.55/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.55/1.49      inference(global_propositional_subsumption,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_29354,c_25439,c_29349]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_32274,plain,
% 7.55/1.49      ( r2_hidden(sK2,k1_xboole_0) != iProver_top ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_32271]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_24,negated_conjecture,
% 7.55/1.49      ( ~ r2_hidden(sK2,sK3)
% 7.55/1.49      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) != k1_xboole_0 ),
% 7.55/1.49      inference(cnf_transformation,[],[f100]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_438,negated_conjecture,
% 7.55/1.49      ( ~ r2_hidden(sK2,sK3)
% 7.55/1.49      | k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0 ),
% 7.55/1.49      inference(theory_normalisation,[status(thm)],[c_24,c_15,c_1]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_893,plain,
% 7.55/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0
% 7.55/1.49      | r2_hidden(sK2,sK3) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1517,plain,
% 7.55/1.49      ( k5_xboole_0(sK3,k2_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_xboole_0
% 7.55/1.49      | r2_hidden(sK2,sK3) != iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_1290,c_893]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_3393,plain,
% 7.55/1.49      ( k5_xboole_0(sK3,sK3) != k1_xboole_0
% 7.55/1.49      | r2_hidden(sK2,sK3) != iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_3020,c_1517]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_3396,plain,
% 7.55/1.49      ( k1_xboole_0 != k1_xboole_0 | r2_hidden(sK2,sK3) != iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_3393,c_16]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_3397,plain,
% 7.55/1.49      ( r2_hidden(sK2,sK3) != iProver_top ),
% 7.55/1.49      inference(equality_resolution_simp,[status(thm)],[c_3396]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_19,plain,
% 7.55/1.49      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 7.55/1.49      inference(cnf_transformation,[],[f108]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_36,plain,
% 7.55/1.49      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_38,plain,
% 7.55/1.49      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_36]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(contradiction,plain,
% 7.55/1.49      ( $false ),
% 7.55/1.49      inference(minisat,[status(thm)],[c_33757,c_32274,c_3397,c_38]) ).
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.55/1.49  
% 7.55/1.49  ------                               Statistics
% 7.55/1.49  
% 7.55/1.49  ------ General
% 7.55/1.49  
% 7.55/1.49  abstr_ref_over_cycles:                  0
% 7.55/1.49  abstr_ref_under_cycles:                 0
% 7.55/1.49  gc_basic_clause_elim:                   0
% 7.55/1.49  forced_gc_time:                         0
% 7.55/1.49  parsing_time:                           0.009
% 7.55/1.49  unif_index_cands_time:                  0.
% 7.55/1.49  unif_index_add_time:                    0.
% 7.55/1.49  orderings_time:                         0.
% 7.55/1.49  out_proof_time:                         0.01
% 7.55/1.49  total_time:                             0.856
% 7.55/1.49  num_of_symbols:                         42
% 7.55/1.49  num_of_terms:                           40032
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing
% 7.55/1.49  
% 7.55/1.49  num_of_splits:                          0
% 7.55/1.49  num_of_split_atoms:                     0
% 7.55/1.49  num_of_reused_defs:                     0
% 7.55/1.49  num_eq_ax_congr_red:                    18
% 7.55/1.49  num_of_sem_filtered_clauses:            1
% 7.55/1.49  num_of_subtypes:                        0
% 7.55/1.49  monotx_restored_types:                  0
% 7.55/1.49  sat_num_of_epr_types:                   0
% 7.55/1.49  sat_num_of_non_cyclic_types:            0
% 7.55/1.49  sat_guarded_non_collapsed_types:        0
% 7.55/1.49  num_pure_diseq_elim:                    0
% 7.55/1.49  simp_replaced_by:                       0
% 7.55/1.49  res_preprocessed:                       117
% 7.55/1.49  prep_upred:                             0
% 7.55/1.49  prep_unflattend:                        0
% 7.55/1.49  smt_new_axioms:                         0
% 7.55/1.49  pred_elim_cands:                        2
% 7.55/1.49  pred_elim:                              0
% 7.55/1.49  pred_elim_cl:                           0
% 7.55/1.49  pred_elim_cycles:                       2
% 7.55/1.49  merged_defs:                            8
% 7.55/1.49  merged_defs_ncl:                        0
% 7.55/1.49  bin_hyper_res:                          8
% 7.55/1.49  prep_cycles:                            4
% 7.55/1.49  pred_elim_time:                         0.001
% 7.55/1.49  splitting_time:                         0.
% 7.55/1.49  sem_filter_time:                        0.
% 7.55/1.49  monotx_time:                            0.
% 7.55/1.49  subtype_inf_time:                       0.
% 7.55/1.49  
% 7.55/1.49  ------ Problem properties
% 7.55/1.49  
% 7.55/1.49  clauses:                                25
% 7.55/1.49  conjectures:                            2
% 7.55/1.49  epr:                                    2
% 7.55/1.49  horn:                                   19
% 7.55/1.49  ground:                                 2
% 7.55/1.49  unary:                                  10
% 7.55/1.49  binary:                                 8
% 7.55/1.49  lits:                                   48
% 7.55/1.49  lits_eq:                                20
% 7.55/1.49  fd_pure:                                0
% 7.55/1.49  fd_pseudo:                              0
% 7.55/1.49  fd_cond:                                0
% 7.55/1.49  fd_pseudo_cond:                         6
% 7.55/1.49  ac_symbols:                             1
% 7.55/1.49  
% 7.55/1.49  ------ Propositional Solver
% 7.55/1.49  
% 7.55/1.49  prop_solver_calls:                      29
% 7.55/1.49  prop_fast_solver_calls:                 689
% 7.55/1.49  smt_solver_calls:                       0
% 7.55/1.49  smt_fast_solver_calls:                  0
% 7.55/1.49  prop_num_of_clauses:                    7589
% 7.55/1.49  prop_preprocess_simplified:             17167
% 7.55/1.49  prop_fo_subsumed:                       7
% 7.55/1.49  prop_solver_time:                       0.
% 7.55/1.49  smt_solver_time:                        0.
% 7.55/1.49  smt_fast_solver_time:                   0.
% 7.55/1.49  prop_fast_solver_time:                  0.
% 7.55/1.49  prop_unsat_core_time:                   0.
% 7.55/1.49  
% 7.55/1.49  ------ QBF
% 7.55/1.49  
% 7.55/1.49  qbf_q_res:                              0
% 7.55/1.49  qbf_num_tautologies:                    0
% 7.55/1.49  qbf_prep_cycles:                        0
% 7.55/1.49  
% 7.55/1.49  ------ BMC1
% 7.55/1.49  
% 7.55/1.49  bmc1_current_bound:                     -1
% 7.55/1.49  bmc1_last_solved_bound:                 -1
% 7.55/1.49  bmc1_unsat_core_size:                   -1
% 7.55/1.49  bmc1_unsat_core_parents_size:           -1
% 7.55/1.49  bmc1_merge_next_fun:                    0
% 7.55/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.55/1.49  
% 7.55/1.49  ------ Instantiation
% 7.55/1.49  
% 7.55/1.49  inst_num_of_clauses:                    1983
% 7.55/1.49  inst_num_in_passive:                    595
% 7.55/1.49  inst_num_in_active:                     537
% 7.55/1.49  inst_num_in_unprocessed:                851
% 7.55/1.49  inst_num_of_loops:                      640
% 7.55/1.49  inst_num_of_learning_restarts:          0
% 7.55/1.49  inst_num_moves_active_passive:          101
% 7.55/1.49  inst_lit_activity:                      0
% 7.55/1.49  inst_lit_activity_moves:                0
% 7.55/1.49  inst_num_tautologies:                   0
% 7.55/1.49  inst_num_prop_implied:                  0
% 7.55/1.49  inst_num_existing_simplified:           0
% 7.55/1.49  inst_num_eq_res_simplified:             0
% 7.55/1.49  inst_num_child_elim:                    0
% 7.55/1.49  inst_num_of_dismatching_blockings:      2039
% 7.55/1.49  inst_num_of_non_proper_insts:           1857
% 7.55/1.49  inst_num_of_duplicates:                 0
% 7.55/1.49  inst_inst_num_from_inst_to_res:         0
% 7.55/1.49  inst_dismatching_checking_time:         0.
% 7.55/1.49  
% 7.55/1.49  ------ Resolution
% 7.55/1.49  
% 7.55/1.49  res_num_of_clauses:                     0
% 7.55/1.49  res_num_in_passive:                     0
% 7.55/1.49  res_num_in_active:                      0
% 7.55/1.49  res_num_of_loops:                       121
% 7.55/1.49  res_forward_subset_subsumed:            50
% 7.55/1.49  res_backward_subset_subsumed:           2
% 7.55/1.49  res_forward_subsumed:                   0
% 7.55/1.49  res_backward_subsumed:                  0
% 7.55/1.49  res_forward_subsumption_resolution:     0
% 7.55/1.49  res_backward_subsumption_resolution:    0
% 7.55/1.49  res_clause_to_clause_subsumption:       37477
% 7.55/1.49  res_orphan_elimination:                 0
% 7.55/1.49  res_tautology_del:                      558
% 7.55/1.49  res_num_eq_res_simplified:              0
% 7.55/1.49  res_num_sel_changes:                    0
% 7.55/1.49  res_moves_from_active_to_pass:          0
% 7.55/1.49  
% 7.55/1.49  ------ Superposition
% 7.55/1.49  
% 7.55/1.49  sup_time_total:                         0.
% 7.55/1.49  sup_time_generating:                    0.
% 7.55/1.49  sup_time_sim_full:                      0.
% 7.55/1.49  sup_time_sim_immed:                     0.
% 7.55/1.49  
% 7.55/1.49  sup_num_of_clauses:                     1551
% 7.55/1.49  sup_num_in_active:                      116
% 7.55/1.49  sup_num_in_passive:                     1435
% 7.55/1.49  sup_num_of_loops:                       127
% 7.55/1.49  sup_fw_superposition:                   4924
% 7.55/1.49  sup_bw_superposition:                   4697
% 7.55/1.49  sup_immediate_simplified:               2241
% 7.55/1.49  sup_given_eliminated:                   0
% 7.55/1.49  comparisons_done:                       0
% 7.55/1.49  comparisons_avoided:                    17
% 7.55/1.49  
% 7.55/1.49  ------ Simplifications
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  sim_fw_subset_subsumed:                 14
% 7.55/1.49  sim_bw_subset_subsumed:                 14
% 7.55/1.49  sim_fw_subsumed:                        351
% 7.55/1.49  sim_bw_subsumed:                        8
% 7.55/1.49  sim_fw_subsumption_res:                 1
% 7.55/1.49  sim_bw_subsumption_res:                 0
% 7.55/1.49  sim_tautology_del:                      9
% 7.55/1.49  sim_eq_tautology_del:                   435
% 7.55/1.49  sim_eq_res_simp:                        1
% 7.55/1.49  sim_fw_demodulated:                     853
% 7.55/1.49  sim_bw_demodulated:                     115
% 7.55/1.49  sim_light_normalised:                   846
% 7.55/1.49  sim_joinable_taut:                      168
% 7.55/1.49  sim_joinable_simp:                      0
% 7.55/1.49  sim_ac_normalised:                      0
% 7.55/1.49  sim_smt_subsumption:                    0
% 7.55/1.49  
%------------------------------------------------------------------------------
