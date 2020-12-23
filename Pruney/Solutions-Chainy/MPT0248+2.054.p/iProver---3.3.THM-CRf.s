%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:16 EST 2020

% Result     : Theorem 6.84s
% Output     : CNFRefutation 6.84s
% Verified   : 
% Statistics : Number of formulae       :  212 (28913 expanded)
%              Number of clauses        :  127 (4015 expanded)
%              Number of leaves         :   25 (8385 expanded)
%              Depth                    :   38
%              Number of atoms          :  474 (49222 expanded)
%              Number of equality atoms :  326 (37163 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f80])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f81])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f82])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f83])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f84])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f73,f86])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f47,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK5
        | k1_tarski(sK3) != sK4 )
      & ( k1_tarski(sK3) != sK5
        | k1_xboole_0 != sK4 )
      & ( k1_tarski(sK3) != sK5
        | k1_tarski(sK3) != sK4 )
      & k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( k1_xboole_0 != sK5
      | k1_tarski(sK3) != sK4 )
    & ( k1_tarski(sK3) != sK5
      | k1_xboole_0 != sK4 )
    & ( k1_tarski(sK3) != sK5
      | k1_tarski(sK3) != sK4 )
    & k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f35,f47])).

fof(f76,plain,(
    k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f85,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f75,f84])).

fof(f95,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f76,f85,f86])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f85])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f43])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f86,f86])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f65,f85])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,
    ( k1_tarski(sK3) != sK5
    | k1_tarski(sK3) != sK4 ),
    inference(cnf_transformation,[],[f48])).

fof(f94,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4 ),
    inference(definition_unfolding,[],[f77,f86,f86])).

fof(f78,plain,
    ( k1_tarski(sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f48])).

fof(f93,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(definition_unfolding,[],[f78,f86])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f85])).

fof(f79,plain,
    ( k1_xboole_0 != sK5
    | k1_tarski(sK3) != sK4 ),
    inference(cnf_transformation,[],[f48])).

fof(f92,plain,
    ( k1_xboole_0 != sK5
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4 ),
    inference(definition_unfolding,[],[f79,f86])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_963,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_968,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_22,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_967,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2560,plain,
    ( r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_967])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_965,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2604,plain,
    ( k3_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = X0
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2560,c_965])).

cnf(c_2708,plain,
    ( k3_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = sK5 ),
    inference(superposition,[status(thm)],[c_968,c_2604])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_975,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_971,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1800,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_971])).

cnf(c_1974,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X1,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_975,c_1800])).

cnf(c_9723,plain,
    ( r1_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2708,c_1974])).

cnf(c_10619,plain,
    ( r1_tarski(sK5,X0) = iProver_top
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_963,c_9723])).

cnf(c_11682,plain,
    ( k3_xboole_0(sK5,X0) = sK5
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_10619,c_965])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_962,plain,
    ( k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11724,plain,
    ( k3_xboole_0(sK5,X0) = sK5
    | k3_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_11682,c_962])).

cnf(c_11734,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
    | k3_xboole_0(sK5,X0) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_11724,c_2708])).

cnf(c_16222,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
    | k3_xboole_0(X0,sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_11734,c_0])).

cnf(c_16,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_964,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1481,plain,
    ( r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_964])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_974,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2505,plain,
    ( r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_974])).

cnf(c_17597,plain,
    ( k3_xboole_0(X0,sK5) = sK5
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_16222,c_2505])).

cnf(c_1546,plain,
    ( k3_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_1481,c_965])).

cnf(c_1980,plain,
    ( r1_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1546,c_1800])).

cnf(c_2430,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_963,c_1980])).

cnf(c_3192,plain,
    ( r1_tarski(sK4,X0) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_975,c_2430])).

cnf(c_3220,plain,
    ( k3_xboole_0(sK4,X0) = sK4
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3192,c_965])).

cnf(c_4048,plain,
    ( k3_xboole_0(sK4,X0) = sK4
    | k3_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_3220,c_962])).

cnf(c_4061,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
    | k3_xboole_0(sK4,X0) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_4048,c_1546])).

cnf(c_4728,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
    | k3_xboole_0(X0,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_4061,c_0])).

cnf(c_21,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_5960,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
    | k3_xboole_0(X0,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_4728,c_21])).

cnf(c_17576,plain,
    ( k3_xboole_0(X0,sK4) = sK4
    | k3_xboole_0(X1,sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_16222,c_5960])).

cnf(c_19305,plain,
    ( k3_xboole_0(X0,sK5) = sK5
    | r1_xboole_0(X1,sK4) != iProver_top
    | r2_hidden(X2,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_17576,c_971])).

cnf(c_20,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1182,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1401,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2228,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_547,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1132,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_2420,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1132])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_970,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1768,plain,
    ( r1_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(sK2(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1546,c_970])).

cnf(c_1168,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_968,c_965])).

cnf(c_1802,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1168,c_971])).

cnf(c_4552,plain,
    ( r1_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r1_xboole_0(sK4,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1768,c_1802])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_972,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9530,plain,
    ( k3_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0
    | r1_xboole_0(sK4,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4552,c_972])).

cnf(c_9544,plain,
    ( sK4 = k1_xboole_0
    | r1_xboole_0(sK4,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9530,c_1546])).

cnf(c_16414,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
    | k3_xboole_0(sK5,X0) = sK5
    | sK4 != sK5 ),
    inference(superposition,[status(thm)],[c_11734,c_21])).

cnf(c_16430,plain,
    ( k3_xboole_0(sK5,X0) = sK5
    | sK4 != sK5 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16414,c_11734])).

cnf(c_1303,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1306,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1303])).

cnf(c_1265,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1510,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_1511,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_550,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_1620,plain,
    ( ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,X1)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_2082,plain,
    ( r1_tarski(sK4,X0)
    | ~ r1_tarski(sK4,sK4)
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1620])).

cnf(c_2861,plain,
    ( ~ r1_tarski(sK4,sK4)
    | r1_tarski(sK4,sK5)
    | sK5 != sK4 ),
    inference(instantiation,[status(thm)],[c_2082])).

cnf(c_2862,plain,
    ( sK5 != sK4
    | r1_tarski(sK4,sK4) != iProver_top
    | r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2861])).

cnf(c_1271,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_1563,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_1874,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) != sK5
    | sK5 = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_9435,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) != sK5
    | sK5 = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1874])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1875,plain,
    ( ~ r1_tarski(X0,sK5)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_12119,plain,
    ( ~ r1_tarski(sK4,sK5)
    | k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_1875])).

cnf(c_12120,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12119])).

cnf(c_1156,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != X0
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_9395,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5))
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
    | sK5 != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) ),
    inference(instantiation,[status(thm)],[c_1156])).

cnf(c_12926,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
    | sK5 != k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_9395])).

cnf(c_1130,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != X0
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_13986,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_1130])).

cnf(c_14005,plain,
    ( sK4 != sK5
    | sK5 = sK4
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_17172,plain,
    ( sK4 != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16430,c_22,c_21,c_1306,c_1510,c_1511,c_2862,c_9435,c_12120,c_12926,c_13986,c_14005])).

cnf(c_1767,plain,
    ( r1_xboole_0(X0,X0) = iProver_top
    | r2_hidden(sK2(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1168,c_970])).

cnf(c_4318,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1767,c_971])).

cnf(c_19302,plain,
    ( k3_xboole_0(X0,sK5) = sK5
    | r1_xboole_0(X1,sK4) != iProver_top
    | r1_xboole_0(sK4,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_17576,c_4318])).

cnf(c_19283,plain,
    ( k3_xboole_0(X0,sK4) = sK4
    | r1_xboole_0(X1,sK5) != iProver_top
    | r2_hidden(X2,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_17576,c_971])).

cnf(c_19,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_5962,plain,
    ( k3_xboole_0(X0,sK4) = sK4
    | sK5 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4728,c_19])).

cnf(c_4549,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_970,c_1802])).

cnf(c_12981,plain,
    ( r1_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r1_xboole_0(sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2708,c_4549])).

cnf(c_13410,plain,
    ( k3_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0
    | r1_xboole_0(sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_12981,c_972])).

cnf(c_13425,plain,
    ( sK5 = k1_xboole_0
    | r1_xboole_0(sK5,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13410,c_2708])).

cnf(c_19280,plain,
    ( k3_xboole_0(X0,sK4) = sK4
    | r1_xboole_0(X1,sK5) != iProver_top
    | r1_xboole_0(sK5,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_17576,c_4318])).

cnf(c_23353,plain,
    ( r1_xboole_0(X1,sK5) != iProver_top
    | k3_xboole_0(X0,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19283,c_5962,c_13425,c_19280])).

cnf(c_23354,plain,
    ( k3_xboole_0(X0,sK4) = sK4
    | r1_xboole_0(X1,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_23353])).

cnf(c_23362,plain,
    ( k3_xboole_0(X0,sK4) = sK4
    | r2_hidden(X1,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_963,c_23354])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_976,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_23745,plain,
    ( k3_xboole_0(X0,sK4) = sK4
    | r1_tarski(X1,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_23362,c_976])).

cnf(c_23869,plain,
    ( k3_xboole_0(X0,sK4) = sK4
    | k3_xboole_0(X1,sK5) = X1 ),
    inference(superposition,[status(thm)],[c_23745,c_965])).

cnf(c_969,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2603,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = X0
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2560,c_969])).

cnf(c_23870,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
    | k3_xboole_0(X0,sK4) = sK4
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_23745,c_2603])).

cnf(c_23923,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
    | k3_xboole_0(X0,sK4) = sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_23870,c_23745])).

cnf(c_23955,plain,
    ( k3_xboole_0(X0,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23869,c_5960,c_23923])).

cnf(c_23996,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
    | sK4 = sK5 ),
    inference(superposition,[status(thm)],[c_23955,c_11734])).

cnf(c_24426,plain,
    ( r1_xboole_0(X1,sK4) != iProver_top
    | k3_xboole_0(X0,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19305,c_22,c_21,c_20,c_1182,c_1306,c_1510,c_1511,c_2228,c_2420,c_2862,c_9435,c_9544,c_12120,c_12926,c_13986,c_14005,c_19302,c_23996])).

cnf(c_24427,plain,
    ( k3_xboole_0(X0,sK5) = sK5
    | r1_xboole_0(X1,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_24426])).

cnf(c_24435,plain,
    ( k3_xboole_0(X0,sK5) = sK5
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_963,c_24427])).

cnf(c_25793,plain,
    ( k3_xboole_0(X0,sK5) = sK5
    | r2_hidden(X1,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17597,c_24435])).

cnf(c_25799,plain,
    ( k3_xboole_0(X0,sK5) = sK5
    | r1_tarski(X1,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_25793,c_976])).

cnf(c_24893,plain,
    ( k3_xboole_0(X0,sK5) = sK5
    | r1_tarski(X1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_24435,c_976])).

cnf(c_2447,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
    | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_969])).

cnf(c_26178,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
    | k3_xboole_0(X0,sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_24893,c_2447])).

cnf(c_26219,plain,
    ( k3_xboole_0(X0,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25799,c_22,c_21,c_1306,c_1510,c_1511,c_2862,c_9435,c_12120,c_12926,c_13986,c_14005,c_23996,c_26178])).

cnf(c_23994,plain,
    ( k3_xboole_0(sK4,X0) = sK4 ),
    inference(superposition,[status(thm)],[c_23955,c_0])).

cnf(c_26246,plain,
    ( sK4 = sK5 ),
    inference(superposition,[status(thm)],[c_26219,c_23994])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26246,c_17172])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:13:32 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 6.84/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.84/1.47  
% 6.84/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.84/1.47  
% 6.84/1.47  ------  iProver source info
% 6.84/1.47  
% 6.84/1.47  git: date: 2020-06-30 10:37:57 +0100
% 6.84/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.84/1.47  git: non_committed_changes: false
% 6.84/1.47  git: last_make_outside_of_git: false
% 6.84/1.47  
% 6.84/1.47  ------ 
% 6.84/1.47  
% 6.84/1.47  ------ Input Options
% 6.84/1.47  
% 6.84/1.47  --out_options                           all
% 6.84/1.47  --tptp_safe_out                         true
% 6.84/1.47  --problem_path                          ""
% 6.84/1.47  --include_path                          ""
% 6.84/1.47  --clausifier                            res/vclausify_rel
% 6.84/1.47  --clausifier_options                    --mode clausify
% 6.84/1.47  --stdin                                 false
% 6.84/1.47  --stats_out                             all
% 6.84/1.47  
% 6.84/1.47  ------ General Options
% 6.84/1.47  
% 6.84/1.47  --fof                                   false
% 6.84/1.47  --time_out_real                         305.
% 6.84/1.47  --time_out_virtual                      -1.
% 6.84/1.47  --symbol_type_check                     false
% 6.84/1.47  --clausify_out                          false
% 6.84/1.47  --sig_cnt_out                           false
% 6.84/1.47  --trig_cnt_out                          false
% 6.84/1.47  --trig_cnt_out_tolerance                1.
% 6.84/1.47  --trig_cnt_out_sk_spl                   false
% 6.84/1.47  --abstr_cl_out                          false
% 6.84/1.47  
% 6.84/1.47  ------ Global Options
% 6.84/1.47  
% 6.84/1.47  --schedule                              default
% 6.84/1.47  --add_important_lit                     false
% 6.84/1.47  --prop_solver_per_cl                    1000
% 6.84/1.47  --min_unsat_core                        false
% 6.84/1.47  --soft_assumptions                      false
% 6.84/1.47  --soft_lemma_size                       3
% 6.84/1.47  --prop_impl_unit_size                   0
% 6.84/1.47  --prop_impl_unit                        []
% 6.84/1.47  --share_sel_clauses                     true
% 6.84/1.47  --reset_solvers                         false
% 6.84/1.47  --bc_imp_inh                            [conj_cone]
% 6.84/1.47  --conj_cone_tolerance                   3.
% 6.84/1.47  --extra_neg_conj                        none
% 6.84/1.47  --large_theory_mode                     true
% 6.84/1.47  --prolific_symb_bound                   200
% 6.84/1.47  --lt_threshold                          2000
% 6.84/1.47  --clause_weak_htbl                      true
% 6.84/1.47  --gc_record_bc_elim                     false
% 6.84/1.47  
% 6.84/1.47  ------ Preprocessing Options
% 6.84/1.47  
% 6.84/1.47  --preprocessing_flag                    true
% 6.84/1.47  --time_out_prep_mult                    0.1
% 6.84/1.47  --splitting_mode                        input
% 6.84/1.47  --splitting_grd                         true
% 6.84/1.47  --splitting_cvd                         false
% 6.84/1.47  --splitting_cvd_svl                     false
% 6.84/1.47  --splitting_nvd                         32
% 6.84/1.47  --sub_typing                            true
% 6.84/1.47  --prep_gs_sim                           true
% 6.84/1.47  --prep_unflatten                        true
% 6.84/1.47  --prep_res_sim                          true
% 6.84/1.47  --prep_upred                            true
% 6.84/1.47  --prep_sem_filter                       exhaustive
% 6.84/1.47  --prep_sem_filter_out                   false
% 6.84/1.47  --pred_elim                             true
% 6.84/1.47  --res_sim_input                         true
% 6.84/1.47  --eq_ax_congr_red                       true
% 6.84/1.47  --pure_diseq_elim                       true
% 6.84/1.47  --brand_transform                       false
% 6.84/1.47  --non_eq_to_eq                          false
% 6.84/1.47  --prep_def_merge                        true
% 6.84/1.47  --prep_def_merge_prop_impl              false
% 6.84/1.47  --prep_def_merge_mbd                    true
% 6.84/1.47  --prep_def_merge_tr_red                 false
% 6.84/1.47  --prep_def_merge_tr_cl                  false
% 6.84/1.47  --smt_preprocessing                     true
% 6.84/1.47  --smt_ac_axioms                         fast
% 6.84/1.47  --preprocessed_out                      false
% 6.84/1.47  --preprocessed_stats                    false
% 6.84/1.47  
% 6.84/1.47  ------ Abstraction refinement Options
% 6.84/1.47  
% 6.84/1.47  --abstr_ref                             []
% 6.84/1.47  --abstr_ref_prep                        false
% 6.84/1.47  --abstr_ref_until_sat                   false
% 6.84/1.47  --abstr_ref_sig_restrict                funpre
% 6.84/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 6.84/1.47  --abstr_ref_under                       []
% 6.84/1.47  
% 6.84/1.47  ------ SAT Options
% 6.84/1.47  
% 6.84/1.47  --sat_mode                              false
% 6.84/1.47  --sat_fm_restart_options                ""
% 6.84/1.47  --sat_gr_def                            false
% 6.84/1.47  --sat_epr_types                         true
% 6.84/1.47  --sat_non_cyclic_types                  false
% 6.84/1.47  --sat_finite_models                     false
% 6.84/1.47  --sat_fm_lemmas                         false
% 6.84/1.47  --sat_fm_prep                           false
% 6.84/1.47  --sat_fm_uc_incr                        true
% 6.84/1.47  --sat_out_model                         small
% 6.84/1.47  --sat_out_clauses                       false
% 6.84/1.47  
% 6.84/1.47  ------ QBF Options
% 6.84/1.47  
% 6.84/1.47  --qbf_mode                              false
% 6.84/1.47  --qbf_elim_univ                         false
% 6.84/1.47  --qbf_dom_inst                          none
% 6.84/1.47  --qbf_dom_pre_inst                      false
% 6.84/1.47  --qbf_sk_in                             false
% 6.84/1.47  --qbf_pred_elim                         true
% 6.84/1.47  --qbf_split                             512
% 6.84/1.47  
% 6.84/1.47  ------ BMC1 Options
% 6.84/1.47  
% 6.84/1.47  --bmc1_incremental                      false
% 6.84/1.47  --bmc1_axioms                           reachable_all
% 6.84/1.47  --bmc1_min_bound                        0
% 6.84/1.47  --bmc1_max_bound                        -1
% 6.84/1.47  --bmc1_max_bound_default                -1
% 6.84/1.47  --bmc1_symbol_reachability              true
% 6.84/1.47  --bmc1_property_lemmas                  false
% 6.84/1.47  --bmc1_k_induction                      false
% 6.84/1.47  --bmc1_non_equiv_states                 false
% 6.84/1.47  --bmc1_deadlock                         false
% 6.84/1.47  --bmc1_ucm                              false
% 6.84/1.47  --bmc1_add_unsat_core                   none
% 6.84/1.47  --bmc1_unsat_core_children              false
% 6.84/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 6.84/1.47  --bmc1_out_stat                         full
% 6.84/1.47  --bmc1_ground_init                      false
% 6.84/1.47  --bmc1_pre_inst_next_state              false
% 6.84/1.47  --bmc1_pre_inst_state                   false
% 6.84/1.47  --bmc1_pre_inst_reach_state             false
% 6.84/1.47  --bmc1_out_unsat_core                   false
% 6.84/1.47  --bmc1_aig_witness_out                  false
% 6.84/1.47  --bmc1_verbose                          false
% 6.84/1.47  --bmc1_dump_clauses_tptp                false
% 6.84/1.47  --bmc1_dump_unsat_core_tptp             false
% 6.84/1.47  --bmc1_dump_file                        -
% 6.84/1.47  --bmc1_ucm_expand_uc_limit              128
% 6.84/1.47  --bmc1_ucm_n_expand_iterations          6
% 6.84/1.47  --bmc1_ucm_extend_mode                  1
% 6.84/1.47  --bmc1_ucm_init_mode                    2
% 6.84/1.47  --bmc1_ucm_cone_mode                    none
% 6.84/1.47  --bmc1_ucm_reduced_relation_type        0
% 6.84/1.47  --bmc1_ucm_relax_model                  4
% 6.84/1.47  --bmc1_ucm_full_tr_after_sat            true
% 6.84/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 6.84/1.47  --bmc1_ucm_layered_model                none
% 6.84/1.47  --bmc1_ucm_max_lemma_size               10
% 6.84/1.47  
% 6.84/1.47  ------ AIG Options
% 6.84/1.47  
% 6.84/1.47  --aig_mode                              false
% 6.84/1.47  
% 6.84/1.47  ------ Instantiation Options
% 6.84/1.47  
% 6.84/1.47  --instantiation_flag                    true
% 6.84/1.47  --inst_sos_flag                         false
% 6.84/1.47  --inst_sos_phase                        true
% 6.84/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.84/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.84/1.47  --inst_lit_sel_side                     num_symb
% 6.84/1.47  --inst_solver_per_active                1400
% 6.84/1.47  --inst_solver_calls_frac                1.
% 6.84/1.47  --inst_passive_queue_type               priority_queues
% 6.84/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.84/1.47  --inst_passive_queues_freq              [25;2]
% 6.84/1.47  --inst_dismatching                      true
% 6.84/1.47  --inst_eager_unprocessed_to_passive     true
% 6.84/1.47  --inst_prop_sim_given                   true
% 6.84/1.47  --inst_prop_sim_new                     false
% 6.84/1.47  --inst_subs_new                         false
% 6.84/1.47  --inst_eq_res_simp                      false
% 6.84/1.47  --inst_subs_given                       false
% 6.84/1.47  --inst_orphan_elimination               true
% 6.84/1.47  --inst_learning_loop_flag               true
% 6.84/1.47  --inst_learning_start                   3000
% 6.84/1.47  --inst_learning_factor                  2
% 6.84/1.47  --inst_start_prop_sim_after_learn       3
% 6.84/1.47  --inst_sel_renew                        solver
% 6.84/1.47  --inst_lit_activity_flag                true
% 6.84/1.47  --inst_restr_to_given                   false
% 6.84/1.47  --inst_activity_threshold               500
% 6.84/1.47  --inst_out_proof                        true
% 6.84/1.47  
% 6.84/1.47  ------ Resolution Options
% 6.84/1.47  
% 6.84/1.47  --resolution_flag                       true
% 6.84/1.47  --res_lit_sel                           adaptive
% 6.84/1.47  --res_lit_sel_side                      none
% 6.84/1.47  --res_ordering                          kbo
% 6.84/1.47  --res_to_prop_solver                    active
% 6.84/1.47  --res_prop_simpl_new                    false
% 6.84/1.47  --res_prop_simpl_given                  true
% 6.84/1.47  --res_passive_queue_type                priority_queues
% 6.84/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.84/1.47  --res_passive_queues_freq               [15;5]
% 6.84/1.47  --res_forward_subs                      full
% 6.84/1.47  --res_backward_subs                     full
% 6.84/1.47  --res_forward_subs_resolution           true
% 6.84/1.47  --res_backward_subs_resolution          true
% 6.84/1.47  --res_orphan_elimination                true
% 6.84/1.47  --res_time_limit                        2.
% 6.84/1.47  --res_out_proof                         true
% 6.84/1.47  
% 6.84/1.47  ------ Superposition Options
% 6.84/1.47  
% 6.84/1.47  --superposition_flag                    true
% 6.84/1.47  --sup_passive_queue_type                priority_queues
% 6.84/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.84/1.47  --sup_passive_queues_freq               [8;1;4]
% 6.84/1.47  --demod_completeness_check              fast
% 6.84/1.47  --demod_use_ground                      true
% 6.84/1.47  --sup_to_prop_solver                    passive
% 6.84/1.47  --sup_prop_simpl_new                    true
% 6.84/1.47  --sup_prop_simpl_given                  true
% 6.84/1.47  --sup_fun_splitting                     false
% 6.84/1.47  --sup_smt_interval                      50000
% 6.84/1.47  
% 6.84/1.47  ------ Superposition Simplification Setup
% 6.84/1.47  
% 6.84/1.47  --sup_indices_passive                   []
% 6.84/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 6.84/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.47  --sup_full_bw                           [BwDemod]
% 6.84/1.47  --sup_immed_triv                        [TrivRules]
% 6.84/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.84/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.47  --sup_immed_bw_main                     []
% 6.84/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.84/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 6.84/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.84/1.48  
% 6.84/1.48  ------ Combination Options
% 6.84/1.48  
% 6.84/1.48  --comb_res_mult                         3
% 6.84/1.48  --comb_sup_mult                         2
% 6.84/1.48  --comb_inst_mult                        10
% 6.84/1.48  
% 6.84/1.48  ------ Debug Options
% 6.84/1.48  
% 6.84/1.48  --dbg_backtrace                         false
% 6.84/1.48  --dbg_dump_prop_clauses                 false
% 6.84/1.48  --dbg_dump_prop_clauses_file            -
% 6.84/1.48  --dbg_out_stat                          false
% 6.84/1.48  ------ Parsing...
% 6.84/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.84/1.48  
% 6.84/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.84/1.48  
% 6.84/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.84/1.48  
% 6.84/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.84/1.48  ------ Proving...
% 6.84/1.48  ------ Problem Properties 
% 6.84/1.48  
% 6.84/1.48  
% 6.84/1.48  clauses                                 21
% 6.84/1.48  conjectures                             4
% 6.84/1.48  EPR                                     3
% 6.84/1.48  Horn                                    17
% 6.84/1.48  unary                                   4
% 6.84/1.48  binary                                  15
% 6.84/1.48  lits                                    40
% 6.84/1.48  lits eq                                 15
% 6.84/1.48  fd_pure                                 0
% 6.84/1.48  fd_pseudo                               0
% 6.84/1.48  fd_cond                                 1
% 6.84/1.48  fd_pseudo_cond                          1
% 6.84/1.48  AC symbols                              0
% 6.84/1.48  
% 6.84/1.48  ------ Schedule dynamic 5 is on 
% 6.84/1.48  
% 6.84/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.84/1.48  
% 6.84/1.48  
% 6.84/1.48  ------ 
% 6.84/1.48  Current options:
% 6.84/1.48  ------ 
% 6.84/1.48  
% 6.84/1.48  ------ Input Options
% 6.84/1.48  
% 6.84/1.48  --out_options                           all
% 6.84/1.48  --tptp_safe_out                         true
% 6.84/1.48  --problem_path                          ""
% 6.84/1.48  --include_path                          ""
% 6.84/1.48  --clausifier                            res/vclausify_rel
% 6.84/1.48  --clausifier_options                    --mode clausify
% 6.84/1.48  --stdin                                 false
% 6.84/1.48  --stats_out                             all
% 6.84/1.48  
% 6.84/1.48  ------ General Options
% 6.84/1.48  
% 6.84/1.48  --fof                                   false
% 6.84/1.48  --time_out_real                         305.
% 6.84/1.48  --time_out_virtual                      -1.
% 6.84/1.48  --symbol_type_check                     false
% 6.84/1.48  --clausify_out                          false
% 6.84/1.48  --sig_cnt_out                           false
% 6.84/1.48  --trig_cnt_out                          false
% 6.84/1.48  --trig_cnt_out_tolerance                1.
% 6.84/1.48  --trig_cnt_out_sk_spl                   false
% 6.84/1.48  --abstr_cl_out                          false
% 6.84/1.48  
% 6.84/1.48  ------ Global Options
% 6.84/1.48  
% 6.84/1.48  --schedule                              default
% 6.84/1.48  --add_important_lit                     false
% 6.84/1.48  --prop_solver_per_cl                    1000
% 6.84/1.48  --min_unsat_core                        false
% 6.84/1.48  --soft_assumptions                      false
% 6.84/1.48  --soft_lemma_size                       3
% 6.84/1.48  --prop_impl_unit_size                   0
% 6.84/1.48  --prop_impl_unit                        []
% 6.84/1.48  --share_sel_clauses                     true
% 6.84/1.48  --reset_solvers                         false
% 6.84/1.48  --bc_imp_inh                            [conj_cone]
% 6.84/1.48  --conj_cone_tolerance                   3.
% 6.84/1.48  --extra_neg_conj                        none
% 6.84/1.48  --large_theory_mode                     true
% 6.84/1.48  --prolific_symb_bound                   200
% 6.84/1.48  --lt_threshold                          2000
% 6.84/1.48  --clause_weak_htbl                      true
% 6.84/1.48  --gc_record_bc_elim                     false
% 6.84/1.48  
% 6.84/1.48  ------ Preprocessing Options
% 6.84/1.48  
% 6.84/1.48  --preprocessing_flag                    true
% 6.84/1.48  --time_out_prep_mult                    0.1
% 6.84/1.48  --splitting_mode                        input
% 6.84/1.48  --splitting_grd                         true
% 6.84/1.48  --splitting_cvd                         false
% 6.84/1.48  --splitting_cvd_svl                     false
% 6.84/1.48  --splitting_nvd                         32
% 6.84/1.48  --sub_typing                            true
% 6.84/1.48  --prep_gs_sim                           true
% 6.84/1.48  --prep_unflatten                        true
% 6.84/1.48  --prep_res_sim                          true
% 6.84/1.48  --prep_upred                            true
% 6.84/1.48  --prep_sem_filter                       exhaustive
% 6.84/1.48  --prep_sem_filter_out                   false
% 6.84/1.48  --pred_elim                             true
% 6.84/1.48  --res_sim_input                         true
% 6.84/1.48  --eq_ax_congr_red                       true
% 6.84/1.48  --pure_diseq_elim                       true
% 6.84/1.48  --brand_transform                       false
% 6.84/1.48  --non_eq_to_eq                          false
% 6.84/1.48  --prep_def_merge                        true
% 6.84/1.48  --prep_def_merge_prop_impl              false
% 6.84/1.48  --prep_def_merge_mbd                    true
% 6.84/1.48  --prep_def_merge_tr_red                 false
% 6.84/1.48  --prep_def_merge_tr_cl                  false
% 6.84/1.48  --smt_preprocessing                     true
% 6.84/1.48  --smt_ac_axioms                         fast
% 6.84/1.48  --preprocessed_out                      false
% 6.84/1.48  --preprocessed_stats                    false
% 6.84/1.48  
% 6.84/1.48  ------ Abstraction refinement Options
% 6.84/1.48  
% 6.84/1.48  --abstr_ref                             []
% 6.84/1.48  --abstr_ref_prep                        false
% 6.84/1.48  --abstr_ref_until_sat                   false
% 6.84/1.48  --abstr_ref_sig_restrict                funpre
% 6.84/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.84/1.48  --abstr_ref_under                       []
% 6.84/1.48  
% 6.84/1.48  ------ SAT Options
% 6.84/1.48  
% 6.84/1.48  --sat_mode                              false
% 6.84/1.48  --sat_fm_restart_options                ""
% 6.84/1.48  --sat_gr_def                            false
% 6.84/1.48  --sat_epr_types                         true
% 6.84/1.48  --sat_non_cyclic_types                  false
% 6.84/1.48  --sat_finite_models                     false
% 6.84/1.48  --sat_fm_lemmas                         false
% 6.84/1.48  --sat_fm_prep                           false
% 6.84/1.48  --sat_fm_uc_incr                        true
% 6.84/1.48  --sat_out_model                         small
% 6.84/1.48  --sat_out_clauses                       false
% 6.84/1.48  
% 6.84/1.48  ------ QBF Options
% 6.84/1.48  
% 6.84/1.48  --qbf_mode                              false
% 6.84/1.48  --qbf_elim_univ                         false
% 6.84/1.48  --qbf_dom_inst                          none
% 6.84/1.48  --qbf_dom_pre_inst                      false
% 6.84/1.48  --qbf_sk_in                             false
% 6.84/1.48  --qbf_pred_elim                         true
% 6.84/1.48  --qbf_split                             512
% 6.84/1.48  
% 6.84/1.48  ------ BMC1 Options
% 6.84/1.48  
% 6.84/1.48  --bmc1_incremental                      false
% 6.84/1.48  --bmc1_axioms                           reachable_all
% 6.84/1.48  --bmc1_min_bound                        0
% 6.84/1.48  --bmc1_max_bound                        -1
% 6.84/1.48  --bmc1_max_bound_default                -1
% 6.84/1.48  --bmc1_symbol_reachability              true
% 6.84/1.48  --bmc1_property_lemmas                  false
% 6.84/1.48  --bmc1_k_induction                      false
% 6.84/1.48  --bmc1_non_equiv_states                 false
% 6.84/1.48  --bmc1_deadlock                         false
% 6.84/1.48  --bmc1_ucm                              false
% 6.84/1.48  --bmc1_add_unsat_core                   none
% 6.84/1.48  --bmc1_unsat_core_children              false
% 6.84/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.84/1.48  --bmc1_out_stat                         full
% 6.84/1.48  --bmc1_ground_init                      false
% 6.84/1.48  --bmc1_pre_inst_next_state              false
% 6.84/1.48  --bmc1_pre_inst_state                   false
% 6.84/1.48  --bmc1_pre_inst_reach_state             false
% 6.84/1.48  --bmc1_out_unsat_core                   false
% 6.84/1.48  --bmc1_aig_witness_out                  false
% 6.84/1.48  --bmc1_verbose                          false
% 6.84/1.48  --bmc1_dump_clauses_tptp                false
% 6.84/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.84/1.48  --bmc1_dump_file                        -
% 6.84/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.84/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.84/1.48  --bmc1_ucm_extend_mode                  1
% 6.84/1.48  --bmc1_ucm_init_mode                    2
% 6.84/1.48  --bmc1_ucm_cone_mode                    none
% 6.84/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.84/1.48  --bmc1_ucm_relax_model                  4
% 6.84/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.84/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.84/1.48  --bmc1_ucm_layered_model                none
% 6.84/1.48  --bmc1_ucm_max_lemma_size               10
% 6.84/1.48  
% 6.84/1.48  ------ AIG Options
% 6.84/1.48  
% 6.84/1.48  --aig_mode                              false
% 6.84/1.48  
% 6.84/1.48  ------ Instantiation Options
% 6.84/1.48  
% 6.84/1.48  --instantiation_flag                    true
% 6.84/1.48  --inst_sos_flag                         false
% 6.84/1.48  --inst_sos_phase                        true
% 6.84/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.84/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.84/1.48  --inst_lit_sel_side                     none
% 6.84/1.48  --inst_solver_per_active                1400
% 6.84/1.48  --inst_solver_calls_frac                1.
% 6.84/1.48  --inst_passive_queue_type               priority_queues
% 6.84/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.84/1.48  --inst_passive_queues_freq              [25;2]
% 6.84/1.48  --inst_dismatching                      true
% 6.84/1.48  --inst_eager_unprocessed_to_passive     true
% 6.84/1.48  --inst_prop_sim_given                   true
% 6.84/1.48  --inst_prop_sim_new                     false
% 6.84/1.48  --inst_subs_new                         false
% 6.84/1.48  --inst_eq_res_simp                      false
% 6.84/1.48  --inst_subs_given                       false
% 6.84/1.48  --inst_orphan_elimination               true
% 6.84/1.48  --inst_learning_loop_flag               true
% 6.84/1.48  --inst_learning_start                   3000
% 6.84/1.48  --inst_learning_factor                  2
% 6.84/1.48  --inst_start_prop_sim_after_learn       3
% 6.84/1.48  --inst_sel_renew                        solver
% 6.84/1.48  --inst_lit_activity_flag                true
% 6.84/1.48  --inst_restr_to_given                   false
% 6.84/1.48  --inst_activity_threshold               500
% 6.84/1.48  --inst_out_proof                        true
% 6.84/1.48  
% 6.84/1.48  ------ Resolution Options
% 6.84/1.48  
% 6.84/1.48  --resolution_flag                       false
% 6.84/1.48  --res_lit_sel                           adaptive
% 6.84/1.48  --res_lit_sel_side                      none
% 6.84/1.48  --res_ordering                          kbo
% 6.84/1.48  --res_to_prop_solver                    active
% 6.84/1.48  --res_prop_simpl_new                    false
% 6.84/1.48  --res_prop_simpl_given                  true
% 6.84/1.48  --res_passive_queue_type                priority_queues
% 6.84/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.84/1.48  --res_passive_queues_freq               [15;5]
% 6.84/1.48  --res_forward_subs                      full
% 6.84/1.48  --res_backward_subs                     full
% 6.84/1.48  --res_forward_subs_resolution           true
% 6.84/1.48  --res_backward_subs_resolution          true
% 6.84/1.48  --res_orphan_elimination                true
% 6.84/1.48  --res_time_limit                        2.
% 6.84/1.48  --res_out_proof                         true
% 6.84/1.48  
% 6.84/1.48  ------ Superposition Options
% 6.84/1.48  
% 6.84/1.48  --superposition_flag                    true
% 6.84/1.48  --sup_passive_queue_type                priority_queues
% 6.84/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.84/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.84/1.48  --demod_completeness_check              fast
% 6.84/1.48  --demod_use_ground                      true
% 6.84/1.48  --sup_to_prop_solver                    passive
% 6.84/1.48  --sup_prop_simpl_new                    true
% 6.84/1.48  --sup_prop_simpl_given                  true
% 6.84/1.48  --sup_fun_splitting                     false
% 6.84/1.48  --sup_smt_interval                      50000
% 6.84/1.48  
% 6.84/1.48  ------ Superposition Simplification Setup
% 6.84/1.48  
% 6.84/1.48  --sup_indices_passive                   []
% 6.84/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.84/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.48  --sup_full_bw                           [BwDemod]
% 6.84/1.48  --sup_immed_triv                        [TrivRules]
% 6.84/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.84/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.48  --sup_immed_bw_main                     []
% 6.84/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.84/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.84/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.84/1.48  
% 6.84/1.48  ------ Combination Options
% 6.84/1.48  
% 6.84/1.48  --comb_res_mult                         3
% 6.84/1.48  --comb_sup_mult                         2
% 6.84/1.48  --comb_inst_mult                        10
% 6.84/1.48  
% 6.84/1.48  ------ Debug Options
% 6.84/1.48  
% 6.84/1.48  --dbg_backtrace                         false
% 6.84/1.48  --dbg_dump_prop_clauses                 false
% 6.84/1.48  --dbg_dump_prop_clauses_file            -
% 6.84/1.48  --dbg_out_stat                          false
% 6.84/1.48  
% 6.84/1.48  
% 6.84/1.48  
% 6.84/1.48  
% 6.84/1.48  ------ Proving...
% 6.84/1.48  
% 6.84/1.48  
% 6.84/1.48  % SZS status Theorem for theBenchmark.p
% 6.84/1.48  
% 6.84/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 6.84/1.48  
% 6.84/1.48  fof(f19,axiom,(
% 6.84/1.48    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f33,plain,(
% 6.84/1.48    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 6.84/1.48    inference(ennf_transformation,[],[f19])).
% 6.84/1.48  
% 6.84/1.48  fof(f73,plain,(
% 6.84/1.48    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f33])).
% 6.84/1.48  
% 6.84/1.48  fof(f12,axiom,(
% 6.84/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f66,plain,(
% 6.84/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f12])).
% 6.84/1.48  
% 6.84/1.48  fof(f13,axiom,(
% 6.84/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f67,plain,(
% 6.84/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f13])).
% 6.84/1.48  
% 6.84/1.48  fof(f14,axiom,(
% 6.84/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f68,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f14])).
% 6.84/1.48  
% 6.84/1.48  fof(f15,axiom,(
% 6.84/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f69,plain,(
% 6.84/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f15])).
% 6.84/1.48  
% 6.84/1.48  fof(f16,axiom,(
% 6.84/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f70,plain,(
% 6.84/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f16])).
% 6.84/1.48  
% 6.84/1.48  fof(f17,axiom,(
% 6.84/1.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f71,plain,(
% 6.84/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f17])).
% 6.84/1.48  
% 6.84/1.48  fof(f18,axiom,(
% 6.84/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f72,plain,(
% 6.84/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f18])).
% 6.84/1.48  
% 6.84/1.48  fof(f80,plain,(
% 6.84/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 6.84/1.48    inference(definition_unfolding,[],[f71,f72])).
% 6.84/1.48  
% 6.84/1.48  fof(f81,plain,(
% 6.84/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 6.84/1.48    inference(definition_unfolding,[],[f70,f80])).
% 6.84/1.48  
% 6.84/1.48  fof(f82,plain,(
% 6.84/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 6.84/1.48    inference(definition_unfolding,[],[f69,f81])).
% 6.84/1.48  
% 6.84/1.48  fof(f83,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 6.84/1.48    inference(definition_unfolding,[],[f68,f82])).
% 6.84/1.48  
% 6.84/1.48  fof(f84,plain,(
% 6.84/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 6.84/1.48    inference(definition_unfolding,[],[f67,f83])).
% 6.84/1.48  
% 6.84/1.48  fof(f86,plain,(
% 6.84/1.48    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 6.84/1.48    inference(definition_unfolding,[],[f66,f84])).
% 6.84/1.48  
% 6.84/1.48  fof(f90,plain,(
% 6.84/1.48    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 6.84/1.48    inference(definition_unfolding,[],[f73,f86])).
% 6.84/1.48  
% 6.84/1.48  fof(f7,axiom,(
% 6.84/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f45,plain,(
% 6.84/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.84/1.48    inference(nnf_transformation,[],[f7])).
% 6.84/1.48  
% 6.84/1.48  fof(f46,plain,(
% 6.84/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.84/1.48    inference(flattening,[],[f45])).
% 6.84/1.48  
% 6.84/1.48  fof(f59,plain,(
% 6.84/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.84/1.48    inference(cnf_transformation,[],[f46])).
% 6.84/1.48  
% 6.84/1.48  fof(f97,plain,(
% 6.84/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.84/1.48    inference(equality_resolution,[],[f59])).
% 6.84/1.48  
% 6.84/1.48  fof(f22,conjecture,(
% 6.84/1.48    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f23,negated_conjecture,(
% 6.84/1.48    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 6.84/1.48    inference(negated_conjecture,[],[f22])).
% 6.84/1.48  
% 6.84/1.48  fof(f35,plain,(
% 6.84/1.48    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 6.84/1.48    inference(ennf_transformation,[],[f23])).
% 6.84/1.48  
% 6.84/1.48  fof(f47,plain,(
% 6.84/1.48    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4) & (k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4) & (k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4) & k2_xboole_0(sK4,sK5) = k1_tarski(sK3))),
% 6.84/1.48    introduced(choice_axiom,[])).
% 6.84/1.48  
% 6.84/1.48  fof(f48,plain,(
% 6.84/1.48    (k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4) & (k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4) & (k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4) & k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 6.84/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f35,f47])).
% 6.84/1.48  
% 6.84/1.48  fof(f76,plain,(
% 6.84/1.48    k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 6.84/1.48    inference(cnf_transformation,[],[f48])).
% 6.84/1.48  
% 6.84/1.48  fof(f21,axiom,(
% 6.84/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f75,plain,(
% 6.84/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 6.84/1.48    inference(cnf_transformation,[],[f21])).
% 6.84/1.48  
% 6.84/1.48  fof(f85,plain,(
% 6.84/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 6.84/1.48    inference(definition_unfolding,[],[f75,f84])).
% 6.84/1.48  
% 6.84/1.48  fof(f95,plain,(
% 6.84/1.48    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),
% 6.84/1.48    inference(definition_unfolding,[],[f76,f85,f86])).
% 6.84/1.48  
% 6.84/1.48  fof(f8,axiom,(
% 6.84/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f30,plain,(
% 6.84/1.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 6.84/1.48    inference(ennf_transformation,[],[f8])).
% 6.84/1.48  
% 6.84/1.48  fof(f62,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f30])).
% 6.84/1.48  
% 6.84/1.48  fof(f87,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 6.84/1.48    inference(definition_unfolding,[],[f62,f85])).
% 6.84/1.48  
% 6.84/1.48  fof(f10,axiom,(
% 6.84/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f32,plain,(
% 6.84/1.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.84/1.48    inference(ennf_transformation,[],[f10])).
% 6.84/1.48  
% 6.84/1.48  fof(f64,plain,(
% 6.84/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f32])).
% 6.84/1.48  
% 6.84/1.48  fof(f3,axiom,(
% 6.84/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f27,plain,(
% 6.84/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.84/1.48    inference(ennf_transformation,[],[f3])).
% 6.84/1.48  
% 6.84/1.48  fof(f38,plain,(
% 6.84/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.84/1.48    inference(nnf_transformation,[],[f27])).
% 6.84/1.48  
% 6.84/1.48  fof(f39,plain,(
% 6.84/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.84/1.48    inference(rectify,[],[f38])).
% 6.84/1.48  
% 6.84/1.48  fof(f40,plain,(
% 6.84/1.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 6.84/1.48    introduced(choice_axiom,[])).
% 6.84/1.48  
% 6.84/1.48  fof(f41,plain,(
% 6.84/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.84/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 6.84/1.48  
% 6.84/1.48  fof(f52,plain,(
% 6.84/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f41])).
% 6.84/1.48  
% 6.84/1.48  fof(f1,axiom,(
% 6.84/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f49,plain,(
% 6.84/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f1])).
% 6.84/1.48  
% 6.84/1.48  fof(f6,axiom,(
% 6.84/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f24,plain,(
% 6.84/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 6.84/1.48    inference(rectify,[],[f6])).
% 6.84/1.48  
% 6.84/1.48  fof(f29,plain,(
% 6.84/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 6.84/1.48    inference(ennf_transformation,[],[f24])).
% 6.84/1.48  
% 6.84/1.48  fof(f43,plain,(
% 6.84/1.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 6.84/1.48    introduced(choice_axiom,[])).
% 6.84/1.48  
% 6.84/1.48  fof(f44,plain,(
% 6.84/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 6.84/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f43])).
% 6.84/1.48  
% 6.84/1.48  fof(f58,plain,(
% 6.84/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 6.84/1.48    inference(cnf_transformation,[],[f44])).
% 6.84/1.48  
% 6.84/1.48  fof(f20,axiom,(
% 6.84/1.48    ! [X0,X1] : (r2_hidden(X0,X1) => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0))),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f34,plain,(
% 6.84/1.48    ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1))),
% 6.84/1.48    inference(ennf_transformation,[],[f20])).
% 6.84/1.48  
% 6.84/1.48  fof(f74,plain,(
% 6.84/1.48    ( ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f34])).
% 6.84/1.48  
% 6.84/1.48  fof(f91,plain,(
% 6.84/1.48    ( ! [X0,X1] : (k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,X1)) )),
% 6.84/1.48    inference(definition_unfolding,[],[f74,f86,f86])).
% 6.84/1.48  
% 6.84/1.48  fof(f11,axiom,(
% 6.84/1.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f65,plain,(
% 6.84/1.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 6.84/1.48    inference(cnf_transformation,[],[f11])).
% 6.84/1.48  
% 6.84/1.48  fof(f89,plain,(
% 6.84/1.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 6.84/1.48    inference(definition_unfolding,[],[f65,f85])).
% 6.84/1.48  
% 6.84/1.48  fof(f51,plain,(
% 6.84/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f41])).
% 6.84/1.48  
% 6.84/1.48  fof(f77,plain,(
% 6.84/1.48    k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4),
% 6.84/1.48    inference(cnf_transformation,[],[f48])).
% 6.84/1.48  
% 6.84/1.48  fof(f94,plain,(
% 6.84/1.48    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5 | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4),
% 6.84/1.48    inference(definition_unfolding,[],[f77,f86,f86])).
% 6.84/1.48  
% 6.84/1.48  fof(f78,plain,(
% 6.84/1.48    k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4),
% 6.84/1.48    inference(cnf_transformation,[],[f48])).
% 6.84/1.48  
% 6.84/1.48  fof(f93,plain,(
% 6.84/1.48    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5 | k1_xboole_0 != sK4),
% 6.84/1.48    inference(definition_unfolding,[],[f78,f86])).
% 6.84/1.48  
% 6.84/1.48  fof(f61,plain,(
% 6.84/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f46])).
% 6.84/1.48  
% 6.84/1.48  fof(f57,plain,(
% 6.84/1.48    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f44])).
% 6.84/1.48  
% 6.84/1.48  fof(f4,axiom,(
% 6.84/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f42,plain,(
% 6.84/1.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 6.84/1.48    inference(nnf_transformation,[],[f4])).
% 6.84/1.48  
% 6.84/1.48  fof(f54,plain,(
% 6.84/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f42])).
% 6.84/1.48  
% 6.84/1.48  fof(f9,axiom,(
% 6.84/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 6.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.84/1.48  
% 6.84/1.48  fof(f31,plain,(
% 6.84/1.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 6.84/1.48    inference(ennf_transformation,[],[f9])).
% 6.84/1.48  
% 6.84/1.48  fof(f63,plain,(
% 6.84/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f31])).
% 6.84/1.48  
% 6.84/1.48  fof(f88,plain,(
% 6.84/1.48    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 6.84/1.48    inference(definition_unfolding,[],[f63,f85])).
% 6.84/1.48  
% 6.84/1.48  fof(f79,plain,(
% 6.84/1.48    k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4),
% 6.84/1.48    inference(cnf_transformation,[],[f48])).
% 6.84/1.48  
% 6.84/1.48  fof(f92,plain,(
% 6.84/1.48    k1_xboole_0 != sK5 | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4),
% 6.84/1.48    inference(definition_unfolding,[],[f79,f86])).
% 6.84/1.48  
% 6.84/1.48  fof(f53,plain,(
% 6.84/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 6.84/1.48    inference(cnf_transformation,[],[f41])).
% 6.84/1.48  
% 6.84/1.48  cnf(c_17,plain,
% 6.84/1.48      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 6.84/1.48      | r2_hidden(X0,X1) ),
% 6.84/1.48      inference(cnf_transformation,[],[f90]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_963,plain,
% 6.84/1.48      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 6.84/1.48      | r2_hidden(X0,X1) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_12,plain,
% 6.84/1.48      ( r1_tarski(X0,X0) ),
% 6.84/1.48      inference(cnf_transformation,[],[f97]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_968,plain,
% 6.84/1.48      ( r1_tarski(X0,X0) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_22,negated_conjecture,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
% 6.84/1.48      inference(cnf_transformation,[],[f95]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_13,plain,
% 6.84/1.48      ( ~ r1_tarski(X0,X1)
% 6.84/1.48      | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 6.84/1.48      inference(cnf_transformation,[],[f87]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_967,plain,
% 6.84/1.48      ( r1_tarski(X0,X1) != iProver_top
% 6.84/1.48      | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2560,plain,
% 6.84/1.48      ( r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 6.84/1.48      | r1_tarski(X0,sK5) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_22,c_967]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_15,plain,
% 6.84/1.48      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 6.84/1.48      inference(cnf_transformation,[],[f64]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_965,plain,
% 6.84/1.48      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2604,plain,
% 6.84/1.48      ( k3_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = X0
% 6.84/1.48      | r1_tarski(X0,sK5) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_2560,c_965]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2708,plain,
% 6.84/1.48      ( k3_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = sK5 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_968,c_2604]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_3,plain,
% 6.84/1.48      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 6.84/1.48      inference(cnf_transformation,[],[f52]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_975,plain,
% 6.84/1.48      ( r1_tarski(X0,X1) = iProver_top
% 6.84/1.48      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_0,plain,
% 6.84/1.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 6.84/1.48      inference(cnf_transformation,[],[f49]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_8,plain,
% 6.84/1.48      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 6.84/1.48      inference(cnf_transformation,[],[f58]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_971,plain,
% 6.84/1.48      ( r1_xboole_0(X0,X1) != iProver_top
% 6.84/1.48      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1800,plain,
% 6.84/1.48      ( r1_xboole_0(X0,X1) != iProver_top
% 6.84/1.48      | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_0,c_971]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1974,plain,
% 6.84/1.48      ( r1_xboole_0(X0,X1) != iProver_top
% 6.84/1.48      | r1_tarski(k3_xboole_0(X1,X0),X2) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_975,c_1800]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_9723,plain,
% 6.84/1.48      ( r1_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK5) != iProver_top
% 6.84/1.48      | r1_tarski(sK5,X0) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_2708,c_1974]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_10619,plain,
% 6.84/1.48      ( r1_tarski(sK5,X0) = iProver_top
% 6.84/1.48      | r2_hidden(sK3,sK5) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_963,c_9723]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_11682,plain,
% 6.84/1.48      ( k3_xboole_0(sK5,X0) = sK5 | r2_hidden(sK3,sK5) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_10619,c_965]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_18,plain,
% 6.84/1.48      ( ~ r2_hidden(X0,X1)
% 6.84/1.48      | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 6.84/1.48      inference(cnf_transformation,[],[f91]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_962,plain,
% 6.84/1.48      ( k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
% 6.84/1.48      | r2_hidden(X1,X0) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_11724,plain,
% 6.84/1.48      ( k3_xboole_0(sK5,X0) = sK5
% 6.84/1.48      | k3_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_11682,c_962]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_11734,plain,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
% 6.84/1.48      | k3_xboole_0(sK5,X0) = sK5 ),
% 6.84/1.48      inference(light_normalisation,[status(thm)],[c_11724,c_2708]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_16222,plain,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
% 6.84/1.48      | k3_xboole_0(X0,sK5) = sK5 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_11734,c_0]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_16,plain,
% 6.84/1.48      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 6.84/1.48      inference(cnf_transformation,[],[f89]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_964,plain,
% 6.84/1.48      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1481,plain,
% 6.84/1.48      ( r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_22,c_964]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4,plain,
% 6.84/1.48      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 6.84/1.48      inference(cnf_transformation,[],[f51]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_974,plain,
% 6.84/1.48      ( r1_tarski(X0,X1) != iProver_top
% 6.84/1.48      | r2_hidden(X2,X0) != iProver_top
% 6.84/1.48      | r2_hidden(X2,X1) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2505,plain,
% 6.84/1.48      ( r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 6.84/1.48      | r2_hidden(X0,sK4) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1481,c_974]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_17597,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK5) = sK5
% 6.84/1.48      | r2_hidden(X1,sK4) != iProver_top
% 6.84/1.48      | r2_hidden(X1,sK5) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_16222,c_2505]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1546,plain,
% 6.84/1.48      ( k3_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = sK4 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1481,c_965]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1980,plain,
% 6.84/1.48      ( r1_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) != iProver_top
% 6.84/1.48      | r2_hidden(X0,sK4) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1546,c_1800]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2430,plain,
% 6.84/1.48      ( r2_hidden(X0,sK4) != iProver_top
% 6.84/1.48      | r2_hidden(sK3,sK4) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_963,c_1980]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_3192,plain,
% 6.84/1.48      ( r1_tarski(sK4,X0) = iProver_top
% 6.84/1.48      | r2_hidden(sK3,sK4) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_975,c_2430]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_3220,plain,
% 6.84/1.48      ( k3_xboole_0(sK4,X0) = sK4 | r2_hidden(sK3,sK4) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_3192,c_965]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4048,plain,
% 6.84/1.48      ( k3_xboole_0(sK4,X0) = sK4
% 6.84/1.48      | k3_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_3220,c_962]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4061,plain,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
% 6.84/1.48      | k3_xboole_0(sK4,X0) = sK4 ),
% 6.84/1.48      inference(light_normalisation,[status(thm)],[c_4048,c_1546]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4728,plain,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
% 6.84/1.48      | k3_xboole_0(X0,sK4) = sK4 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_4061,c_0]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_21,negated_conjecture,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4
% 6.84/1.48      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5 ),
% 6.84/1.48      inference(cnf_transformation,[],[f94]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5960,plain,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
% 6.84/1.48      | k3_xboole_0(X0,sK4) = sK4 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_4728,c_21]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_17576,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK4) = sK4 | k3_xboole_0(X1,sK5) = sK5 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_16222,c_5960]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_19305,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK5) = sK5
% 6.84/1.48      | r1_xboole_0(X1,sK4) != iProver_top
% 6.84/1.48      | r2_hidden(X2,sK4) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_17576,c_971]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_20,negated_conjecture,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
% 6.84/1.48      | k1_xboole_0 != sK4 ),
% 6.84/1.48      inference(cnf_transformation,[],[f93]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1182,plain,
% 6.84/1.48      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_10,plain,
% 6.84/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 6.84/1.48      inference(cnf_transformation,[],[f61]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1401,plain,
% 6.84/1.48      ( ~ r1_tarski(X0,k1_xboole_0)
% 6.84/1.48      | ~ r1_tarski(k1_xboole_0,X0)
% 6.84/1.48      | k1_xboole_0 = X0 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_10]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2228,plain,
% 6.84/1.48      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 6.84/1.48      | k1_xboole_0 = k1_xboole_0 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1401]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_547,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1132,plain,
% 6.84/1.48      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_547]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2420,plain,
% 6.84/1.48      ( sK4 != k1_xboole_0
% 6.84/1.48      | k1_xboole_0 = sK4
% 6.84/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1132]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_9,plain,
% 6.84/1.48      ( r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ),
% 6.84/1.48      inference(cnf_transformation,[],[f57]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_970,plain,
% 6.84/1.48      ( r1_xboole_0(X0,X1) = iProver_top
% 6.84/1.48      | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1768,plain,
% 6.84/1.48      ( r1_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 6.84/1.48      | r2_hidden(sK2(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),sK4) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1546,c_970]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1168,plain,
% 6.84/1.48      ( k3_xboole_0(X0,X0) = X0 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_968,c_965]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1802,plain,
% 6.84/1.48      ( r1_xboole_0(X0,X0) != iProver_top
% 6.84/1.48      | r2_hidden(X1,X0) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1168,c_971]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4552,plain,
% 6.84/1.48      ( r1_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 6.84/1.48      | r1_xboole_0(sK4,sK4) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1768,c_1802]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_6,plain,
% 6.84/1.48      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 6.84/1.48      inference(cnf_transformation,[],[f54]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_972,plain,
% 6.84/1.48      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 6.84/1.48      | r1_xboole_0(X0,X1) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_9530,plain,
% 6.84/1.48      ( k3_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0
% 6.84/1.48      | r1_xboole_0(sK4,sK4) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_4552,c_972]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_9544,plain,
% 6.84/1.48      ( sK4 = k1_xboole_0 | r1_xboole_0(sK4,sK4) != iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_9530,c_1546]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_16414,plain,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
% 6.84/1.48      | k3_xboole_0(sK5,X0) = sK5
% 6.84/1.48      | sK4 != sK5 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_11734,c_21]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_16430,plain,
% 6.84/1.48      ( k3_xboole_0(sK5,X0) = sK5 | sK4 != sK5 ),
% 6.84/1.48      inference(forward_subsumption_resolution,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_16414,c_11734]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1303,plain,
% 6.84/1.48      ( r1_tarski(sK4,sK4) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1306,plain,
% 6.84/1.48      ( r1_tarski(sK4,sK4) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_1303]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1265,plain,
% 6.84/1.48      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_10]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1510,plain,
% 6.84/1.48      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1265]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1511,plain,
% 6.84/1.48      ( r1_tarski(sK5,sK5) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_550,plain,
% 6.84/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,X2) | X2 != X1 ),
% 6.84/1.48      theory(equality) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1620,plain,
% 6.84/1.48      ( ~ r1_tarski(sK4,X0) | r1_tarski(sK4,X1) | X1 != X0 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_550]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2082,plain,
% 6.84/1.48      ( r1_tarski(sK4,X0) | ~ r1_tarski(sK4,sK4) | X0 != sK4 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1620]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2861,plain,
% 6.84/1.48      ( ~ r1_tarski(sK4,sK4) | r1_tarski(sK4,sK5) | sK5 != sK4 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_2082]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2862,plain,
% 6.84/1.48      ( sK5 != sK4
% 6.84/1.48      | r1_tarski(sK4,sK4) != iProver_top
% 6.84/1.48      | r1_tarski(sK4,sK5) = iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_2861]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1271,plain,
% 6.84/1.48      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_547]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1563,plain,
% 6.84/1.48      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1271]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1874,plain,
% 6.84/1.48      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) != sK5
% 6.84/1.48      | sK5 = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5))
% 6.84/1.48      | sK5 != sK5 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1563]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_9435,plain,
% 6.84/1.48      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) != sK5
% 6.84/1.48      | sK5 = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))
% 6.84/1.48      | sK5 != sK5 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1874]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_14,plain,
% 6.84/1.48      ( ~ r1_tarski(X0,X1)
% 6.84/1.48      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 6.84/1.48      inference(cnf_transformation,[],[f88]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1875,plain,
% 6.84/1.48      ( ~ r1_tarski(X0,sK5)
% 6.84/1.48      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_14]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_12119,plain,
% 6.84/1.48      ( ~ r1_tarski(sK4,sK5)
% 6.84/1.48      | k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1875]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_12120,plain,
% 6.84/1.48      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5
% 6.84/1.48      | r1_tarski(sK4,sK5) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_12119]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1156,plain,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != X0
% 6.84/1.48      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
% 6.84/1.48      | sK5 != X0 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_547]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_9395,plain,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5))
% 6.84/1.48      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
% 6.84/1.48      | sK5 != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1156]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_12926,plain,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))
% 6.84/1.48      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
% 6.84/1.48      | sK5 != k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_9395]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1130,plain,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != X0
% 6.84/1.48      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
% 6.84/1.48      | sK4 != X0 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_547]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_13986,plain,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
% 6.84/1.48      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
% 6.84/1.48      | sK4 != sK5 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1130]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_14005,plain,
% 6.84/1.48      ( sK4 != sK5 | sK5 = sK4 | sK5 != sK5 ),
% 6.84/1.48      inference(instantiation,[status(thm)],[c_1563]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_17172,plain,
% 6.84/1.48      ( sK4 != sK5 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_16430,c_22,c_21,c_1306,c_1510,c_1511,c_2862,c_9435,
% 6.84/1.48                 c_12120,c_12926,c_13986,c_14005]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_1767,plain,
% 6.84/1.48      ( r1_xboole_0(X0,X0) = iProver_top
% 6.84/1.48      | r2_hidden(sK2(X0,X0),X0) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1168,c_970]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4318,plain,
% 6.84/1.48      ( r1_xboole_0(X0,X1) != iProver_top
% 6.84/1.48      | r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1767,c_971]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_19302,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK5) = sK5
% 6.84/1.48      | r1_xboole_0(X1,sK4) != iProver_top
% 6.84/1.48      | r1_xboole_0(sK4,sK4) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_17576,c_4318]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_19283,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK4) = sK4
% 6.84/1.48      | r1_xboole_0(X1,sK5) != iProver_top
% 6.84/1.48      | r2_hidden(X2,sK5) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_17576,c_971]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_19,negated_conjecture,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4
% 6.84/1.48      | k1_xboole_0 != sK5 ),
% 6.84/1.48      inference(cnf_transformation,[],[f92]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_5962,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK4) = sK4 | sK5 != k1_xboole_0 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_4728,c_19]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_4549,plain,
% 6.84/1.48      ( r1_xboole_0(X0,X1) = iProver_top
% 6.84/1.48      | r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_970,c_1802]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_12981,plain,
% 6.84/1.48      ( r1_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 6.84/1.48      | r1_xboole_0(sK5,sK5) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_2708,c_4549]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_13410,plain,
% 6.84/1.48      ( k3_xboole_0(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0
% 6.84/1.48      | r1_xboole_0(sK5,sK5) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_12981,c_972]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_13425,plain,
% 6.84/1.48      ( sK5 = k1_xboole_0 | r1_xboole_0(sK5,sK5) != iProver_top ),
% 6.84/1.48      inference(demodulation,[status(thm)],[c_13410,c_2708]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_19280,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK4) = sK4
% 6.84/1.48      | r1_xboole_0(X1,sK5) != iProver_top
% 6.84/1.48      | r1_xboole_0(sK5,sK5) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_17576,c_4318]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_23353,plain,
% 6.84/1.48      ( r1_xboole_0(X1,sK5) != iProver_top | k3_xboole_0(X0,sK4) = sK4 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_19283,c_5962,c_13425,c_19280]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_23354,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK4) = sK4 | r1_xboole_0(X1,sK5) != iProver_top ),
% 6.84/1.48      inference(renaming,[status(thm)],[c_23353]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_23362,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK4) = sK4 | r2_hidden(X1,sK5) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_963,c_23354]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2,plain,
% 6.84/1.48      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 6.84/1.48      inference(cnf_transformation,[],[f53]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_976,plain,
% 6.84/1.48      ( r1_tarski(X0,X1) = iProver_top
% 6.84/1.48      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_23745,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK4) = sK4 | r1_tarski(X1,sK5) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_23362,c_976]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_23869,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK4) = sK4 | k3_xboole_0(X1,sK5) = X1 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_23745,c_965]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_969,plain,
% 6.84/1.48      ( X0 = X1
% 6.84/1.48      | r1_tarski(X1,X0) != iProver_top
% 6.84/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 6.84/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2603,plain,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = X0
% 6.84/1.48      | r1_tarski(X0,sK5) != iProver_top
% 6.84/1.48      | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_2560,c_969]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_23870,plain,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
% 6.84/1.48      | k3_xboole_0(X0,sK4) = sK4
% 6.84/1.48      | r1_tarski(sK5,sK5) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_23745,c_2603]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_23923,plain,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
% 6.84/1.48      | k3_xboole_0(X0,sK4) = sK4 ),
% 6.84/1.48      inference(forward_subsumption_resolution,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_23870,c_23745]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_23955,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK4) = sK4 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_23869,c_5960,c_23923]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_23996,plain,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5 | sK4 = sK5 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_23955,c_11734]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_24426,plain,
% 6.84/1.48      ( r1_xboole_0(X1,sK4) != iProver_top | k3_xboole_0(X0,sK5) = sK5 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_19305,c_22,c_21,c_20,c_1182,c_1306,c_1510,c_1511,
% 6.84/1.48                 c_2228,c_2420,c_2862,c_9435,c_9544,c_12120,c_12926,
% 6.84/1.48                 c_13986,c_14005,c_19302,c_23996]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_24427,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK5) = sK5 | r1_xboole_0(X1,sK4) != iProver_top ),
% 6.84/1.48      inference(renaming,[status(thm)],[c_24426]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_24435,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK5) = sK5 | r2_hidden(X1,sK4) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_963,c_24427]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_25793,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK5) = sK5 | r2_hidden(X1,sK5) = iProver_top ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_17597,c_24435]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_25799,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK5) = sK5 | r1_tarski(X1,sK5) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_25793,c_976]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_24893,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK5) = sK5 | r1_tarski(X1,sK4) = iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_24435,c_976]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_2447,plain,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
% 6.84/1.48      | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) != iProver_top ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_1481,c_969]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_26178,plain,
% 6.84/1.48      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
% 6.84/1.48      | k3_xboole_0(X0,sK5) = sK5 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_24893,c_2447]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_26219,plain,
% 6.84/1.48      ( k3_xboole_0(X0,sK5) = sK5 ),
% 6.84/1.48      inference(global_propositional_subsumption,
% 6.84/1.48                [status(thm)],
% 6.84/1.48                [c_25799,c_22,c_21,c_1306,c_1510,c_1511,c_2862,c_9435,
% 6.84/1.48                 c_12120,c_12926,c_13986,c_14005,c_23996,c_26178]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_23994,plain,
% 6.84/1.48      ( k3_xboole_0(sK4,X0) = sK4 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_23955,c_0]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(c_26246,plain,
% 6.84/1.48      ( sK4 = sK5 ),
% 6.84/1.48      inference(superposition,[status(thm)],[c_26219,c_23994]) ).
% 6.84/1.48  
% 6.84/1.48  cnf(contradiction,plain,
% 6.84/1.48      ( $false ),
% 6.84/1.48      inference(minisat,[status(thm)],[c_26246,c_17172]) ).
% 6.84/1.48  
% 6.84/1.48  
% 6.84/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 6.84/1.48  
% 6.84/1.48  ------                               Statistics
% 6.84/1.48  
% 6.84/1.48  ------ General
% 6.84/1.48  
% 6.84/1.48  abstr_ref_over_cycles:                  0
% 6.84/1.48  abstr_ref_under_cycles:                 0
% 6.84/1.48  gc_basic_clause_elim:                   0
% 6.84/1.48  forced_gc_time:                         0
% 6.84/1.48  parsing_time:                           0.009
% 6.84/1.48  unif_index_cands_time:                  0.
% 6.84/1.48  unif_index_add_time:                    0.
% 6.84/1.48  orderings_time:                         0.
% 6.84/1.48  out_proof_time:                         0.012
% 6.84/1.48  total_time:                             0.727
% 6.84/1.48  num_of_symbols:                         45
% 6.84/1.48  num_of_terms:                           15494
% 6.84/1.48  
% 6.84/1.48  ------ Preprocessing
% 6.84/1.48  
% 6.84/1.48  num_of_splits:                          0
% 6.84/1.48  num_of_split_atoms:                     0
% 6.84/1.48  num_of_reused_defs:                     0
% 6.84/1.48  num_eq_ax_congr_red:                    25
% 6.84/1.48  num_of_sem_filtered_clauses:            1
% 6.84/1.48  num_of_subtypes:                        0
% 6.84/1.48  monotx_restored_types:                  0
% 6.84/1.48  sat_num_of_epr_types:                   0
% 6.84/1.48  sat_num_of_non_cyclic_types:            0
% 6.84/1.48  sat_guarded_non_collapsed_types:        0
% 6.84/1.48  num_pure_diseq_elim:                    0
% 6.84/1.48  simp_replaced_by:                       0
% 6.84/1.48  res_preprocessed:                       102
% 6.84/1.48  prep_upred:                             0
% 6.84/1.48  prep_unflattend:                        8
% 6.84/1.48  smt_new_axioms:                         0
% 6.84/1.48  pred_elim_cands:                        3
% 6.84/1.48  pred_elim:                              1
% 6.84/1.48  pred_elim_cl:                           1
% 6.84/1.48  pred_elim_cycles:                       3
% 6.84/1.48  merged_defs:                            8
% 6.84/1.48  merged_defs_ncl:                        0
% 6.84/1.48  bin_hyper_res:                          8
% 6.84/1.48  prep_cycles:                            4
% 6.84/1.48  pred_elim_time:                         0.002
% 6.84/1.48  splitting_time:                         0.
% 6.84/1.48  sem_filter_time:                        0.
% 6.84/1.48  monotx_time:                            0.
% 6.84/1.48  subtype_inf_time:                       0.
% 6.84/1.48  
% 6.84/1.48  ------ Problem properties
% 6.84/1.48  
% 6.84/1.48  clauses:                                21
% 6.84/1.48  conjectures:                            4
% 6.84/1.48  epr:                                    3
% 6.84/1.48  horn:                                   17
% 6.84/1.48  ground:                                 4
% 6.84/1.48  unary:                                  4
% 6.84/1.48  binary:                                 15
% 6.84/1.48  lits:                                   40
% 6.84/1.48  lits_eq:                                15
% 6.84/1.48  fd_pure:                                0
% 6.84/1.48  fd_pseudo:                              0
% 6.84/1.48  fd_cond:                                1
% 6.84/1.48  fd_pseudo_cond:                         1
% 6.84/1.48  ac_symbols:                             0
% 6.84/1.48  
% 6.84/1.48  ------ Propositional Solver
% 6.84/1.48  
% 6.84/1.48  prop_solver_calls:                      30
% 6.84/1.48  prop_fast_solver_calls:                 1074
% 6.84/1.48  smt_solver_calls:                       0
% 6.84/1.48  smt_fast_solver_calls:                  0
% 6.84/1.48  prop_num_of_clauses:                    9432
% 6.84/1.48  prop_preprocess_simplified:             13573
% 6.84/1.48  prop_fo_subsumed:                       35
% 6.84/1.48  prop_solver_time:                       0.
% 6.84/1.48  smt_solver_time:                        0.
% 6.84/1.48  smt_fast_solver_time:                   0.
% 6.84/1.48  prop_fast_solver_time:                  0.
% 6.84/1.48  prop_unsat_core_time:                   0.
% 6.84/1.48  
% 6.84/1.48  ------ QBF
% 6.84/1.48  
% 6.84/1.48  qbf_q_res:                              0
% 6.84/1.48  qbf_num_tautologies:                    0
% 6.84/1.48  qbf_prep_cycles:                        0
% 6.84/1.48  
% 6.84/1.48  ------ BMC1
% 6.84/1.48  
% 6.84/1.48  bmc1_current_bound:                     -1
% 6.84/1.48  bmc1_last_solved_bound:                 -1
% 6.84/1.48  bmc1_unsat_core_size:                   -1
% 6.84/1.48  bmc1_unsat_core_parents_size:           -1
% 6.84/1.48  bmc1_merge_next_fun:                    0
% 6.84/1.48  bmc1_unsat_core_clauses_time:           0.
% 6.84/1.48  
% 6.84/1.48  ------ Instantiation
% 6.84/1.48  
% 6.84/1.48  inst_num_of_clauses:                    2092
% 6.84/1.48  inst_num_in_passive:                    305
% 6.84/1.48  inst_num_in_active:                     758
% 6.84/1.48  inst_num_in_unprocessed:                1029
% 6.84/1.48  inst_num_of_loops:                      1120
% 6.84/1.48  inst_num_of_learning_restarts:          0
% 6.84/1.48  inst_num_moves_active_passive:          359
% 6.84/1.48  inst_lit_activity:                      0
% 6.84/1.48  inst_lit_activity_moves:                0
% 6.84/1.48  inst_num_tautologies:                   0
% 6.84/1.48  inst_num_prop_implied:                  0
% 6.84/1.48  inst_num_existing_simplified:           0
% 6.84/1.48  inst_num_eq_res_simplified:             0
% 6.84/1.48  inst_num_child_elim:                    0
% 6.84/1.48  inst_num_of_dismatching_blockings:      1195
% 6.84/1.48  inst_num_of_non_proper_insts:           2393
% 6.84/1.48  inst_num_of_duplicates:                 0
% 6.84/1.48  inst_inst_num_from_inst_to_res:         0
% 6.84/1.48  inst_dismatching_checking_time:         0.
% 6.84/1.48  
% 6.84/1.48  ------ Resolution
% 6.84/1.48  
% 6.84/1.48  res_num_of_clauses:                     0
% 6.84/1.48  res_num_in_passive:                     0
% 6.84/1.48  res_num_in_active:                      0
% 6.84/1.48  res_num_of_loops:                       106
% 6.84/1.48  res_forward_subset_subsumed:            297
% 6.84/1.48  res_backward_subset_subsumed:           4
% 6.84/1.48  res_forward_subsumed:                   0
% 6.84/1.48  res_backward_subsumed:                  0
% 6.84/1.48  res_forward_subsumption_resolution:     0
% 6.84/1.48  res_backward_subsumption_resolution:    0
% 6.84/1.48  res_clause_to_clause_subsumption:       4804
% 6.84/1.48  res_orphan_elimination:                 0
% 6.84/1.48  res_tautology_del:                      273
% 6.84/1.48  res_num_eq_res_simplified:              0
% 6.84/1.48  res_num_sel_changes:                    0
% 6.84/1.48  res_moves_from_active_to_pass:          0
% 6.84/1.48  
% 6.84/1.48  ------ Superposition
% 6.84/1.48  
% 6.84/1.48  sup_time_total:                         0.
% 6.84/1.48  sup_time_generating:                    0.
% 6.84/1.48  sup_time_sim_full:                      0.
% 6.84/1.48  sup_time_sim_immed:                     0.
% 6.84/1.48  
% 6.84/1.48  sup_num_of_clauses:                     552
% 6.84/1.48  sup_num_in_active:                      139
% 6.84/1.48  sup_num_in_passive:                     413
% 6.84/1.48  sup_num_of_loops:                       223
% 6.84/1.48  sup_fw_superposition:                   1312
% 6.84/1.48  sup_bw_superposition:                   1427
% 6.84/1.48  sup_immediate_simplified:               339
% 6.84/1.48  sup_given_eliminated:                   0
% 6.84/1.48  comparisons_done:                       0
% 6.84/1.48  comparisons_avoided:                    62
% 6.84/1.48  
% 6.84/1.48  ------ Simplifications
% 6.84/1.48  
% 6.84/1.48  
% 6.84/1.48  sim_fw_subset_subsumed:                 151
% 6.84/1.48  sim_bw_subset_subsumed:                 424
% 6.84/1.48  sim_fw_subsumed:                        77
% 6.84/1.48  sim_bw_subsumed:                        10
% 6.84/1.48  sim_fw_subsumption_res:                 22
% 6.84/1.48  sim_bw_subsumption_res:                 2
% 6.84/1.48  sim_tautology_del:                      39
% 6.84/1.48  sim_eq_tautology_del:                   30
% 6.84/1.48  sim_eq_res_simp:                        0
% 6.84/1.48  sim_fw_demodulated:                     56
% 6.84/1.48  sim_bw_demodulated:                     20
% 6.84/1.48  sim_light_normalised:                   24
% 6.84/1.48  sim_joinable_taut:                      0
% 6.84/1.48  sim_joinable_simp:                      0
% 6.84/1.48  sim_ac_normalised:                      0
% 6.84/1.48  sim_smt_subsumption:                    0
% 6.84/1.48  
%------------------------------------------------------------------------------
