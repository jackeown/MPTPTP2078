%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:21 EST 2020

% Result     : Theorem 23.84s
% Output     : CNFRefutation 23.84s
% Verified   : 
% Statistics : Number of formulae       :  160 (3283 expanded)
%              Number of clauses        :   84 ( 401 expanded)
%              Number of leaves         :   26 (1000 expanded)
%              Depth                    :   25
%              Number of atoms          :  344 (5459 expanded)
%              Number of equality atoms :  225 (4519 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK3
        | k1_tarski(sK1) != sK2 )
      & ( k1_tarski(sK1) != sK3
        | k1_xboole_0 != sK2 )
      & ( k1_tarski(sK1) != sK3
        | k1_tarski(sK1) != sK2 )
      & k2_xboole_0(sK2,sK3) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( k1_xboole_0 != sK3
      | k1_tarski(sK1) != sK2 )
    & ( k1_tarski(sK1) != sK3
      | k1_xboole_0 != sK2 )
    & ( k1_tarski(sK1) != sK3
      | k1_tarski(sK1) != sK2 )
    & k2_xboole_0(sK2,sK3) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f38])).

fof(f67,plain,(
    k2_xboole_0(sK2,sK3) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f75])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f71])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f72])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f73])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f75])).

fof(f89,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f67,f76,f78])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f52,f76])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f36])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f63,f78,f78])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f55,f76])).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f47,f77])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f90,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f49])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f34])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f70,plain,
    ( k1_xboole_0 != sK3
    | k1_tarski(sK1) != sK2 ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,
    ( k1_xboole_0 != sK3
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2 ),
    inference(definition_unfolding,[],[f70,f78])).

fof(f68,plain,
    ( k1_tarski(sK1) != sK3
    | k1_tarski(sK1) != sK2 ),
    inference(cnf_transformation,[],[f39])).

fof(f88,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2 ),
    inference(definition_unfolding,[],[f68,f78,f78])).

fof(f69,plain,
    ( k1_tarski(sK1) != sK3
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f69,f78])).

cnf(c_21,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_12,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_783,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11959,plain,
    ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_783])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_780,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13000,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11959,c_780])).

cnf(c_7,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_13,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_559,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(theory_normalisation,[status(thm)],[c_7,c_13,c_0])).

cnf(c_786,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_559])).

cnf(c_13511,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_786])).

cnf(c_13179,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13000,c_780])).

cnf(c_10,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_39,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1400,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1846,plain,
    ( ~ r2_hidden(sK0(X0,sK2),sK2)
    | ~ r1_xboole_0(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1400])).

cnf(c_1847,plain,
    ( r2_hidden(sK0(X0,sK2),sK2) != iProver_top
    | r1_xboole_0(sK2,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1846])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_6545,plain,
    ( r2_hidden(sK0(X0,sK2),sK2)
    | r1_xboole_0(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6546,plain,
    ( r2_hidden(sK0(X0,sK2),sK2) = iProver_top
    | r1_xboole_0(X0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6545])).

cnf(c_567,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1172,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | X0 != k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_567])).

cnf(c_6500,plain,
    ( r1_xboole_0(sK2,X0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | X0 != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_19726,plain,
    ( r1_xboole_0(sK2,sK2)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6500])).

cnf(c_19727,plain,
    ( sK2 != k1_xboole_0
    | r1_xboole_0(sK2,sK2) = iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19726])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_157,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_11,c_3])).

cnf(c_19740,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_xboole_0(X0,sK2)
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_19746,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,sK2) != iProver_top
    | r1_xboole_0(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19740])).

cnf(c_19924,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13179,c_39,c_1847,c_6546,c_19727,c_19746])).

cnf(c_19936,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k5_xboole_0(sK2,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13511,c_19924])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1071,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_14,c_13])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1036,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_1273,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1071,c_1036])).

cnf(c_867,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_1693,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_1273,c_867])).

cnf(c_19973,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,X0)) = k5_xboole_0(X0,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | k5_xboole_0(sK2,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19936,c_1693])).

cnf(c_41796,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,X0)) = k5_xboole_0(X0,k5_xboole_0(sK3,sK2))
    | k5_xboole_0(sK2,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13000,c_19973])).

cnf(c_18,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_13186,plain,
    ( sK2 = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13000,c_18])).

cnf(c_20,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_13184,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13000,c_20])).

cnf(c_19,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_938,plain,
    ( ~ r1_tarski(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK2
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_940,plain,
    ( ~ r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_938])).

cnf(c_562,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1134,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_562])).

cnf(c_974,plain,
    ( r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1419,plain,
    ( r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_569,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_918,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | X0 != X2
    | X1 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(instantiation,[status(thm)],[c_569])).

cnf(c_1104,plain,
    ( r1_tarski(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))
    | X0 != sK2
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_918])).

cnf(c_1567,plain,
    ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_13334,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13184,c_21,c_20,c_19,c_940,c_1134,c_1419,c_1567])).

cnf(c_15505,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK3,sK2)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_13000,c_13511])).

cnf(c_1278,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_1273])).

cnf(c_15513,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15505,c_1278])).

cnf(c_19939,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15513,c_19924])).

cnf(c_43435,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_41796,c_21,c_20,c_19,c_940,c_1134,c_1419,c_1567,c_13186,c_19939])).

cnf(c_43468,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_43435,c_13511])).

cnf(c_1691,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_8,c_867])).

cnf(c_43484,plain,
    ( r1_tarski(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_43468,c_1691])).

cnf(c_43460,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_43435,c_19924])).

cnf(c_1841,plain,
    ( ~ r2_hidden(sK0(X0,k1_xboole_0),k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1400])).

cnf(c_1842,plain,
    ( r2_hidden(sK0(X0,k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1841])).

cnf(c_5866,plain,
    ( r2_hidden(sK0(X0,k1_xboole_0),k1_xboole_0)
    | r1_xboole_0(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5867,plain,
    ( r2_hidden(sK0(X0,k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5866])).

cnf(c_12950,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_xboole_0(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_12956,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12950])).

cnf(c_91793,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43460,c_39,c_1842,c_5867,c_12956])).

cnf(c_91803,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_43484,c_91793])).

cnf(c_866,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_1614,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X2,X1))) = X2 ),
    inference(superposition,[status(thm)],[c_866,c_1278])).

cnf(c_93173,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_91803,c_1614])).

cnf(c_93192,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k5_xboole_0(X0,sK3),X0) ),
    inference(light_normalisation,[status(thm)],[c_93173,c_8])).

cnf(c_1311,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_1278,c_1278])).

cnf(c_93193,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3 ),
    inference(demodulation,[status(thm)],[c_93192,c_1311])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_93193,c_13334])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:31:05 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 23.84/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.84/3.49  
% 23.84/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.84/3.49  
% 23.84/3.49  ------  iProver source info
% 23.84/3.49  
% 23.84/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.84/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.84/3.49  git: non_committed_changes: false
% 23.84/3.49  git: last_make_outside_of_git: false
% 23.84/3.49  
% 23.84/3.49  ------ 
% 23.84/3.49  
% 23.84/3.49  ------ Input Options
% 23.84/3.49  
% 23.84/3.49  --out_options                           all
% 23.84/3.49  --tptp_safe_out                         true
% 23.84/3.49  --problem_path                          ""
% 23.84/3.49  --include_path                          ""
% 23.84/3.49  --clausifier                            res/vclausify_rel
% 23.84/3.49  --clausifier_options                    --mode clausify
% 23.84/3.49  --stdin                                 false
% 23.84/3.49  --stats_out                             all
% 23.84/3.49  
% 23.84/3.49  ------ General Options
% 23.84/3.49  
% 23.84/3.49  --fof                                   false
% 23.84/3.49  --time_out_real                         305.
% 23.84/3.49  --time_out_virtual                      -1.
% 23.84/3.49  --symbol_type_check                     false
% 23.84/3.49  --clausify_out                          false
% 23.84/3.49  --sig_cnt_out                           false
% 23.84/3.49  --trig_cnt_out                          false
% 23.84/3.49  --trig_cnt_out_tolerance                1.
% 23.84/3.49  --trig_cnt_out_sk_spl                   false
% 23.84/3.49  --abstr_cl_out                          false
% 23.84/3.49  
% 23.84/3.49  ------ Global Options
% 23.84/3.49  
% 23.84/3.49  --schedule                              default
% 23.84/3.49  --add_important_lit                     false
% 23.84/3.49  --prop_solver_per_cl                    1000
% 23.84/3.49  --min_unsat_core                        false
% 23.84/3.49  --soft_assumptions                      false
% 23.84/3.49  --soft_lemma_size                       3
% 23.84/3.49  --prop_impl_unit_size                   0
% 23.84/3.49  --prop_impl_unit                        []
% 23.84/3.49  --share_sel_clauses                     true
% 23.84/3.49  --reset_solvers                         false
% 23.84/3.49  --bc_imp_inh                            [conj_cone]
% 23.84/3.49  --conj_cone_tolerance                   3.
% 23.84/3.49  --extra_neg_conj                        none
% 23.84/3.49  --large_theory_mode                     true
% 23.84/3.49  --prolific_symb_bound                   200
% 23.84/3.49  --lt_threshold                          2000
% 23.84/3.49  --clause_weak_htbl                      true
% 23.84/3.49  --gc_record_bc_elim                     false
% 23.84/3.49  
% 23.84/3.49  ------ Preprocessing Options
% 23.84/3.49  
% 23.84/3.49  --preprocessing_flag                    true
% 23.84/3.49  --time_out_prep_mult                    0.1
% 23.84/3.49  --splitting_mode                        input
% 23.84/3.49  --splitting_grd                         true
% 23.84/3.49  --splitting_cvd                         false
% 23.84/3.49  --splitting_cvd_svl                     false
% 23.84/3.49  --splitting_nvd                         32
% 23.84/3.49  --sub_typing                            true
% 23.84/3.49  --prep_gs_sim                           true
% 23.84/3.49  --prep_unflatten                        true
% 23.84/3.49  --prep_res_sim                          true
% 23.84/3.49  --prep_upred                            true
% 23.84/3.49  --prep_sem_filter                       exhaustive
% 23.84/3.49  --prep_sem_filter_out                   false
% 23.84/3.49  --pred_elim                             true
% 23.84/3.49  --res_sim_input                         true
% 23.84/3.49  --eq_ax_congr_red                       true
% 23.84/3.49  --pure_diseq_elim                       true
% 23.84/3.49  --brand_transform                       false
% 23.84/3.49  --non_eq_to_eq                          false
% 23.84/3.49  --prep_def_merge                        true
% 23.84/3.49  --prep_def_merge_prop_impl              false
% 23.84/3.49  --prep_def_merge_mbd                    true
% 23.84/3.49  --prep_def_merge_tr_red                 false
% 23.84/3.49  --prep_def_merge_tr_cl                  false
% 23.84/3.49  --smt_preprocessing                     true
% 23.84/3.49  --smt_ac_axioms                         fast
% 23.84/3.49  --preprocessed_out                      false
% 23.84/3.49  --preprocessed_stats                    false
% 23.84/3.49  
% 23.84/3.49  ------ Abstraction refinement Options
% 23.84/3.49  
% 23.84/3.49  --abstr_ref                             []
% 23.84/3.49  --abstr_ref_prep                        false
% 23.84/3.49  --abstr_ref_until_sat                   false
% 23.84/3.49  --abstr_ref_sig_restrict                funpre
% 23.84/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.84/3.49  --abstr_ref_under                       []
% 23.84/3.49  
% 23.84/3.49  ------ SAT Options
% 23.84/3.49  
% 23.84/3.49  --sat_mode                              false
% 23.84/3.49  --sat_fm_restart_options                ""
% 23.84/3.49  --sat_gr_def                            false
% 23.84/3.49  --sat_epr_types                         true
% 23.84/3.49  --sat_non_cyclic_types                  false
% 23.84/3.49  --sat_finite_models                     false
% 23.84/3.49  --sat_fm_lemmas                         false
% 23.84/3.49  --sat_fm_prep                           false
% 23.84/3.49  --sat_fm_uc_incr                        true
% 23.84/3.49  --sat_out_model                         small
% 23.84/3.49  --sat_out_clauses                       false
% 23.84/3.49  
% 23.84/3.49  ------ QBF Options
% 23.84/3.49  
% 23.84/3.49  --qbf_mode                              false
% 23.84/3.49  --qbf_elim_univ                         false
% 23.84/3.49  --qbf_dom_inst                          none
% 23.84/3.49  --qbf_dom_pre_inst                      false
% 23.84/3.49  --qbf_sk_in                             false
% 23.84/3.49  --qbf_pred_elim                         true
% 23.84/3.49  --qbf_split                             512
% 23.84/3.49  
% 23.84/3.49  ------ BMC1 Options
% 23.84/3.49  
% 23.84/3.49  --bmc1_incremental                      false
% 23.84/3.49  --bmc1_axioms                           reachable_all
% 23.84/3.49  --bmc1_min_bound                        0
% 23.84/3.49  --bmc1_max_bound                        -1
% 23.84/3.49  --bmc1_max_bound_default                -1
% 23.84/3.49  --bmc1_symbol_reachability              true
% 23.84/3.49  --bmc1_property_lemmas                  false
% 23.84/3.49  --bmc1_k_induction                      false
% 23.84/3.49  --bmc1_non_equiv_states                 false
% 23.84/3.49  --bmc1_deadlock                         false
% 23.84/3.49  --bmc1_ucm                              false
% 23.84/3.49  --bmc1_add_unsat_core                   none
% 23.84/3.49  --bmc1_unsat_core_children              false
% 23.84/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.84/3.49  --bmc1_out_stat                         full
% 23.84/3.49  --bmc1_ground_init                      false
% 23.84/3.49  --bmc1_pre_inst_next_state              false
% 23.84/3.49  --bmc1_pre_inst_state                   false
% 23.84/3.49  --bmc1_pre_inst_reach_state             false
% 23.84/3.49  --bmc1_out_unsat_core                   false
% 23.84/3.49  --bmc1_aig_witness_out                  false
% 23.84/3.49  --bmc1_verbose                          false
% 23.84/3.49  --bmc1_dump_clauses_tptp                false
% 23.84/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.84/3.49  --bmc1_dump_file                        -
% 23.84/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.84/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.84/3.49  --bmc1_ucm_extend_mode                  1
% 23.84/3.49  --bmc1_ucm_init_mode                    2
% 23.84/3.49  --bmc1_ucm_cone_mode                    none
% 23.84/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.84/3.49  --bmc1_ucm_relax_model                  4
% 23.84/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.84/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.84/3.49  --bmc1_ucm_layered_model                none
% 23.84/3.49  --bmc1_ucm_max_lemma_size               10
% 23.84/3.49  
% 23.84/3.49  ------ AIG Options
% 23.84/3.49  
% 23.84/3.49  --aig_mode                              false
% 23.84/3.49  
% 23.84/3.49  ------ Instantiation Options
% 23.84/3.49  
% 23.84/3.49  --instantiation_flag                    true
% 23.84/3.49  --inst_sos_flag                         false
% 23.84/3.49  --inst_sos_phase                        true
% 23.84/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.84/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.84/3.49  --inst_lit_sel_side                     num_symb
% 23.84/3.49  --inst_solver_per_active                1400
% 23.84/3.49  --inst_solver_calls_frac                1.
% 23.84/3.49  --inst_passive_queue_type               priority_queues
% 23.84/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.84/3.49  --inst_passive_queues_freq              [25;2]
% 23.84/3.49  --inst_dismatching                      true
% 23.84/3.49  --inst_eager_unprocessed_to_passive     true
% 23.84/3.49  --inst_prop_sim_given                   true
% 23.84/3.49  --inst_prop_sim_new                     false
% 23.84/3.49  --inst_subs_new                         false
% 23.84/3.49  --inst_eq_res_simp                      false
% 23.84/3.49  --inst_subs_given                       false
% 23.84/3.49  --inst_orphan_elimination               true
% 23.84/3.49  --inst_learning_loop_flag               true
% 23.84/3.49  --inst_learning_start                   3000
% 23.84/3.49  --inst_learning_factor                  2
% 23.84/3.49  --inst_start_prop_sim_after_learn       3
% 23.84/3.49  --inst_sel_renew                        solver
% 23.84/3.49  --inst_lit_activity_flag                true
% 23.84/3.49  --inst_restr_to_given                   false
% 23.84/3.49  --inst_activity_threshold               500
% 23.84/3.49  --inst_out_proof                        true
% 23.84/3.49  
% 23.84/3.49  ------ Resolution Options
% 23.84/3.49  
% 23.84/3.49  --resolution_flag                       true
% 23.84/3.49  --res_lit_sel                           adaptive
% 23.84/3.49  --res_lit_sel_side                      none
% 23.84/3.49  --res_ordering                          kbo
% 23.84/3.49  --res_to_prop_solver                    active
% 23.84/3.49  --res_prop_simpl_new                    false
% 23.84/3.49  --res_prop_simpl_given                  true
% 23.84/3.49  --res_passive_queue_type                priority_queues
% 23.84/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.84/3.49  --res_passive_queues_freq               [15;5]
% 23.84/3.49  --res_forward_subs                      full
% 23.84/3.49  --res_backward_subs                     full
% 23.84/3.49  --res_forward_subs_resolution           true
% 23.84/3.49  --res_backward_subs_resolution          true
% 23.84/3.49  --res_orphan_elimination                true
% 23.84/3.49  --res_time_limit                        2.
% 23.84/3.49  --res_out_proof                         true
% 23.84/3.49  
% 23.84/3.49  ------ Superposition Options
% 23.84/3.49  
% 23.84/3.49  --superposition_flag                    true
% 23.84/3.49  --sup_passive_queue_type                priority_queues
% 23.84/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.84/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.84/3.49  --demod_completeness_check              fast
% 23.84/3.49  --demod_use_ground                      true
% 23.84/3.49  --sup_to_prop_solver                    passive
% 23.84/3.49  --sup_prop_simpl_new                    true
% 23.84/3.49  --sup_prop_simpl_given                  true
% 23.84/3.49  --sup_fun_splitting                     false
% 23.84/3.49  --sup_smt_interval                      50000
% 23.84/3.49  
% 23.84/3.49  ------ Superposition Simplification Setup
% 23.84/3.49  
% 23.84/3.49  --sup_indices_passive                   []
% 23.84/3.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.84/3.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.84/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.84/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.84/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.84/3.49  --sup_full_bw                           [BwDemod]
% 23.84/3.49  --sup_immed_triv                        [TrivRules]
% 23.84/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.84/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.84/3.49  --sup_immed_bw_main                     []
% 23.84/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.84/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.84/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.84/3.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.84/3.49  
% 23.84/3.49  ------ Combination Options
% 23.84/3.49  
% 23.84/3.49  --comb_res_mult                         3
% 23.84/3.49  --comb_sup_mult                         2
% 23.84/3.49  --comb_inst_mult                        10
% 23.84/3.49  
% 23.84/3.49  ------ Debug Options
% 23.84/3.49  
% 23.84/3.49  --dbg_backtrace                         false
% 23.84/3.49  --dbg_dump_prop_clauses                 false
% 23.84/3.49  --dbg_dump_prop_clauses_file            -
% 23.84/3.49  --dbg_out_stat                          false
% 23.84/3.49  ------ Parsing...
% 23.84/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.84/3.49  
% 23.84/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.84/3.49  
% 23.84/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.84/3.49  
% 23.84/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.84/3.49  ------ Proving...
% 23.84/3.49  ------ Problem Properties 
% 23.84/3.49  
% 23.84/3.49  
% 23.84/3.49  clauses                                 21
% 23.84/3.49  conjectures                             4
% 23.84/3.49  EPR                                     4
% 23.84/3.49  Horn                                    18
% 23.84/3.49  unary                                   12
% 23.84/3.49  binary                                  6
% 23.84/3.49  lits                                    33
% 23.84/3.49  lits eq                                 17
% 23.84/3.49  fd_pure                                 0
% 23.84/3.49  fd_pseudo                               0
% 23.84/3.49  fd_cond                                 2
% 23.84/3.49  fd_pseudo_cond                          1
% 23.84/3.49  AC symbols                              1
% 23.84/3.49  
% 23.84/3.49  ------ Schedule dynamic 5 is on 
% 23.84/3.49  
% 23.84/3.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.84/3.49  
% 23.84/3.49  
% 23.84/3.49  ------ 
% 23.84/3.49  Current options:
% 23.84/3.49  ------ 
% 23.84/3.49  
% 23.84/3.49  ------ Input Options
% 23.84/3.49  
% 23.84/3.49  --out_options                           all
% 23.84/3.49  --tptp_safe_out                         true
% 23.84/3.49  --problem_path                          ""
% 23.84/3.49  --include_path                          ""
% 23.84/3.49  --clausifier                            res/vclausify_rel
% 23.84/3.49  --clausifier_options                    --mode clausify
% 23.84/3.49  --stdin                                 false
% 23.84/3.49  --stats_out                             all
% 23.84/3.49  
% 23.84/3.49  ------ General Options
% 23.84/3.49  
% 23.84/3.49  --fof                                   false
% 23.84/3.49  --time_out_real                         305.
% 23.84/3.49  --time_out_virtual                      -1.
% 23.84/3.49  --symbol_type_check                     false
% 23.84/3.49  --clausify_out                          false
% 23.84/3.49  --sig_cnt_out                           false
% 23.84/3.49  --trig_cnt_out                          false
% 23.84/3.49  --trig_cnt_out_tolerance                1.
% 23.84/3.49  --trig_cnt_out_sk_spl                   false
% 23.84/3.49  --abstr_cl_out                          false
% 23.84/3.49  
% 23.84/3.49  ------ Global Options
% 23.84/3.49  
% 23.84/3.49  --schedule                              default
% 23.84/3.49  --add_important_lit                     false
% 23.84/3.49  --prop_solver_per_cl                    1000
% 23.84/3.49  --min_unsat_core                        false
% 23.84/3.49  --soft_assumptions                      false
% 23.84/3.49  --soft_lemma_size                       3
% 23.84/3.49  --prop_impl_unit_size                   0
% 23.84/3.49  --prop_impl_unit                        []
% 23.84/3.49  --share_sel_clauses                     true
% 23.84/3.49  --reset_solvers                         false
% 23.84/3.49  --bc_imp_inh                            [conj_cone]
% 23.84/3.49  --conj_cone_tolerance                   3.
% 23.84/3.49  --extra_neg_conj                        none
% 23.84/3.49  --large_theory_mode                     true
% 23.84/3.49  --prolific_symb_bound                   200
% 23.84/3.49  --lt_threshold                          2000
% 23.84/3.49  --clause_weak_htbl                      true
% 23.84/3.49  --gc_record_bc_elim                     false
% 23.84/3.49  
% 23.84/3.49  ------ Preprocessing Options
% 23.84/3.49  
% 23.84/3.49  --preprocessing_flag                    true
% 23.84/3.49  --time_out_prep_mult                    0.1
% 23.84/3.49  --splitting_mode                        input
% 23.84/3.49  --splitting_grd                         true
% 23.84/3.49  --splitting_cvd                         false
% 23.84/3.49  --splitting_cvd_svl                     false
% 23.84/3.49  --splitting_nvd                         32
% 23.84/3.49  --sub_typing                            true
% 23.84/3.49  --prep_gs_sim                           true
% 23.84/3.49  --prep_unflatten                        true
% 23.84/3.49  --prep_res_sim                          true
% 23.84/3.49  --prep_upred                            true
% 23.84/3.49  --prep_sem_filter                       exhaustive
% 23.84/3.49  --prep_sem_filter_out                   false
% 23.84/3.49  --pred_elim                             true
% 23.84/3.49  --res_sim_input                         true
% 23.84/3.49  --eq_ax_congr_red                       true
% 23.84/3.49  --pure_diseq_elim                       true
% 23.84/3.49  --brand_transform                       false
% 23.84/3.49  --non_eq_to_eq                          false
% 23.84/3.49  --prep_def_merge                        true
% 23.84/3.49  --prep_def_merge_prop_impl              false
% 23.84/3.49  --prep_def_merge_mbd                    true
% 23.84/3.49  --prep_def_merge_tr_red                 false
% 23.84/3.49  --prep_def_merge_tr_cl                  false
% 23.84/3.49  --smt_preprocessing                     true
% 23.84/3.49  --smt_ac_axioms                         fast
% 23.84/3.49  --preprocessed_out                      false
% 23.84/3.49  --preprocessed_stats                    false
% 23.84/3.49  
% 23.84/3.49  ------ Abstraction refinement Options
% 23.84/3.49  
% 23.84/3.49  --abstr_ref                             []
% 23.84/3.49  --abstr_ref_prep                        false
% 23.84/3.49  --abstr_ref_until_sat                   false
% 23.84/3.49  --abstr_ref_sig_restrict                funpre
% 23.84/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.84/3.49  --abstr_ref_under                       []
% 23.84/3.49  
% 23.84/3.49  ------ SAT Options
% 23.84/3.49  
% 23.84/3.49  --sat_mode                              false
% 23.84/3.49  --sat_fm_restart_options                ""
% 23.84/3.49  --sat_gr_def                            false
% 23.84/3.49  --sat_epr_types                         true
% 23.84/3.49  --sat_non_cyclic_types                  false
% 23.84/3.49  --sat_finite_models                     false
% 23.84/3.49  --sat_fm_lemmas                         false
% 23.84/3.49  --sat_fm_prep                           false
% 23.84/3.49  --sat_fm_uc_incr                        true
% 23.84/3.49  --sat_out_model                         small
% 23.84/3.49  --sat_out_clauses                       false
% 23.84/3.49  
% 23.84/3.49  ------ QBF Options
% 23.84/3.49  
% 23.84/3.49  --qbf_mode                              false
% 23.84/3.49  --qbf_elim_univ                         false
% 23.84/3.49  --qbf_dom_inst                          none
% 23.84/3.49  --qbf_dom_pre_inst                      false
% 23.84/3.49  --qbf_sk_in                             false
% 23.84/3.49  --qbf_pred_elim                         true
% 23.84/3.49  --qbf_split                             512
% 23.84/3.49  
% 23.84/3.49  ------ BMC1 Options
% 23.84/3.49  
% 23.84/3.49  --bmc1_incremental                      false
% 23.84/3.49  --bmc1_axioms                           reachable_all
% 23.84/3.49  --bmc1_min_bound                        0
% 23.84/3.49  --bmc1_max_bound                        -1
% 23.84/3.49  --bmc1_max_bound_default                -1
% 23.84/3.49  --bmc1_symbol_reachability              true
% 23.84/3.49  --bmc1_property_lemmas                  false
% 23.84/3.49  --bmc1_k_induction                      false
% 23.84/3.49  --bmc1_non_equiv_states                 false
% 23.84/3.49  --bmc1_deadlock                         false
% 23.84/3.49  --bmc1_ucm                              false
% 23.84/3.49  --bmc1_add_unsat_core                   none
% 23.84/3.49  --bmc1_unsat_core_children              false
% 23.84/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.84/3.49  --bmc1_out_stat                         full
% 23.84/3.49  --bmc1_ground_init                      false
% 23.84/3.49  --bmc1_pre_inst_next_state              false
% 23.84/3.49  --bmc1_pre_inst_state                   false
% 23.84/3.49  --bmc1_pre_inst_reach_state             false
% 23.84/3.49  --bmc1_out_unsat_core                   false
% 23.84/3.49  --bmc1_aig_witness_out                  false
% 23.84/3.49  --bmc1_verbose                          false
% 23.84/3.49  --bmc1_dump_clauses_tptp                false
% 23.84/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.84/3.49  --bmc1_dump_file                        -
% 23.84/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.84/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.84/3.49  --bmc1_ucm_extend_mode                  1
% 23.84/3.49  --bmc1_ucm_init_mode                    2
% 23.84/3.49  --bmc1_ucm_cone_mode                    none
% 23.84/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.84/3.49  --bmc1_ucm_relax_model                  4
% 23.84/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.84/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.84/3.49  --bmc1_ucm_layered_model                none
% 23.84/3.49  --bmc1_ucm_max_lemma_size               10
% 23.84/3.49  
% 23.84/3.49  ------ AIG Options
% 23.84/3.49  
% 23.84/3.49  --aig_mode                              false
% 23.84/3.49  
% 23.84/3.49  ------ Instantiation Options
% 23.84/3.49  
% 23.84/3.49  --instantiation_flag                    true
% 23.84/3.49  --inst_sos_flag                         false
% 23.84/3.49  --inst_sos_phase                        true
% 23.84/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.84/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.84/3.49  --inst_lit_sel_side                     none
% 23.84/3.49  --inst_solver_per_active                1400
% 23.84/3.49  --inst_solver_calls_frac                1.
% 23.84/3.49  --inst_passive_queue_type               priority_queues
% 23.84/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.84/3.49  --inst_passive_queues_freq              [25;2]
% 23.84/3.49  --inst_dismatching                      true
% 23.84/3.49  --inst_eager_unprocessed_to_passive     true
% 23.84/3.49  --inst_prop_sim_given                   true
% 23.84/3.49  --inst_prop_sim_new                     false
% 23.84/3.49  --inst_subs_new                         false
% 23.84/3.49  --inst_eq_res_simp                      false
% 23.84/3.49  --inst_subs_given                       false
% 23.84/3.49  --inst_orphan_elimination               true
% 23.84/3.49  --inst_learning_loop_flag               true
% 23.84/3.49  --inst_learning_start                   3000
% 23.84/3.49  --inst_learning_factor                  2
% 23.84/3.49  --inst_start_prop_sim_after_learn       3
% 23.84/3.49  --inst_sel_renew                        solver
% 23.84/3.49  --inst_lit_activity_flag                true
% 23.84/3.49  --inst_restr_to_given                   false
% 23.84/3.49  --inst_activity_threshold               500
% 23.84/3.49  --inst_out_proof                        true
% 23.84/3.49  
% 23.84/3.49  ------ Resolution Options
% 23.84/3.49  
% 23.84/3.49  --resolution_flag                       false
% 23.84/3.49  --res_lit_sel                           adaptive
% 23.84/3.49  --res_lit_sel_side                      none
% 23.84/3.49  --res_ordering                          kbo
% 23.84/3.49  --res_to_prop_solver                    active
% 23.84/3.49  --res_prop_simpl_new                    false
% 23.84/3.49  --res_prop_simpl_given                  true
% 23.84/3.49  --res_passive_queue_type                priority_queues
% 23.84/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.84/3.49  --res_passive_queues_freq               [15;5]
% 23.84/3.49  --res_forward_subs                      full
% 23.84/3.49  --res_backward_subs                     full
% 23.84/3.49  --res_forward_subs_resolution           true
% 23.84/3.49  --res_backward_subs_resolution          true
% 23.84/3.49  --res_orphan_elimination                true
% 23.84/3.49  --res_time_limit                        2.
% 23.84/3.49  --res_out_proof                         true
% 23.84/3.49  
% 23.84/3.49  ------ Superposition Options
% 23.84/3.49  
% 23.84/3.49  --superposition_flag                    true
% 23.84/3.49  --sup_passive_queue_type                priority_queues
% 23.84/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.84/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.84/3.49  --demod_completeness_check              fast
% 23.84/3.49  --demod_use_ground                      true
% 23.84/3.49  --sup_to_prop_solver                    passive
% 23.84/3.49  --sup_prop_simpl_new                    true
% 23.84/3.49  --sup_prop_simpl_given                  true
% 23.84/3.49  --sup_fun_splitting                     false
% 23.84/3.49  --sup_smt_interval                      50000
% 23.84/3.49  
% 23.84/3.49  ------ Superposition Simplification Setup
% 23.84/3.49  
% 23.84/3.49  --sup_indices_passive                   []
% 23.84/3.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.84/3.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.84/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.84/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.84/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.84/3.49  --sup_full_bw                           [BwDemod]
% 23.84/3.49  --sup_immed_triv                        [TrivRules]
% 23.84/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.84/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.84/3.49  --sup_immed_bw_main                     []
% 23.84/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.84/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.84/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.84/3.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.84/3.49  
% 23.84/3.49  ------ Combination Options
% 23.84/3.49  
% 23.84/3.49  --comb_res_mult                         3
% 23.84/3.49  --comb_sup_mult                         2
% 23.84/3.49  --comb_inst_mult                        10
% 23.84/3.49  
% 23.84/3.49  ------ Debug Options
% 23.84/3.49  
% 23.84/3.49  --dbg_backtrace                         false
% 23.84/3.49  --dbg_dump_prop_clauses                 false
% 23.84/3.49  --dbg_dump_prop_clauses_file            -
% 23.84/3.49  --dbg_out_stat                          false
% 23.84/3.49  
% 23.84/3.49  
% 23.84/3.49  
% 23.84/3.49  
% 23.84/3.49  ------ Proving...
% 23.84/3.49  
% 23.84/3.49  
% 23.84/3.49  % SZS status Theorem for theBenchmark.p
% 23.84/3.49  
% 23.84/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.84/3.49  
% 23.84/3.49  fof(f23,conjecture,(
% 23.84/3.49    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f24,negated_conjecture,(
% 23.84/3.49    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 23.84/3.49    inference(negated_conjecture,[],[f23])).
% 23.84/3.49  
% 23.84/3.49  fof(f33,plain,(
% 23.84/3.49    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 23.84/3.49    inference(ennf_transformation,[],[f24])).
% 23.84/3.49  
% 23.84/3.49  fof(f38,plain,(
% 23.84/3.49    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK3 | k1_tarski(sK1) != sK2) & (k1_tarski(sK1) != sK3 | k1_xboole_0 != sK2) & (k1_tarski(sK1) != sK3 | k1_tarski(sK1) != sK2) & k2_xboole_0(sK2,sK3) = k1_tarski(sK1))),
% 23.84/3.49    introduced(choice_axiom,[])).
% 23.84/3.49  
% 23.84/3.49  fof(f39,plain,(
% 23.84/3.49    (k1_xboole_0 != sK3 | k1_tarski(sK1) != sK2) & (k1_tarski(sK1) != sK3 | k1_xboole_0 != sK2) & (k1_tarski(sK1) != sK3 | k1_tarski(sK1) != sK2) & k2_xboole_0(sK2,sK3) = k1_tarski(sK1)),
% 23.84/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f38])).
% 23.84/3.49  
% 23.84/3.49  fof(f67,plain,(
% 23.84/3.49    k2_xboole_0(sK2,sK3) = k1_tarski(sK1)),
% 23.84/3.49    inference(cnf_transformation,[],[f39])).
% 23.84/3.49  
% 23.84/3.49  fof(f22,axiom,(
% 23.84/3.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f66,plain,(
% 23.84/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 23.84/3.49    inference(cnf_transformation,[],[f22])).
% 23.84/3.49  
% 23.84/3.49  fof(f76,plain,(
% 23.84/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 23.84/3.49    inference(definition_unfolding,[],[f66,f75])).
% 23.84/3.49  
% 23.84/3.49  fof(f14,axiom,(
% 23.84/3.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f56,plain,(
% 23.84/3.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f14])).
% 23.84/3.49  
% 23.84/3.49  fof(f15,axiom,(
% 23.84/3.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f57,plain,(
% 23.84/3.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f15])).
% 23.84/3.49  
% 23.84/3.49  fof(f16,axiom,(
% 23.84/3.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f58,plain,(
% 23.84/3.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f16])).
% 23.84/3.49  
% 23.84/3.49  fof(f17,axiom,(
% 23.84/3.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f59,plain,(
% 23.84/3.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f17])).
% 23.84/3.49  
% 23.84/3.49  fof(f18,axiom,(
% 23.84/3.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f60,plain,(
% 23.84/3.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f18])).
% 23.84/3.49  
% 23.84/3.49  fof(f19,axiom,(
% 23.84/3.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f61,plain,(
% 23.84/3.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f19])).
% 23.84/3.49  
% 23.84/3.49  fof(f20,axiom,(
% 23.84/3.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f62,plain,(
% 23.84/3.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f20])).
% 23.84/3.49  
% 23.84/3.49  fof(f71,plain,(
% 23.84/3.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 23.84/3.49    inference(definition_unfolding,[],[f61,f62])).
% 23.84/3.49  
% 23.84/3.49  fof(f72,plain,(
% 23.84/3.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 23.84/3.49    inference(definition_unfolding,[],[f60,f71])).
% 23.84/3.49  
% 23.84/3.49  fof(f73,plain,(
% 23.84/3.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 23.84/3.49    inference(definition_unfolding,[],[f59,f72])).
% 23.84/3.49  
% 23.84/3.49  fof(f74,plain,(
% 23.84/3.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 23.84/3.49    inference(definition_unfolding,[],[f58,f73])).
% 23.84/3.49  
% 23.84/3.49  fof(f75,plain,(
% 23.84/3.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 23.84/3.49    inference(definition_unfolding,[],[f57,f74])).
% 23.84/3.49  
% 23.84/3.49  fof(f78,plain,(
% 23.84/3.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 23.84/3.49    inference(definition_unfolding,[],[f56,f75])).
% 23.84/3.49  
% 23.84/3.49  fof(f89,plain,(
% 23.84/3.49    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 23.84/3.49    inference(definition_unfolding,[],[f67,f76,f78])).
% 23.84/3.49  
% 23.84/3.49  fof(f10,axiom,(
% 23.84/3.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f52,plain,(
% 23.84/3.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 23.84/3.49    inference(cnf_transformation,[],[f10])).
% 23.84/3.49  
% 23.84/3.49  fof(f82,plain,(
% 23.84/3.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 23.84/3.49    inference(definition_unfolding,[],[f52,f76])).
% 23.84/3.49  
% 23.84/3.49  fof(f21,axiom,(
% 23.84/3.49    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f36,plain,(
% 23.84/3.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 23.84/3.49    inference(nnf_transformation,[],[f21])).
% 23.84/3.49  
% 23.84/3.49  fof(f37,plain,(
% 23.84/3.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 23.84/3.49    inference(flattening,[],[f36])).
% 23.84/3.49  
% 23.84/3.49  fof(f63,plain,(
% 23.84/3.49    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 23.84/3.49    inference(cnf_transformation,[],[f37])).
% 23.84/3.49  
% 23.84/3.49  fof(f85,plain,(
% 23.84/3.49    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 23.84/3.49    inference(definition_unfolding,[],[f63,f78,f78])).
% 23.84/3.49  
% 23.84/3.49  fof(f6,axiom,(
% 23.84/3.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f47,plain,(
% 23.84/3.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f6])).
% 23.84/3.49  
% 23.84/3.49  fof(f13,axiom,(
% 23.84/3.49    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f55,plain,(
% 23.84/3.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f13])).
% 23.84/3.49  
% 23.84/3.49  fof(f77,plain,(
% 23.84/3.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 23.84/3.49    inference(definition_unfolding,[],[f55,f76])).
% 23.84/3.49  
% 23.84/3.49  fof(f81,plain,(
% 23.84/3.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 23.84/3.49    inference(definition_unfolding,[],[f47,f77])).
% 23.84/3.49  
% 23.84/3.49  fof(f11,axiom,(
% 23.84/3.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f53,plain,(
% 23.84/3.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f11])).
% 23.84/3.49  
% 23.84/3.49  fof(f1,axiom,(
% 23.84/3.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f40,plain,(
% 23.84/3.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f1])).
% 23.84/3.49  
% 23.84/3.49  fof(f8,axiom,(
% 23.84/3.49    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f30,plain,(
% 23.84/3.49    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 23.84/3.49    inference(ennf_transformation,[],[f8])).
% 23.84/3.49  
% 23.84/3.49  fof(f49,plain,(
% 23.84/3.49    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f30])).
% 23.84/3.49  
% 23.84/3.49  fof(f90,plain,(
% 23.84/3.49    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 23.84/3.49    inference(equality_resolution,[],[f49])).
% 23.84/3.49  
% 23.84/3.49  fof(f5,axiom,(
% 23.84/3.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f27,plain,(
% 23.84/3.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 23.84/3.49    inference(rectify,[],[f5])).
% 23.84/3.49  
% 23.84/3.49  fof(f29,plain,(
% 23.84/3.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 23.84/3.49    inference(ennf_transformation,[],[f27])).
% 23.84/3.49  
% 23.84/3.49  fof(f34,plain,(
% 23.84/3.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 23.84/3.49    introduced(choice_axiom,[])).
% 23.84/3.49  
% 23.84/3.49  fof(f35,plain,(
% 23.84/3.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 23.84/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f34])).
% 23.84/3.49  
% 23.84/3.49  fof(f46,plain,(
% 23.84/3.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f35])).
% 23.84/3.49  
% 23.84/3.49  fof(f45,plain,(
% 23.84/3.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f35])).
% 23.84/3.49  
% 23.84/3.49  fof(f9,axiom,(
% 23.84/3.49    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f31,plain,(
% 23.84/3.49    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 23.84/3.49    inference(ennf_transformation,[],[f9])).
% 23.84/3.49  
% 23.84/3.49  fof(f32,plain,(
% 23.84/3.49    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 23.84/3.49    inference(flattening,[],[f31])).
% 23.84/3.49  
% 23.84/3.49  fof(f51,plain,(
% 23.84/3.49    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f32])).
% 23.84/3.49  
% 23.84/3.49  fof(f4,axiom,(
% 23.84/3.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f28,plain,(
% 23.84/3.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 23.84/3.49    inference(ennf_transformation,[],[f4])).
% 23.84/3.49  
% 23.84/3.49  fof(f43,plain,(
% 23.84/3.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 23.84/3.49    inference(cnf_transformation,[],[f28])).
% 23.84/3.49  
% 23.84/3.49  fof(f12,axiom,(
% 23.84/3.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f54,plain,(
% 23.84/3.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 23.84/3.49    inference(cnf_transformation,[],[f12])).
% 23.84/3.49  
% 23.84/3.49  fof(f7,axiom,(
% 23.84/3.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 23.84/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.49  
% 23.84/3.49  fof(f48,plain,(
% 23.84/3.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.84/3.49    inference(cnf_transformation,[],[f7])).
% 23.84/3.49  
% 23.84/3.49  fof(f70,plain,(
% 23.84/3.49    k1_xboole_0 != sK3 | k1_tarski(sK1) != sK2),
% 23.84/3.49    inference(cnf_transformation,[],[f39])).
% 23.84/3.49  
% 23.84/3.49  fof(f86,plain,(
% 23.84/3.49    k1_xboole_0 != sK3 | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2),
% 23.84/3.49    inference(definition_unfolding,[],[f70,f78])).
% 23.84/3.49  
% 23.84/3.49  fof(f68,plain,(
% 23.84/3.49    k1_tarski(sK1) != sK3 | k1_tarski(sK1) != sK2),
% 23.84/3.49    inference(cnf_transformation,[],[f39])).
% 23.84/3.49  
% 23.84/3.49  fof(f88,plain,(
% 23.84/3.49    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2),
% 23.84/3.49    inference(definition_unfolding,[],[f68,f78,f78])).
% 23.84/3.49  
% 23.84/3.49  fof(f69,plain,(
% 23.84/3.49    k1_tarski(sK1) != sK3 | k1_xboole_0 != sK2),
% 23.84/3.49    inference(cnf_transformation,[],[f39])).
% 23.84/3.49  
% 23.84/3.49  fof(f87,plain,(
% 23.84/3.49    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 | k1_xboole_0 != sK2),
% 23.84/3.49    inference(definition_unfolding,[],[f69,f78])).
% 23.84/3.49  
% 23.84/3.49  cnf(c_21,negated_conjecture,
% 23.84/3.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 23.84/3.49      inference(cnf_transformation,[],[f89]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_12,plain,
% 23.84/3.49      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 23.84/3.49      inference(cnf_transformation,[],[f82]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_783,plain,
% 23.84/3.49      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_11959,plain,
% 23.84/3.49      ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
% 23.84/3.49      inference(superposition,[status(thm)],[c_21,c_783]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_17,plain,
% 23.84/3.49      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 23.84/3.49      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 23.84/3.49      | k1_xboole_0 = X0 ),
% 23.84/3.49      inference(cnf_transformation,[],[f85]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_780,plain,
% 23.84/3.49      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 23.84/3.49      | k1_xboole_0 = X1
% 23.84/3.49      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_13000,plain,
% 23.84/3.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
% 23.84/3.49      | sK2 = k1_xboole_0 ),
% 23.84/3.49      inference(superposition,[status(thm)],[c_11959,c_780]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_7,plain,
% 23.84/3.49      ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
% 23.84/3.49      inference(cnf_transformation,[],[f81]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_13,plain,
% 23.84/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 23.84/3.49      inference(cnf_transformation,[],[f53]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_0,plain,
% 23.84/3.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 23.84/3.49      inference(cnf_transformation,[],[f40]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_559,plain,
% 23.84/3.49      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
% 23.84/3.49      inference(theory_normalisation,[status(thm)],[c_7,c_13,c_0]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_786,plain,
% 23.84/3.49      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_559]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_13511,plain,
% 23.84/3.49      ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
% 23.84/3.49      inference(superposition,[status(thm)],[c_21,c_786]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_13179,plain,
% 23.84/3.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = X0
% 23.84/3.49      | sK2 = k1_xboole_0
% 23.84/3.49      | k1_xboole_0 = X0
% 23.84/3.49      | r1_tarski(X0,sK2) != iProver_top ),
% 23.84/3.49      inference(superposition,[status(thm)],[c_13000,c_780]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_10,plain,
% 23.84/3.49      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 23.84/3.49      inference(cnf_transformation,[],[f90]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_39,plain,
% 23.84/3.49      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_4,plain,
% 23.84/3.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 23.84/3.49      inference(cnf_transformation,[],[f46]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_1400,plain,
% 23.84/3.49      ( ~ r2_hidden(sK0(X0,X1),X1)
% 23.84/3.49      | ~ r2_hidden(sK0(X0,X1),X2)
% 23.84/3.49      | ~ r1_xboole_0(X2,X1) ),
% 23.84/3.49      inference(instantiation,[status(thm)],[c_4]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_1846,plain,
% 23.84/3.49      ( ~ r2_hidden(sK0(X0,sK2),sK2) | ~ r1_xboole_0(sK2,sK2) ),
% 23.84/3.49      inference(instantiation,[status(thm)],[c_1400]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_1847,plain,
% 23.84/3.49      ( r2_hidden(sK0(X0,sK2),sK2) != iProver_top
% 23.84/3.49      | r1_xboole_0(sK2,sK2) != iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_1846]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_5,plain,
% 23.84/3.49      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 23.84/3.49      inference(cnf_transformation,[],[f45]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_6545,plain,
% 23.84/3.49      ( r2_hidden(sK0(X0,sK2),sK2) | r1_xboole_0(X0,sK2) ),
% 23.84/3.49      inference(instantiation,[status(thm)],[c_5]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_6546,plain,
% 23.84/3.49      ( r2_hidden(sK0(X0,sK2),sK2) = iProver_top
% 23.84/3.49      | r1_xboole_0(X0,sK2) = iProver_top ),
% 23.84/3.49      inference(predicate_to_equality,[status(thm)],[c_6545]) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_567,plain,
% 23.84/3.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.84/3.49      theory(equality) ).
% 23.84/3.49  
% 23.84/3.49  cnf(c_1172,plain,
% 23.84/3.49      ( r1_xboole_0(X0,X1)
% 23.84/3.49      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 23.84/3.49      | X0 != k1_xboole_0
% 23.84/3.49      | X1 != k1_xboole_0 ),
% 23.84/3.49      inference(instantiation,[status(thm)],[c_567]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_6500,plain,
% 23.84/3.50      ( r1_xboole_0(sK2,X0)
% 23.84/3.50      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 23.84/3.50      | X0 != k1_xboole_0
% 23.84/3.50      | sK2 != k1_xboole_0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_1172]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_19726,plain,
% 23.84/3.50      ( r1_xboole_0(sK2,sK2)
% 23.84/3.50      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 23.84/3.50      | sK2 != k1_xboole_0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_6500]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_19727,plain,
% 23.84/3.50      ( sK2 != k1_xboole_0
% 23.84/3.50      | r1_xboole_0(sK2,sK2) = iProver_top
% 23.84/3.50      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 23.84/3.50      inference(predicate_to_equality,[status(thm)],[c_19726]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_11,plain,
% 23.84/3.50      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 23.84/3.50      inference(cnf_transformation,[],[f51]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_3,plain,
% 23.84/3.50      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 23.84/3.50      inference(cnf_transformation,[],[f43]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_157,plain,
% 23.84/3.50      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | k1_xboole_0 = X0 ),
% 23.84/3.50      inference(resolution,[status(thm)],[c_11,c_3]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_19740,plain,
% 23.84/3.50      ( ~ r1_tarski(X0,sK2) | ~ r1_xboole_0(X0,sK2) | k1_xboole_0 = X0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_157]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_19746,plain,
% 23.84/3.50      ( k1_xboole_0 = X0
% 23.84/3.50      | r1_tarski(X0,sK2) != iProver_top
% 23.84/3.50      | r1_xboole_0(X0,sK2) != iProver_top ),
% 23.84/3.50      inference(predicate_to_equality,[status(thm)],[c_19740]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_19924,plain,
% 23.84/3.50      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = X0
% 23.84/3.50      | k1_xboole_0 = X0
% 23.84/3.50      | r1_tarski(X0,sK2) != iProver_top ),
% 23.84/3.50      inference(global_propositional_subsumption,
% 23.84/3.50                [status(thm)],
% 23.84/3.50                [c_13179,c_39,c_1847,c_6546,c_19727,c_19746]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_19936,plain,
% 23.84/3.50      ( k5_xboole_0(sK2,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 23.84/3.50      | k5_xboole_0(sK2,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0 ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_13511,c_19924]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_14,plain,
% 23.84/3.50      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.84/3.50      inference(cnf_transformation,[],[f54]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1071,plain,
% 23.84/3.50      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_14,c_13]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_8,plain,
% 23.84/3.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.84/3.50      inference(cnf_transformation,[],[f48]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1036,plain,
% 23.84/3.50      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1273,plain,
% 23.84/3.50      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 23.84/3.50      inference(demodulation,[status(thm)],[c_1071,c_1036]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_867,plain,
% 23.84/3.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1693,plain,
% 23.84/3.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X2,X1) ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_1273,c_867]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_19973,plain,
% 23.84/3.50      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,X0)) = k5_xboole_0(X0,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
% 23.84/3.50      | k5_xboole_0(sK2,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0 ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_19936,c_1693]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_41796,plain,
% 23.84/3.50      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,X0)) = k5_xboole_0(X0,k5_xboole_0(sK3,sK2))
% 23.84/3.50      | k5_xboole_0(sK2,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
% 23.84/3.50      | sK2 = k1_xboole_0 ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_13000,c_19973]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_18,negated_conjecture,
% 23.84/3.50      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2
% 23.84/3.50      | k1_xboole_0 != sK3 ),
% 23.84/3.50      inference(cnf_transformation,[],[f86]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_13186,plain,
% 23.84/3.50      ( sK2 = k1_xboole_0 | sK3 != k1_xboole_0 ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_13000,c_18]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_20,negated_conjecture,
% 23.84/3.50      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2
% 23.84/3.50      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 ),
% 23.84/3.50      inference(cnf_transformation,[],[f88]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_13184,plain,
% 23.84/3.50      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
% 23.84/3.50      | sK2 = k1_xboole_0 ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_13000,c_20]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_19,negated_conjecture,
% 23.84/3.50      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
% 23.84/3.50      | k1_xboole_0 != sK2 ),
% 23.84/3.50      inference(cnf_transformation,[],[f87]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_938,plain,
% 23.84/3.50      ( ~ r1_tarski(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 23.84/3.50      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK2
% 23.84/3.50      | k1_xboole_0 = sK2 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_17]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_940,plain,
% 23.84/3.50      ( ~ r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 23.84/3.50      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
% 23.84/3.50      | k1_xboole_0 = sK2 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_938]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_562,plain,( X0 = X0 ),theory(equality) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1134,plain,
% 23.84/3.50      ( sK2 = sK2 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_562]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_974,plain,
% 23.84/3.50      ( r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0))) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_12]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1419,plain,
% 23.84/3.50      ( r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_974]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_569,plain,
% 23.84/3.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.84/3.50      theory(equality) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_918,plain,
% 23.84/3.50      ( r1_tarski(X0,X1)
% 23.84/3.50      | ~ r1_tarski(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
% 23.84/3.50      | X0 != X2
% 23.84/3.50      | X1 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_569]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1104,plain,
% 23.84/3.50      ( r1_tarski(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 23.84/3.50      | ~ r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))
% 23.84/3.50      | X0 != sK2
% 23.84/3.50      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_918]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1567,plain,
% 23.84/3.50      ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 23.84/3.50      | ~ r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))
% 23.84/3.50      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 23.84/3.50      | sK2 != sK2 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_1104]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_13334,plain,
% 23.84/3.50      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 ),
% 23.84/3.50      inference(global_propositional_subsumption,
% 23.84/3.50                [status(thm)],
% 23.84/3.50                [c_13184,c_21,c_20,c_19,c_940,c_1134,c_1419,c_1567]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_15505,plain,
% 23.84/3.50      ( sK2 = k1_xboole_0
% 23.84/3.50      | r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK3,sK2)),sK2) = iProver_top ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_13000,c_13511]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1278,plain,
% 23.84/3.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_0,c_1273]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_15513,plain,
% 23.84/3.50      ( sK2 = k1_xboole_0 | r1_tarski(sK3,sK2) = iProver_top ),
% 23.84/3.50      inference(demodulation,[status(thm)],[c_15505,c_1278]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_19939,plain,
% 23.84/3.50      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3
% 23.84/3.50      | sK2 = k1_xboole_0
% 23.84/3.50      | sK3 = k1_xboole_0 ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_15513,c_19924]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_43435,plain,
% 23.84/3.50      ( sK2 = k1_xboole_0 ),
% 23.84/3.50      inference(global_propositional_subsumption,
% 23.84/3.50                [status(thm)],
% 23.84/3.50                [c_41796,c_21,c_20,c_19,c_940,c_1134,c_1419,c_1567,
% 23.84/3.50                 c_13186,c_19939]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_43468,plain,
% 23.84/3.50      ( r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k1_xboole_0) = iProver_top ),
% 23.84/3.50      inference(demodulation,[status(thm)],[c_43435,c_13511]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1691,plain,
% 23.84/3.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_8,c_867]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_43484,plain,
% 23.84/3.50      ( r1_tarski(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3),k1_xboole_0) = iProver_top ),
% 23.84/3.50      inference(demodulation,[status(thm)],[c_43468,c_1691]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_43460,plain,
% 23.84/3.50      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = X0
% 23.84/3.50      | k1_xboole_0 = X0
% 23.84/3.50      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 23.84/3.50      inference(demodulation,[status(thm)],[c_43435,c_19924]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1841,plain,
% 23.84/3.50      ( ~ r2_hidden(sK0(X0,k1_xboole_0),k1_xboole_0)
% 23.84/3.50      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_1400]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1842,plain,
% 23.84/3.50      ( r2_hidden(sK0(X0,k1_xboole_0),k1_xboole_0) != iProver_top
% 23.84/3.50      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 23.84/3.50      inference(predicate_to_equality,[status(thm)],[c_1841]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_5866,plain,
% 23.84/3.50      ( r2_hidden(sK0(X0,k1_xboole_0),k1_xboole_0)
% 23.84/3.50      | r1_xboole_0(X0,k1_xboole_0) ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_5]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_5867,plain,
% 23.84/3.50      ( r2_hidden(sK0(X0,k1_xboole_0),k1_xboole_0) = iProver_top
% 23.84/3.50      | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 23.84/3.50      inference(predicate_to_equality,[status(thm)],[c_5866]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_12950,plain,
% 23.84/3.50      ( ~ r1_tarski(X0,k1_xboole_0)
% 23.84/3.50      | ~ r1_xboole_0(X0,k1_xboole_0)
% 23.84/3.50      | k1_xboole_0 = X0 ),
% 23.84/3.50      inference(instantiation,[status(thm)],[c_157]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_12956,plain,
% 23.84/3.50      ( k1_xboole_0 = X0
% 23.84/3.50      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 23.84/3.50      | r1_xboole_0(X0,k1_xboole_0) != iProver_top ),
% 23.84/3.50      inference(predicate_to_equality,[status(thm)],[c_12950]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_91793,plain,
% 23.84/3.50      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 23.84/3.50      inference(global_propositional_subsumption,
% 23.84/3.50                [status(thm)],
% 23.84/3.50                [c_43460,c_39,c_1842,c_5867,c_12956]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_91803,plain,
% 23.84/3.50      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3) = k1_xboole_0 ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_43484,c_91793]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_866,plain,
% 23.84/3.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1614,plain,
% 23.84/3.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X2,X1))) = X2 ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_866,c_1278]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_93173,plain,
% 23.84/3.50      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X0,k1_xboole_0)) ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_91803,c_1614]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_93192,plain,
% 23.84/3.50      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k5_xboole_0(X0,sK3),X0) ),
% 23.84/3.50      inference(light_normalisation,[status(thm)],[c_93173,c_8]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_1311,plain,
% 23.84/3.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 23.84/3.50      inference(superposition,[status(thm)],[c_1278,c_1278]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(c_93193,plain,
% 23.84/3.50      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3 ),
% 23.84/3.50      inference(demodulation,[status(thm)],[c_93192,c_1311]) ).
% 23.84/3.50  
% 23.84/3.50  cnf(contradiction,plain,
% 23.84/3.50      ( $false ),
% 23.84/3.50      inference(minisat,[status(thm)],[c_93193,c_13334]) ).
% 23.84/3.50  
% 23.84/3.50  
% 23.84/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.84/3.50  
% 23.84/3.50  ------                               Statistics
% 23.84/3.50  
% 23.84/3.50  ------ General
% 23.84/3.50  
% 23.84/3.50  abstr_ref_over_cycles:                  0
% 23.84/3.50  abstr_ref_under_cycles:                 0
% 23.84/3.50  gc_basic_clause_elim:                   0
% 23.84/3.50  forced_gc_time:                         0
% 23.84/3.50  parsing_time:                           0.011
% 23.84/3.50  unif_index_cands_time:                  0.
% 23.84/3.50  unif_index_add_time:                    0.
% 23.84/3.50  orderings_time:                         0.
% 23.84/3.50  out_proof_time:                         0.015
% 23.84/3.50  total_time:                             3.01
% 23.84/3.50  num_of_symbols:                         43
% 23.84/3.50  num_of_terms:                           125048
% 23.84/3.50  
% 23.84/3.50  ------ Preprocessing
% 23.84/3.50  
% 23.84/3.50  num_of_splits:                          0
% 23.84/3.50  num_of_split_atoms:                     0
% 23.84/3.50  num_of_reused_defs:                     0
% 23.84/3.50  num_eq_ax_congr_red:                    10
% 23.84/3.50  num_of_sem_filtered_clauses:            1
% 23.84/3.50  num_of_subtypes:                        0
% 23.84/3.50  monotx_restored_types:                  0
% 23.84/3.50  sat_num_of_epr_types:                   0
% 23.84/3.50  sat_num_of_non_cyclic_types:            0
% 23.84/3.50  sat_guarded_non_collapsed_types:        0
% 23.84/3.50  num_pure_diseq_elim:                    0
% 23.84/3.50  simp_replaced_by:                       0
% 23.84/3.50  res_preprocessed:                       102
% 23.84/3.50  prep_upred:                             0
% 23.84/3.50  prep_unflattend:                        52
% 23.84/3.50  smt_new_axioms:                         0
% 23.84/3.50  pred_elim_cands:                        3
% 23.84/3.50  pred_elim:                              1
% 23.84/3.50  pred_elim_cl:                           1
% 23.84/3.50  pred_elim_cycles:                       5
% 23.84/3.50  merged_defs:                            0
% 23.84/3.50  merged_defs_ncl:                        0
% 23.84/3.50  bin_hyper_res:                          0
% 23.84/3.50  prep_cycles:                            4
% 23.84/3.50  pred_elim_time:                         0.006
% 23.84/3.50  splitting_time:                         0.
% 23.84/3.50  sem_filter_time:                        0.
% 23.84/3.50  monotx_time:                            0.001
% 23.84/3.50  subtype_inf_time:                       0.
% 23.84/3.50  
% 23.84/3.50  ------ Problem properties
% 23.84/3.50  
% 23.84/3.50  clauses:                                21
% 23.84/3.50  conjectures:                            4
% 23.84/3.50  epr:                                    4
% 23.84/3.50  horn:                                   18
% 23.84/3.50  ground:                                 5
% 23.84/3.50  unary:                                  12
% 23.84/3.50  binary:                                 6
% 23.84/3.50  lits:                                   33
% 23.84/3.50  lits_eq:                                17
% 23.84/3.50  fd_pure:                                0
% 23.84/3.50  fd_pseudo:                              0
% 23.84/3.50  fd_cond:                                2
% 23.84/3.50  fd_pseudo_cond:                         1
% 23.84/3.50  ac_symbols:                             1
% 23.84/3.50  
% 23.84/3.50  ------ Propositional Solver
% 23.84/3.50  
% 23.84/3.50  prop_solver_calls:                      29
% 23.84/3.50  prop_fast_solver_calls:                 784
% 23.84/3.50  smt_solver_calls:                       0
% 23.84/3.50  smt_fast_solver_calls:                  0
% 23.84/3.50  prop_num_of_clauses:                    15431
% 23.84/3.50  prop_preprocess_simplified:             16074
% 23.84/3.50  prop_fo_subsumed:                       7
% 23.84/3.50  prop_solver_time:                       0.
% 23.84/3.50  smt_solver_time:                        0.
% 23.84/3.50  smt_fast_solver_time:                   0.
% 23.84/3.50  prop_fast_solver_time:                  0.
% 23.84/3.50  prop_unsat_core_time:                   0.001
% 23.84/3.50  
% 23.84/3.50  ------ QBF
% 23.84/3.50  
% 23.84/3.50  qbf_q_res:                              0
% 23.84/3.50  qbf_num_tautologies:                    0
% 23.84/3.50  qbf_prep_cycles:                        0
% 23.84/3.50  
% 23.84/3.50  ------ BMC1
% 23.84/3.50  
% 23.84/3.50  bmc1_current_bound:                     -1
% 23.84/3.50  bmc1_last_solved_bound:                 -1
% 23.84/3.50  bmc1_unsat_core_size:                   -1
% 23.84/3.50  bmc1_unsat_core_parents_size:           -1
% 23.84/3.50  bmc1_merge_next_fun:                    0
% 23.84/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.84/3.50  
% 23.84/3.50  ------ Instantiation
% 23.84/3.50  
% 23.84/3.50  inst_num_of_clauses:                    2045
% 23.84/3.50  inst_num_in_passive:                    427
% 23.84/3.50  inst_num_in_active:                     665
% 23.84/3.50  inst_num_in_unprocessed:                958
% 23.84/3.50  inst_num_of_loops:                      830
% 23.84/3.50  inst_num_of_learning_restarts:          0
% 23.84/3.50  inst_num_moves_active_passive:          162
% 23.84/3.50  inst_lit_activity:                      0
% 23.84/3.50  inst_lit_activity_moves:                0
% 23.84/3.50  inst_num_tautologies:                   0
% 23.84/3.50  inst_num_prop_implied:                  0
% 23.84/3.50  inst_num_existing_simplified:           0
% 23.84/3.50  inst_num_eq_res_simplified:             0
% 23.84/3.50  inst_num_child_elim:                    0
% 23.84/3.50  inst_num_of_dismatching_blockings:      892
% 23.84/3.50  inst_num_of_non_proper_insts:           1728
% 23.84/3.50  inst_num_of_duplicates:                 0
% 23.84/3.50  inst_inst_num_from_inst_to_res:         0
% 23.84/3.50  inst_dismatching_checking_time:         0.
% 23.84/3.50  
% 23.84/3.50  ------ Resolution
% 23.84/3.50  
% 23.84/3.50  res_num_of_clauses:                     0
% 23.84/3.50  res_num_in_passive:                     0
% 23.84/3.50  res_num_in_active:                      0
% 23.84/3.50  res_num_of_loops:                       106
% 23.84/3.50  res_forward_subset_subsumed:            210
% 23.84/3.50  res_backward_subset_subsumed:           12
% 23.84/3.50  res_forward_subsumed:                   2
% 23.84/3.50  res_backward_subsumed:                  0
% 23.84/3.50  res_forward_subsumption_resolution:     0
% 23.84/3.50  res_backward_subsumption_resolution:    0
% 23.84/3.50  res_clause_to_clause_subsumption:       571478
% 23.84/3.50  res_orphan_elimination:                 0
% 23.84/3.50  res_tautology_del:                      114
% 23.84/3.50  res_num_eq_res_simplified:              0
% 23.84/3.50  res_num_sel_changes:                    0
% 23.84/3.50  res_moves_from_active_to_pass:          0
% 23.84/3.50  
% 23.84/3.50  ------ Superposition
% 23.84/3.50  
% 23.84/3.50  sup_time_total:                         0.
% 23.84/3.50  sup_time_generating:                    0.
% 23.84/3.50  sup_time_sim_full:                      0.
% 23.84/3.50  sup_time_sim_immed:                     0.
% 23.84/3.50  
% 23.84/3.50  sup_num_of_clauses:                     7021
% 23.84/3.50  sup_num_in_active:                      105
% 23.84/3.50  sup_num_in_passive:                     6916
% 23.84/3.50  sup_num_of_loops:                       165
% 23.84/3.50  sup_fw_superposition:                   17228
% 23.84/3.50  sup_bw_superposition:                   13471
% 23.84/3.50  sup_immediate_simplified:               15057
% 23.84/3.50  sup_given_eliminated:                   9
% 23.84/3.50  comparisons_done:                       0
% 23.84/3.50  comparisons_avoided:                    43
% 23.84/3.50  
% 23.84/3.50  ------ Simplifications
% 23.84/3.50  
% 23.84/3.50  
% 23.84/3.50  sim_fw_subset_subsumed:                 40
% 23.84/3.50  sim_bw_subset_subsumed:                 300
% 23.84/3.50  sim_fw_subsumed:                        705
% 23.84/3.50  sim_bw_subsumed:                        9
% 23.84/3.50  sim_fw_subsumption_res:                 0
% 23.84/3.50  sim_bw_subsumption_res:                 0
% 23.84/3.50  sim_tautology_del:                      1
% 23.84/3.50  sim_eq_tautology_del:                   1368
% 23.84/3.50  sim_eq_res_simp:                        0
% 23.84/3.50  sim_fw_demodulated:                     9758
% 23.84/3.50  sim_bw_demodulated:                     1214
% 23.84/3.50  sim_light_normalised:                   4856
% 23.84/3.50  sim_joinable_taut:                      1012
% 23.84/3.50  sim_joinable_simp:                      0
% 23.84/3.50  sim_ac_normalised:                      0
% 23.84/3.50  sim_smt_subsumption:                    0
% 23.84/3.50  
%------------------------------------------------------------------------------
