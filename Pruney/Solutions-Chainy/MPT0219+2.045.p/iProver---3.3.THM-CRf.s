%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:16 EST 2020

% Result     : Theorem 31.50s
% Output     : CNFRefutation 31.50s
% Verified   : 
% Statistics : Number of formulae       :  259 (204901 expanded)
%              Number of clauses        :  187 (74908 expanded)
%              Number of leaves         :   21 (46759 expanded)
%              Depth                    :   40
%              Number of atoms          :  416 (592011 expanded)
%              Number of equality atoms :  264 (223093 expanded)
%              Maximal formula depth    :   11 (   2 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :   17 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f57,f50])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) ),
    inference(definition_unfolding,[],[f53,f65,f65,f50])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f73])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f74])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f23,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK2 != sK3
      & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( sK2 != sK3
    & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f35])).

fof(f63,plain,(
    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f66])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f67])).

fof(f78,plain,(
    k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f63,f65,f68,f68,f68])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f55,f65])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f62,f68,f68])).

fof(f64,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_540,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_18,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_15,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1108,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_18,c_15])).

cnf(c_7237,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_0,c_1108])).

cnf(c_16,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_935,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_16,c_18])).

cnf(c_8660,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))))) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_7237,c_935])).

cnf(c_14,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_533,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_534,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1882,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_533,c_534])).

cnf(c_8700,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_8660,c_1882])).

cnf(c_8701,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_8700,c_16,c_935])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_538,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3203,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_538])).

cnf(c_8861,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8701,c_3203])).

cnf(c_33924,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = X1
    | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_540,c_8861])).

cnf(c_33926,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = X0
    | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33924,c_1882])).

cnf(c_33927,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_33926,c_16])).

cnf(c_12,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_535,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1881,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_535,c_534])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_537,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2834,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_537])).

cnf(c_30091,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1881,c_2834])).

cnf(c_30090,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1881,c_538])).

cnf(c_38027,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30091,c_30090])).

cnf(c_38036,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_33927,c_38027])).

cnf(c_1185,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_935,c_18])).

cnf(c_1186,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_1185,c_935])).

cnf(c_38588,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_38036,c_18])).

cnf(c_38957,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_1186,c_38588])).

cnf(c_38980,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_38036,c_38588])).

cnf(c_39262,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_38980,c_16])).

cnf(c_39501,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(demodulation,[status(thm)],[c_38957,c_1186,c_39262])).

cnf(c_47628,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k1_xboole_0) = X1 ),
    inference(superposition,[status(thm)],[c_38036,c_39501])).

cnf(c_47714,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),X2) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_39501,c_39501])).

cnf(c_47754,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_47714,c_1186])).

cnf(c_39011,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_38588,c_1186])).

cnf(c_39443,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(light_normalisation,[status(thm)],[c_39011,c_1186])).

cnf(c_39444,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
    inference(demodulation,[status(thm)],[c_39443,c_39262])).

cnf(c_47425,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
    inference(superposition,[status(thm)],[c_39444,c_39444])).

cnf(c_47549,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = sP0_iProver_split(X1,X2) ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_47425])).

cnf(c_47755,plain,
    ( sP0_iProver_split(X0,X1) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_47754,c_1186,c_47549])).

cnf(c_48586,plain,
    ( k5_xboole_0(k5_xboole_0(sP0_iProver_split(X0,X1),X0),k1_xboole_0) = X1 ),
    inference(light_normalisation,[status(thm)],[c_47628,c_47755])).

cnf(c_48587,plain,
    ( sP0_iProver_split(sP0_iProver_split(X0,X1),X0) = X1 ),
    inference(demodulation,[status(thm)],[c_48586,c_16,c_1186,c_47755])).

cnf(c_47666,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k1_xboole_0)) = X1 ),
    inference(superposition,[status(thm)],[c_38036,c_39501])).

cnf(c_48454,plain,
    ( k5_xboole_0(sP0_iProver_split(X0,X1),X0) = X1 ),
    inference(light_normalisation,[status(thm)],[c_47666,c_16,c_47755])).

cnf(c_39263,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_39262,c_38588])).

cnf(c_51790,plain,
    ( k5_xboole_0(sP0_iProver_split(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_48454,c_39263])).

cnf(c_53502,plain,
    ( sP0_iProver_split(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_48587,c_51790])).

cnf(c_21,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_826,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_0,c_21])).

cnf(c_936,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),X0)) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),X0) ),
    inference(superposition,[status(thm)],[c_826,c_18])).

cnf(c_1333,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),X0) ),
    inference(demodulation,[status(thm)],[c_936,c_1186])).

cnf(c_17,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_532,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1196,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_532])).

cnf(c_1318,plain,
    ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X0,X1),X2))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_1196])).

cnf(c_4029,plain,
    ( r1_tarski(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1333,c_1318])).

cnf(c_4387,plain,
    ( k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_4029,c_534])).

cnf(c_54513,plain,
    ( k3_xboole_0(sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(demodulation,[status(thm)],[c_53502,c_4387])).

cnf(c_7274,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
    inference(superposition,[status(thm)],[c_1108,c_1333])).

cnf(c_7289,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(demodulation,[status(thm)],[c_7274,c_1333])).

cnf(c_7392,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_0,c_7289])).

cnf(c_54521,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = sP0_iProver_split(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(demodulation,[status(thm)],[c_53502,c_7392])).

cnf(c_38606,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_38036,c_1333])).

cnf(c_38656,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(demodulation,[status(thm)],[c_38606,c_16])).

cnf(c_44173,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_38656,c_39263])).

cnf(c_44421,plain,
    ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_44173,c_39263])).

cnf(c_54522,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = sP0_iProver_split(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_54521,c_44421])).

cnf(c_54523,plain,
    ( sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sP0_iProver_split(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(demodulation,[status(thm)],[c_54522,c_1881,c_47755])).

cnf(c_1335,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))))) ),
    inference(superposition,[status(thm)],[c_15,c_1333])).

cnf(c_1343,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
    inference(demodulation,[status(thm)],[c_1335,c_1333])).

cnf(c_1344,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
    inference(demodulation,[status(thm)],[c_1343,c_1186])).

cnf(c_1473,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
    inference(superposition,[status(thm)],[c_0,c_1344])).

cnf(c_1494,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0)))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
    inference(superposition,[status(thm)],[c_0,c_1473])).

cnf(c_1700,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))))),X1)) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),X1) ),
    inference(superposition,[status(thm)],[c_1494,c_18])).

cnf(c_1703,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0)))),X1))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),X1))) ),
    inference(demodulation,[status(thm)],[c_1700,c_1186])).

cnf(c_1704,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))),X1)))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),X1))) ),
    inference(demodulation,[status(thm)],[c_1703,c_1186])).

cnf(c_38610,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0)))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_38036,c_1704])).

cnf(c_38654,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0)))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))) ),
    inference(demodulation,[status(thm)],[c_38610,c_16])).

cnf(c_41655,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0)))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))) ),
    inference(superposition,[status(thm)],[c_0,c_38654])).

cnf(c_47657,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))))) = k5_xboole_0(k5_xboole_0(X1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X1,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))))) ),
    inference(superposition,[status(thm)],[c_41655,c_39501])).

cnf(c_48493,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X1,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1))))) = k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X1,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1))))) ),
    inference(light_normalisation,[status(thm)],[c_47657,c_44421])).

cnf(c_8628,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_0,c_7237])).

cnf(c_44172,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_8628,c_39263])).

cnf(c_44450,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_44172,c_39263])).

cnf(c_48494,plain,
    ( sP0_iProver_split(sP0_iProver_split(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sP0_iProver_split(X0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X1,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1))))) = sP0_iProver_split(X1,k3_xboole_0(X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(demodulation,[status(thm)],[c_48493,c_1186,c_44450,c_47755])).

cnf(c_47759,plain,
    ( k5_xboole_0(sP0_iProver_split(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(demodulation,[status(thm)],[c_47755,c_39501])).

cnf(c_47784,plain,
    ( sP0_iProver_split(sP0_iProver_split(X0,X1),sP0_iProver_split(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(demodulation,[status(thm)],[c_47759,c_47755])).

cnf(c_47785,plain,
    ( sP0_iProver_split(sP0_iProver_split(X0,X1),sP0_iProver_split(X0,sP0_iProver_split(X1,X2))) = X2 ),
    inference(demodulation,[status(thm)],[c_47784,c_47755])).

cnf(c_48495,plain,
    ( sP0_iProver_split(X0,k3_xboole_0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(X0,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)) ),
    inference(demodulation,[status(thm)],[c_48494,c_47755,c_47785])).

cnf(c_54524,plain,
    ( sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(demodulation,[status(thm)],[c_54523,c_1881,c_48495])).

cnf(c_7390,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_0,c_7289])).

cnf(c_7505,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_0,c_7390])).

cnf(c_47634,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
    inference(superposition,[status(thm)],[c_7505,c_39501])).

cnf(c_48562,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sP0_iProver_split(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) ),
    inference(demodulation,[status(thm)],[c_47634,c_48495])).

cnf(c_48563,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) ),
    inference(light_normalisation,[status(thm)],[c_48562,c_44421])).

cnf(c_48564,plain,
    ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_48563,c_1186,c_1881,c_38036,c_47755])).

cnf(c_47672,plain,
    ( k5_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) = k5_xboole_0(k5_xboole_0(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
    inference(superposition,[status(thm)],[c_7505,c_39501])).

cnf(c_47677,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))))) = k5_xboole_0(k5_xboole_0(X1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X1,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))))) ),
    inference(superposition,[status(thm)],[c_38654,c_39501])).

cnf(c_44175,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0)))) ),
    inference(superposition,[status(thm)],[c_38654,c_39263])).

cnf(c_44419,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))))) = k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0)) ),
    inference(demodulation,[status(thm)],[c_44175,c_39263])).

cnf(c_44423,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0))))) = k5_xboole_0(X0,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)) ),
    inference(demodulation,[status(thm)],[c_44421,c_44419])).

cnf(c_48412,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X1,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1))))) = k5_xboole_0(X1,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1)) ),
    inference(light_normalisation,[status(thm)],[c_47677,c_44421,c_44423])).

cnf(c_48413,plain,
    ( sP0_iProver_split(sP0_iProver_split(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sP0_iProver_split(X0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X1,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1))))) = sP0_iProver_split(X1,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1)) ),
    inference(demodulation,[status(thm)],[c_48412,c_1186,c_47755])).

cnf(c_48414,plain,
    ( sP0_iProver_split(X0,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)) = k5_xboole_0(X0,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)) ),
    inference(demodulation,[status(thm)],[c_48413,c_47755,c_47785])).

cnf(c_48426,plain,
    ( k5_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sP0_iProver_split(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) = k5_xboole_0(k5_xboole_0(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
    inference(demodulation,[status(thm)],[c_47672,c_48414])).

cnf(c_48427,plain,
    ( k5_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = k5_xboole_0(k5_xboole_0(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
    inference(light_normalisation,[status(thm)],[c_48426,c_44421])).

cnf(c_48428,plain,
    ( sP0_iProver_split(sP0_iProver_split(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sP0_iProver_split(X0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) ),
    inference(demodulation,[status(thm)],[c_48427,c_1186,c_1881,c_47755])).

cnf(c_48429,plain,
    ( sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(demodulation,[status(thm)],[c_48428,c_47755,c_47785])).

cnf(c_48430,plain,
    ( sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_48429,c_1881])).

cnf(c_48565,plain,
    ( sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_xboole_0) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_48564,c_48430])).

cnf(c_51786,plain,
    ( sP0_iProver_split(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_16,c_48454])).

cnf(c_52605,plain,
    ( sP0_iProver_split(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_51786,c_48587])).

cnf(c_53054,plain,
    ( sP0_iProver_split(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_52605,c_48587])).

cnf(c_54525,plain,
    ( sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(demodulation,[status(thm)],[c_54524,c_1881,c_1882,c_48565,c_53054])).

cnf(c_54548,plain,
    ( k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(demodulation,[status(thm)],[c_54513,c_54525])).

cnf(c_1475,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
    inference(superposition,[status(thm)],[c_18,c_1344])).

cnf(c_1483,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) ),
    inference(demodulation,[status(thm)],[c_1475,c_1186])).

cnf(c_1751,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) ),
    inference(superposition,[status(thm)],[c_1483,c_1333])).

cnf(c_1752,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) ),
    inference(demodulation,[status(thm)],[c_1751,c_1333])).

cnf(c_1872,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) ),
    inference(superposition,[status(thm)],[c_1752,c_1483])).

cnf(c_1876,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) ),
    inference(demodulation,[status(thm)],[c_1872,c_1752])).

cnf(c_1877,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))))) ),
    inference(demodulation,[status(thm)],[c_1876,c_1186])).

cnf(c_1878,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))))) ),
    inference(demodulation,[status(thm)],[c_1877,c_1186])).

cnf(c_38959,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_826,c_38588])).

cnf(c_39500,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_38959,c_38036,c_39262])).

cnf(c_40343,plain,
    ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_39500,c_39262])).

cnf(c_54154,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) ),
    inference(light_normalisation,[status(thm)],[c_1878,c_1878,c_40343,c_44421])).

cnf(c_47551,plain,
    ( k5_xboole_0(X0,sP0_iProver_split(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_47549,c_39444])).

cnf(c_54155,plain,
    ( k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = sP0_iProver_split(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(demodulation,[status(thm)],[c_54154,c_1882,c_39262,c_39263,c_47551,c_47755])).

cnf(c_54156,plain,
    ( sP0_iProver_split(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = sP0_iProver_split(k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(demodulation,[status(thm)],[c_54155,c_1882,c_39262,c_39263,c_47755])).

cnf(c_54157,plain,
    ( sP0_iProver_split(k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sP0_iProver_split(k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_54156,c_1882,c_39263,c_44421,c_47755,c_51786,c_52605])).

cnf(c_54158,plain,
    ( sP0_iProver_split(k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_54157,c_1882,c_47755,c_51786])).

cnf(c_54159,plain,
    ( sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sP0_iProver_split(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_54158,c_1882,c_44421,c_47755,c_52605])).

cnf(c_54160,plain,
    ( sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sP0_iProver_split(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_54159,c_1882,c_47755,c_51786])).

cnf(c_54161,plain,
    ( sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sP0_iProver_split(k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_54160,c_39263,c_47755])).

cnf(c_54162,plain,
    ( sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_54161,c_1882,c_44421,c_51786,c_52605])).

cnf(c_54167,plain,
    ( k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_54162,c_48454])).

cnf(c_54172,plain,
    ( k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_54167,c_38036])).

cnf(c_54549,plain,
    ( k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_xboole_0)) = sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_54548,c_44421,c_54172])).

cnf(c_54550,plain,
    ( k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(demodulation,[status(thm)],[c_54549,c_16])).

cnf(c_55207,plain,
    ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_0,c_54550])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_544,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2832,plain,
    ( r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X0) = iProver_top
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_544,c_537])).

cnf(c_47673,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))) ),
    inference(superposition,[status(thm)],[c_8628,c_39501])).

cnf(c_48423,plain,
    ( k5_xboole_0(sP0_iProver_split(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))) ),
    inference(light_normalisation,[status(thm)],[c_47673,c_47755])).

cnf(c_48424,plain,
    ( sP0_iProver_split(sP0_iProver_split(X0,X1),sP0_iProver_split(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = sP0_iProver_split(X2,k3_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_48423,c_44450,c_47755])).

cnf(c_48425,plain,
    ( sP0_iProver_split(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_48424,c_47755,c_47785])).

cnf(c_65865,plain,
    ( r2_hidden(sK0(sP0_iProver_split(X0,k3_xboole_0(X0,X1)),X2),X0) = iProver_top
    | r1_tarski(sP0_iProver_split(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2832,c_48425])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_545,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_65896,plain,
    ( r1_tarski(sP0_iProver_split(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_65865,c_545])).

cnf(c_66327,plain,
    ( r1_tarski(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_55207,c_65896])).

cnf(c_47422,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2))),X3)) = k5_xboole_0(X2,X3) ),
    inference(superposition,[status(thm)],[c_39444,c_18])).

cnf(c_49161,plain,
    ( sP0_iProver_split(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3))) = sP0_iProver_split(X2,X3) ),
    inference(demodulation,[status(thm)],[c_47422,c_1186,c_47755])).

cnf(c_49162,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3))) = sP0_iProver_split(X2,X3) ),
    inference(demodulation,[status(thm)],[c_49161,c_47755])).

cnf(c_49163,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)))) = sP0_iProver_split(X2,X3) ),
    inference(demodulation,[status(thm)],[c_49162,c_1186])).

cnf(c_49164,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)))) = sP0_iProver_split(X2,X3) ),
    inference(demodulation,[status(thm)],[c_49163,c_47755])).

cnf(c_49165,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))))) = sP0_iProver_split(X2,X3) ),
    inference(demodulation,[status(thm)],[c_49164,c_1186])).

cnf(c_49166,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X2,X3))))) = sP0_iProver_split(X2,X3) ),
    inference(demodulation,[status(thm)],[c_49165,c_47755])).

cnf(c_49167,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,X3))))) = sP0_iProver_split(X2,X3) ),
    inference(demodulation,[status(thm)],[c_49166,c_47755])).

cnf(c_47680,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),X3))) = X3 ),
    inference(superposition,[status(thm)],[c_39501,c_39501])).

cnf(c_48401,plain,
    ( sP0_iProver_split(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),X3)))) = X3 ),
    inference(demodulation,[status(thm)],[c_47680,c_1186,c_47755])).

cnf(c_48402,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),X3)))) = X3 ),
    inference(demodulation,[status(thm)],[c_48401,c_47755])).

cnf(c_48403,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),X3)))) = X3 ),
    inference(demodulation,[status(thm)],[c_48402,c_47755])).

cnf(c_48404,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X0),X3))))) = X3 ),
    inference(demodulation,[status(thm)],[c_48403,c_1186])).

cnf(c_48405,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,sP0_iProver_split(X1,k5_xboole_0(k5_xboole_0(X2,X0),X3))))) = X3 ),
    inference(demodulation,[status(thm)],[c_48404,c_47755])).

cnf(c_48406,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,sP0_iProver_split(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3)))))) = X3 ),
    inference(demodulation,[status(thm)],[c_48405,c_1186])).

cnf(c_48407,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,sP0_iProver_split(X1,sP0_iProver_split(X2,k5_xboole_0(X0,X3)))))) = X3 ),
    inference(demodulation,[status(thm)],[c_48406,c_47755])).

cnf(c_48408,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,sP0_iProver_split(X1,sP0_iProver_split(X2,sP0_iProver_split(X0,X3)))))) = X3 ),
    inference(demodulation,[status(thm)],[c_48407,c_47755])).

cnf(c_49182,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_49167,c_48408])).

cnf(c_66349,plain,
    ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_66327,c_49182])).

cnf(c_19,plain,
    ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_561,plain,
    ( ~ r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_565,plain,
    ( sK2 = sK3
    | r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_20,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_66349,c_565,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:36:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.50/4.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.50/4.48  
% 31.50/4.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.50/4.48  
% 31.50/4.48  ------  iProver source info
% 31.50/4.48  
% 31.50/4.48  git: date: 2020-06-30 10:37:57 +0100
% 31.50/4.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.50/4.48  git: non_committed_changes: false
% 31.50/4.48  git: last_make_outside_of_git: false
% 31.50/4.48  
% 31.50/4.48  ------ 
% 31.50/4.48  
% 31.50/4.48  ------ Input Options
% 31.50/4.48  
% 31.50/4.48  --out_options                           all
% 31.50/4.48  --tptp_safe_out                         true
% 31.50/4.48  --problem_path                          ""
% 31.50/4.48  --include_path                          ""
% 31.50/4.48  --clausifier                            res/vclausify_rel
% 31.50/4.48  --clausifier_options                    ""
% 31.50/4.48  --stdin                                 false
% 31.50/4.48  --stats_out                             all
% 31.50/4.48  
% 31.50/4.48  ------ General Options
% 31.50/4.48  
% 31.50/4.48  --fof                                   false
% 31.50/4.48  --time_out_real                         305.
% 31.50/4.48  --time_out_virtual                      -1.
% 31.50/4.48  --symbol_type_check                     false
% 31.50/4.48  --clausify_out                          false
% 31.50/4.48  --sig_cnt_out                           false
% 31.50/4.48  --trig_cnt_out                          false
% 31.50/4.48  --trig_cnt_out_tolerance                1.
% 31.50/4.48  --trig_cnt_out_sk_spl                   false
% 31.50/4.48  --abstr_cl_out                          false
% 31.50/4.48  
% 31.50/4.48  ------ Global Options
% 31.50/4.48  
% 31.50/4.48  --schedule                              default
% 31.50/4.48  --add_important_lit                     false
% 31.50/4.48  --prop_solver_per_cl                    1000
% 31.50/4.48  --min_unsat_core                        false
% 31.50/4.48  --soft_assumptions                      false
% 31.50/4.48  --soft_lemma_size                       3
% 31.50/4.48  --prop_impl_unit_size                   0
% 31.50/4.48  --prop_impl_unit                        []
% 31.50/4.48  --share_sel_clauses                     true
% 31.50/4.48  --reset_solvers                         false
% 31.50/4.48  --bc_imp_inh                            [conj_cone]
% 31.50/4.48  --conj_cone_tolerance                   3.
% 31.50/4.48  --extra_neg_conj                        none
% 31.50/4.48  --large_theory_mode                     true
% 31.50/4.48  --prolific_symb_bound                   200
% 31.50/4.48  --lt_threshold                          2000
% 31.50/4.48  --clause_weak_htbl                      true
% 31.50/4.48  --gc_record_bc_elim                     false
% 31.50/4.48  
% 31.50/4.48  ------ Preprocessing Options
% 31.50/4.48  
% 31.50/4.48  --preprocessing_flag                    true
% 31.50/4.48  --time_out_prep_mult                    0.1
% 31.50/4.48  --splitting_mode                        input
% 31.50/4.48  --splitting_grd                         true
% 31.50/4.48  --splitting_cvd                         false
% 31.50/4.48  --splitting_cvd_svl                     false
% 31.50/4.48  --splitting_nvd                         32
% 31.50/4.48  --sub_typing                            true
% 31.50/4.48  --prep_gs_sim                           true
% 31.50/4.48  --prep_unflatten                        true
% 31.50/4.48  --prep_res_sim                          true
% 31.50/4.48  --prep_upred                            true
% 31.50/4.48  --prep_sem_filter                       exhaustive
% 31.50/4.48  --prep_sem_filter_out                   false
% 31.50/4.48  --pred_elim                             true
% 31.50/4.48  --res_sim_input                         true
% 31.50/4.48  --eq_ax_congr_red                       true
% 31.50/4.48  --pure_diseq_elim                       true
% 31.50/4.48  --brand_transform                       false
% 31.50/4.48  --non_eq_to_eq                          false
% 31.50/4.48  --prep_def_merge                        true
% 31.50/4.48  --prep_def_merge_prop_impl              false
% 31.50/4.48  --prep_def_merge_mbd                    true
% 31.50/4.48  --prep_def_merge_tr_red                 false
% 31.50/4.48  --prep_def_merge_tr_cl                  false
% 31.50/4.48  --smt_preprocessing                     true
% 31.50/4.48  --smt_ac_axioms                         fast
% 31.50/4.48  --preprocessed_out                      false
% 31.50/4.48  --preprocessed_stats                    false
% 31.50/4.48  
% 31.50/4.48  ------ Abstraction refinement Options
% 31.50/4.48  
% 31.50/4.48  --abstr_ref                             []
% 31.50/4.48  --abstr_ref_prep                        false
% 31.50/4.48  --abstr_ref_until_sat                   false
% 31.50/4.48  --abstr_ref_sig_restrict                funpre
% 31.50/4.48  --abstr_ref_af_restrict_to_split_sk     false
% 31.50/4.48  --abstr_ref_under                       []
% 31.50/4.48  
% 31.50/4.48  ------ SAT Options
% 31.50/4.48  
% 31.50/4.48  --sat_mode                              false
% 31.50/4.48  --sat_fm_restart_options                ""
% 31.50/4.48  --sat_gr_def                            false
% 31.50/4.48  --sat_epr_types                         true
% 31.50/4.48  --sat_non_cyclic_types                  false
% 31.50/4.48  --sat_finite_models                     false
% 31.50/4.48  --sat_fm_lemmas                         false
% 31.50/4.48  --sat_fm_prep                           false
% 31.50/4.48  --sat_fm_uc_incr                        true
% 31.50/4.48  --sat_out_model                         small
% 31.50/4.48  --sat_out_clauses                       false
% 31.50/4.48  
% 31.50/4.48  ------ QBF Options
% 31.50/4.48  
% 31.50/4.48  --qbf_mode                              false
% 31.50/4.48  --qbf_elim_univ                         false
% 31.50/4.48  --qbf_dom_inst                          none
% 31.50/4.48  --qbf_dom_pre_inst                      false
% 31.50/4.48  --qbf_sk_in                             false
% 31.50/4.48  --qbf_pred_elim                         true
% 31.50/4.48  --qbf_split                             512
% 31.50/4.48  
% 31.50/4.48  ------ BMC1 Options
% 31.50/4.48  
% 31.50/4.48  --bmc1_incremental                      false
% 31.50/4.48  --bmc1_axioms                           reachable_all
% 31.50/4.48  --bmc1_min_bound                        0
% 31.50/4.48  --bmc1_max_bound                        -1
% 31.50/4.48  --bmc1_max_bound_default                -1
% 31.50/4.48  --bmc1_symbol_reachability              true
% 31.50/4.48  --bmc1_property_lemmas                  false
% 31.50/4.48  --bmc1_k_induction                      false
% 31.50/4.48  --bmc1_non_equiv_states                 false
% 31.50/4.48  --bmc1_deadlock                         false
% 31.50/4.48  --bmc1_ucm                              false
% 31.50/4.48  --bmc1_add_unsat_core                   none
% 31.50/4.48  --bmc1_unsat_core_children              false
% 31.50/4.48  --bmc1_unsat_core_extrapolate_axioms    false
% 31.50/4.48  --bmc1_out_stat                         full
% 31.50/4.48  --bmc1_ground_init                      false
% 31.50/4.48  --bmc1_pre_inst_next_state              false
% 31.50/4.48  --bmc1_pre_inst_state                   false
% 31.50/4.48  --bmc1_pre_inst_reach_state             false
% 31.50/4.48  --bmc1_out_unsat_core                   false
% 31.50/4.48  --bmc1_aig_witness_out                  false
% 31.50/4.48  --bmc1_verbose                          false
% 31.50/4.48  --bmc1_dump_clauses_tptp                false
% 31.50/4.48  --bmc1_dump_unsat_core_tptp             false
% 31.50/4.48  --bmc1_dump_file                        -
% 31.50/4.48  --bmc1_ucm_expand_uc_limit              128
% 31.50/4.48  --bmc1_ucm_n_expand_iterations          6
% 31.50/4.48  --bmc1_ucm_extend_mode                  1
% 31.50/4.48  --bmc1_ucm_init_mode                    2
% 31.50/4.48  --bmc1_ucm_cone_mode                    none
% 31.50/4.48  --bmc1_ucm_reduced_relation_type        0
% 31.50/4.48  --bmc1_ucm_relax_model                  4
% 31.50/4.48  --bmc1_ucm_full_tr_after_sat            true
% 31.50/4.48  --bmc1_ucm_expand_neg_assumptions       false
% 31.50/4.48  --bmc1_ucm_layered_model                none
% 31.50/4.48  --bmc1_ucm_max_lemma_size               10
% 31.50/4.48  
% 31.50/4.48  ------ AIG Options
% 31.50/4.48  
% 31.50/4.48  --aig_mode                              false
% 31.50/4.48  
% 31.50/4.48  ------ Instantiation Options
% 31.50/4.48  
% 31.50/4.48  --instantiation_flag                    true
% 31.50/4.48  --inst_sos_flag                         true
% 31.50/4.48  --inst_sos_phase                        true
% 31.50/4.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.50/4.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.50/4.48  --inst_lit_sel_side                     num_symb
% 31.50/4.48  --inst_solver_per_active                1400
% 31.50/4.48  --inst_solver_calls_frac                1.
% 31.50/4.48  --inst_passive_queue_type               priority_queues
% 31.50/4.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.50/4.48  --inst_passive_queues_freq              [25;2]
% 31.50/4.48  --inst_dismatching                      true
% 31.50/4.48  --inst_eager_unprocessed_to_passive     true
% 31.50/4.48  --inst_prop_sim_given                   true
% 31.50/4.48  --inst_prop_sim_new                     false
% 31.50/4.48  --inst_subs_new                         false
% 31.50/4.49  --inst_eq_res_simp                      false
% 31.50/4.49  --inst_subs_given                       false
% 31.50/4.49  --inst_orphan_elimination               true
% 31.50/4.49  --inst_learning_loop_flag               true
% 31.50/4.49  --inst_learning_start                   3000
% 31.50/4.49  --inst_learning_factor                  2
% 31.50/4.49  --inst_start_prop_sim_after_learn       3
% 31.50/4.49  --inst_sel_renew                        solver
% 31.50/4.49  --inst_lit_activity_flag                true
% 31.50/4.49  --inst_restr_to_given                   false
% 31.50/4.49  --inst_activity_threshold               500
% 31.50/4.49  --inst_out_proof                        true
% 31.50/4.49  
% 31.50/4.49  ------ Resolution Options
% 31.50/4.49  
% 31.50/4.49  --resolution_flag                       true
% 31.50/4.49  --res_lit_sel                           adaptive
% 31.50/4.49  --res_lit_sel_side                      none
% 31.50/4.49  --res_ordering                          kbo
% 31.50/4.49  --res_to_prop_solver                    active
% 31.50/4.49  --res_prop_simpl_new                    false
% 31.50/4.49  --res_prop_simpl_given                  true
% 31.50/4.49  --res_passive_queue_type                priority_queues
% 31.50/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.50/4.49  --res_passive_queues_freq               [15;5]
% 31.50/4.49  --res_forward_subs                      full
% 31.50/4.49  --res_backward_subs                     full
% 31.50/4.49  --res_forward_subs_resolution           true
% 31.50/4.49  --res_backward_subs_resolution          true
% 31.50/4.49  --res_orphan_elimination                true
% 31.50/4.49  --res_time_limit                        2.
% 31.50/4.49  --res_out_proof                         true
% 31.50/4.49  
% 31.50/4.49  ------ Superposition Options
% 31.50/4.49  
% 31.50/4.49  --superposition_flag                    true
% 31.50/4.49  --sup_passive_queue_type                priority_queues
% 31.50/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.50/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.50/4.49  --demod_completeness_check              fast
% 31.50/4.49  --demod_use_ground                      true
% 31.50/4.49  --sup_to_prop_solver                    passive
% 31.50/4.49  --sup_prop_simpl_new                    true
% 31.50/4.49  --sup_prop_simpl_given                  true
% 31.50/4.49  --sup_fun_splitting                     true
% 31.50/4.49  --sup_smt_interval                      50000
% 31.50/4.49  
% 31.50/4.49  ------ Superposition Simplification Setup
% 31.50/4.49  
% 31.50/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.50/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.50/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.50/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.50/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.50/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.50/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.50/4.49  --sup_immed_triv                        [TrivRules]
% 31.50/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.50/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.50/4.49  --sup_immed_bw_main                     []
% 31.50/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.50/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.50/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.50/4.49  --sup_input_bw                          []
% 31.50/4.49  
% 31.50/4.49  ------ Combination Options
% 31.50/4.49  
% 31.50/4.49  --comb_res_mult                         3
% 31.50/4.49  --comb_sup_mult                         2
% 31.50/4.49  --comb_inst_mult                        10
% 31.50/4.49  
% 31.50/4.49  ------ Debug Options
% 31.50/4.49  
% 31.50/4.49  --dbg_backtrace                         false
% 31.50/4.49  --dbg_dump_prop_clauses                 false
% 31.50/4.49  --dbg_dump_prop_clauses_file            -
% 31.50/4.49  --dbg_out_stat                          false
% 31.50/4.49  ------ Parsing...
% 31.50/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.50/4.49  
% 31.50/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 31.50/4.49  
% 31.50/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.50/4.49  
% 31.50/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.50/4.49  ------ Proving...
% 31.50/4.49  ------ Problem Properties 
% 31.50/4.49  
% 31.50/4.49  
% 31.50/4.49  clauses                                 21
% 31.50/4.49  conjectures                             2
% 31.50/4.49  EPR                                     5
% 31.50/4.49  Horn                                    16
% 31.50/4.49  unary                                   9
% 31.50/4.49  binary                                  6
% 31.50/4.49  lits                                    40
% 31.50/4.49  lits eq                                 12
% 31.50/4.49  fd_pure                                 0
% 31.50/4.49  fd_pseudo                               0
% 31.50/4.49  fd_cond                                 0
% 31.50/4.49  fd_pseudo_cond                          5
% 31.50/4.49  AC symbols                              0
% 31.50/4.49  
% 31.50/4.49  ------ Schedule dynamic 5 is on 
% 31.50/4.49  
% 31.50/4.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.50/4.49  
% 31.50/4.49  
% 31.50/4.49  ------ 
% 31.50/4.49  Current options:
% 31.50/4.49  ------ 
% 31.50/4.49  
% 31.50/4.49  ------ Input Options
% 31.50/4.49  
% 31.50/4.49  --out_options                           all
% 31.50/4.49  --tptp_safe_out                         true
% 31.50/4.49  --problem_path                          ""
% 31.50/4.49  --include_path                          ""
% 31.50/4.49  --clausifier                            res/vclausify_rel
% 31.50/4.49  --clausifier_options                    ""
% 31.50/4.49  --stdin                                 false
% 31.50/4.49  --stats_out                             all
% 31.50/4.49  
% 31.50/4.49  ------ General Options
% 31.50/4.49  
% 31.50/4.49  --fof                                   false
% 31.50/4.49  --time_out_real                         305.
% 31.50/4.49  --time_out_virtual                      -1.
% 31.50/4.49  --symbol_type_check                     false
% 31.50/4.49  --clausify_out                          false
% 31.50/4.49  --sig_cnt_out                           false
% 31.50/4.49  --trig_cnt_out                          false
% 31.50/4.49  --trig_cnt_out_tolerance                1.
% 31.50/4.49  --trig_cnt_out_sk_spl                   false
% 31.50/4.49  --abstr_cl_out                          false
% 31.50/4.49  
% 31.50/4.49  ------ Global Options
% 31.50/4.49  
% 31.50/4.49  --schedule                              default
% 31.50/4.49  --add_important_lit                     false
% 31.50/4.49  --prop_solver_per_cl                    1000
% 31.50/4.49  --min_unsat_core                        false
% 31.50/4.49  --soft_assumptions                      false
% 31.50/4.49  --soft_lemma_size                       3
% 31.50/4.49  --prop_impl_unit_size                   0
% 31.50/4.49  --prop_impl_unit                        []
% 31.50/4.49  --share_sel_clauses                     true
% 31.50/4.49  --reset_solvers                         false
% 31.50/4.49  --bc_imp_inh                            [conj_cone]
% 31.50/4.49  --conj_cone_tolerance                   3.
% 31.50/4.49  --extra_neg_conj                        none
% 31.50/4.49  --large_theory_mode                     true
% 31.50/4.49  --prolific_symb_bound                   200
% 31.50/4.49  --lt_threshold                          2000
% 31.50/4.49  --clause_weak_htbl                      true
% 31.50/4.49  --gc_record_bc_elim                     false
% 31.50/4.49  
% 31.50/4.49  ------ Preprocessing Options
% 31.50/4.49  
% 31.50/4.49  --preprocessing_flag                    true
% 31.50/4.49  --time_out_prep_mult                    0.1
% 31.50/4.49  --splitting_mode                        input
% 31.50/4.49  --splitting_grd                         true
% 31.50/4.49  --splitting_cvd                         false
% 31.50/4.49  --splitting_cvd_svl                     false
% 31.50/4.49  --splitting_nvd                         32
% 31.50/4.49  --sub_typing                            true
% 31.50/4.49  --prep_gs_sim                           true
% 31.50/4.49  --prep_unflatten                        true
% 31.50/4.49  --prep_res_sim                          true
% 31.50/4.49  --prep_upred                            true
% 31.50/4.49  --prep_sem_filter                       exhaustive
% 31.50/4.49  --prep_sem_filter_out                   false
% 31.50/4.49  --pred_elim                             true
% 31.50/4.49  --res_sim_input                         true
% 31.50/4.49  --eq_ax_congr_red                       true
% 31.50/4.49  --pure_diseq_elim                       true
% 31.50/4.49  --brand_transform                       false
% 31.50/4.49  --non_eq_to_eq                          false
% 31.50/4.49  --prep_def_merge                        true
% 31.50/4.49  --prep_def_merge_prop_impl              false
% 31.50/4.49  --prep_def_merge_mbd                    true
% 31.50/4.49  --prep_def_merge_tr_red                 false
% 31.50/4.49  --prep_def_merge_tr_cl                  false
% 31.50/4.49  --smt_preprocessing                     true
% 31.50/4.49  --smt_ac_axioms                         fast
% 31.50/4.49  --preprocessed_out                      false
% 31.50/4.49  --preprocessed_stats                    false
% 31.50/4.49  
% 31.50/4.49  ------ Abstraction refinement Options
% 31.50/4.49  
% 31.50/4.49  --abstr_ref                             []
% 31.50/4.49  --abstr_ref_prep                        false
% 31.50/4.49  --abstr_ref_until_sat                   false
% 31.50/4.49  --abstr_ref_sig_restrict                funpre
% 31.50/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.50/4.49  --abstr_ref_under                       []
% 31.50/4.49  
% 31.50/4.49  ------ SAT Options
% 31.50/4.49  
% 31.50/4.49  --sat_mode                              false
% 31.50/4.49  --sat_fm_restart_options                ""
% 31.50/4.49  --sat_gr_def                            false
% 31.50/4.49  --sat_epr_types                         true
% 31.50/4.49  --sat_non_cyclic_types                  false
% 31.50/4.49  --sat_finite_models                     false
% 31.50/4.49  --sat_fm_lemmas                         false
% 31.50/4.49  --sat_fm_prep                           false
% 31.50/4.49  --sat_fm_uc_incr                        true
% 31.50/4.49  --sat_out_model                         small
% 31.50/4.49  --sat_out_clauses                       false
% 31.50/4.49  
% 31.50/4.49  ------ QBF Options
% 31.50/4.49  
% 31.50/4.49  --qbf_mode                              false
% 31.50/4.49  --qbf_elim_univ                         false
% 31.50/4.49  --qbf_dom_inst                          none
% 31.50/4.49  --qbf_dom_pre_inst                      false
% 31.50/4.49  --qbf_sk_in                             false
% 31.50/4.49  --qbf_pred_elim                         true
% 31.50/4.49  --qbf_split                             512
% 31.50/4.49  
% 31.50/4.49  ------ BMC1 Options
% 31.50/4.49  
% 31.50/4.49  --bmc1_incremental                      false
% 31.50/4.49  --bmc1_axioms                           reachable_all
% 31.50/4.49  --bmc1_min_bound                        0
% 31.50/4.49  --bmc1_max_bound                        -1
% 31.50/4.49  --bmc1_max_bound_default                -1
% 31.50/4.49  --bmc1_symbol_reachability              true
% 31.50/4.49  --bmc1_property_lemmas                  false
% 31.50/4.49  --bmc1_k_induction                      false
% 31.50/4.49  --bmc1_non_equiv_states                 false
% 31.50/4.49  --bmc1_deadlock                         false
% 31.50/4.49  --bmc1_ucm                              false
% 31.50/4.49  --bmc1_add_unsat_core                   none
% 31.50/4.49  --bmc1_unsat_core_children              false
% 31.50/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.50/4.49  --bmc1_out_stat                         full
% 31.50/4.49  --bmc1_ground_init                      false
% 31.50/4.49  --bmc1_pre_inst_next_state              false
% 31.50/4.49  --bmc1_pre_inst_state                   false
% 31.50/4.49  --bmc1_pre_inst_reach_state             false
% 31.50/4.49  --bmc1_out_unsat_core                   false
% 31.50/4.49  --bmc1_aig_witness_out                  false
% 31.50/4.49  --bmc1_verbose                          false
% 31.50/4.49  --bmc1_dump_clauses_tptp                false
% 31.50/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.50/4.49  --bmc1_dump_file                        -
% 31.50/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.50/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.50/4.49  --bmc1_ucm_extend_mode                  1
% 31.50/4.49  --bmc1_ucm_init_mode                    2
% 31.50/4.49  --bmc1_ucm_cone_mode                    none
% 31.50/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.50/4.49  --bmc1_ucm_relax_model                  4
% 31.50/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.50/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.50/4.49  --bmc1_ucm_layered_model                none
% 31.50/4.49  --bmc1_ucm_max_lemma_size               10
% 31.50/4.49  
% 31.50/4.49  ------ AIG Options
% 31.50/4.49  
% 31.50/4.49  --aig_mode                              false
% 31.50/4.49  
% 31.50/4.49  ------ Instantiation Options
% 31.50/4.49  
% 31.50/4.49  --instantiation_flag                    true
% 31.50/4.49  --inst_sos_flag                         true
% 31.50/4.49  --inst_sos_phase                        true
% 31.50/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.50/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.50/4.49  --inst_lit_sel_side                     none
% 31.50/4.49  --inst_solver_per_active                1400
% 31.50/4.49  --inst_solver_calls_frac                1.
% 31.50/4.49  --inst_passive_queue_type               priority_queues
% 31.50/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.50/4.49  --inst_passive_queues_freq              [25;2]
% 31.50/4.49  --inst_dismatching                      true
% 31.50/4.49  --inst_eager_unprocessed_to_passive     true
% 31.50/4.49  --inst_prop_sim_given                   true
% 31.50/4.49  --inst_prop_sim_new                     false
% 31.50/4.49  --inst_subs_new                         false
% 31.50/4.49  --inst_eq_res_simp                      false
% 31.50/4.49  --inst_subs_given                       false
% 31.50/4.49  --inst_orphan_elimination               true
% 31.50/4.49  --inst_learning_loop_flag               true
% 31.50/4.49  --inst_learning_start                   3000
% 31.50/4.49  --inst_learning_factor                  2
% 31.50/4.49  --inst_start_prop_sim_after_learn       3
% 31.50/4.49  --inst_sel_renew                        solver
% 31.50/4.49  --inst_lit_activity_flag                true
% 31.50/4.49  --inst_restr_to_given                   false
% 31.50/4.49  --inst_activity_threshold               500
% 31.50/4.49  --inst_out_proof                        true
% 31.50/4.49  
% 31.50/4.49  ------ Resolution Options
% 31.50/4.49  
% 31.50/4.49  --resolution_flag                       false
% 31.50/4.49  --res_lit_sel                           adaptive
% 31.50/4.49  --res_lit_sel_side                      none
% 31.50/4.49  --res_ordering                          kbo
% 31.50/4.49  --res_to_prop_solver                    active
% 31.50/4.49  --res_prop_simpl_new                    false
% 31.50/4.49  --res_prop_simpl_given                  true
% 31.50/4.49  --res_passive_queue_type                priority_queues
% 31.50/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.50/4.49  --res_passive_queues_freq               [15;5]
% 31.50/4.49  --res_forward_subs                      full
% 31.50/4.49  --res_backward_subs                     full
% 31.50/4.49  --res_forward_subs_resolution           true
% 31.50/4.49  --res_backward_subs_resolution          true
% 31.50/4.49  --res_orphan_elimination                true
% 31.50/4.49  --res_time_limit                        2.
% 31.50/4.49  --res_out_proof                         true
% 31.50/4.49  
% 31.50/4.49  ------ Superposition Options
% 31.50/4.49  
% 31.50/4.49  --superposition_flag                    true
% 31.50/4.49  --sup_passive_queue_type                priority_queues
% 31.50/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.50/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.50/4.49  --demod_completeness_check              fast
% 31.50/4.49  --demod_use_ground                      true
% 31.50/4.49  --sup_to_prop_solver                    passive
% 31.50/4.49  --sup_prop_simpl_new                    true
% 31.50/4.49  --sup_prop_simpl_given                  true
% 31.50/4.49  --sup_fun_splitting                     true
% 31.50/4.49  --sup_smt_interval                      50000
% 31.50/4.49  
% 31.50/4.49  ------ Superposition Simplification Setup
% 31.50/4.49  
% 31.50/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.50/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.50/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.50/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.50/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.50/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.50/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.50/4.49  --sup_immed_triv                        [TrivRules]
% 31.50/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.50/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.50/4.49  --sup_immed_bw_main                     []
% 31.50/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.50/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.50/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.50/4.49  --sup_input_bw                          []
% 31.50/4.49  
% 31.50/4.49  ------ Combination Options
% 31.50/4.49  
% 31.50/4.49  --comb_res_mult                         3
% 31.50/4.49  --comb_sup_mult                         2
% 31.50/4.49  --comb_inst_mult                        10
% 31.50/4.49  
% 31.50/4.49  ------ Debug Options
% 31.50/4.49  
% 31.50/4.49  --dbg_backtrace                         false
% 31.50/4.49  --dbg_dump_prop_clauses                 false
% 31.50/4.49  --dbg_dump_prop_clauses_file            -
% 31.50/4.49  --dbg_out_stat                          false
% 31.50/4.49  
% 31.50/4.49  
% 31.50/4.49  
% 31.50/4.49  
% 31.50/4.49  ------ Proving...
% 31.50/4.49  
% 31.50/4.49  
% 31.50/4.49  % SZS status Theorem for theBenchmark.p
% 31.50/4.49  
% 31.50/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.50/4.49  
% 31.50/4.49  fof(f1,axiom,(
% 31.50/4.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f37,plain,(
% 31.50/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 31.50/4.49    inference(cnf_transformation,[],[f1])).
% 31.50/4.49  
% 31.50/4.49  fof(f3,axiom,(
% 31.50/4.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f28,plain,(
% 31.50/4.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 31.50/4.49    inference(nnf_transformation,[],[f3])).
% 31.50/4.49  
% 31.50/4.49  fof(f29,plain,(
% 31.50/4.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 31.50/4.49    inference(flattening,[],[f28])).
% 31.50/4.49  
% 31.50/4.49  fof(f30,plain,(
% 31.50/4.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 31.50/4.49    inference(rectify,[],[f29])).
% 31.50/4.49  
% 31.50/4.49  fof(f31,plain,(
% 31.50/4.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 31.50/4.49    introduced(choice_axiom,[])).
% 31.50/4.49  
% 31.50/4.49  fof(f32,plain,(
% 31.50/4.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 31.50/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 31.50/4.49  
% 31.50/4.49  fof(f44,plain,(
% 31.50/4.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 31.50/4.49    inference(cnf_transformation,[],[f32])).
% 31.50/4.49  
% 31.50/4.49  fof(f5,axiom,(
% 31.50/4.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f50,plain,(
% 31.50/4.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 31.50/4.49    inference(cnf_transformation,[],[f5])).
% 31.50/4.49  
% 31.50/4.49  fof(f71,plain,(
% 31.50/4.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 31.50/4.49    inference(definition_unfolding,[],[f44,f50])).
% 31.50/4.49  
% 31.50/4.49  fof(f11,axiom,(
% 31.50/4.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f56,plain,(
% 31.50/4.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 31.50/4.49    inference(cnf_transformation,[],[f11])).
% 31.50/4.49  
% 31.50/4.49  fof(f8,axiom,(
% 31.50/4.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f53,plain,(
% 31.50/4.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 31.50/4.49    inference(cnf_transformation,[],[f8])).
% 31.50/4.49  
% 31.50/4.49  fof(f12,axiom,(
% 31.50/4.49    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f57,plain,(
% 31.50/4.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 31.50/4.49    inference(cnf_transformation,[],[f12])).
% 31.50/4.49  
% 31.50/4.49  fof(f65,plain,(
% 31.50/4.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 31.50/4.49    inference(definition_unfolding,[],[f57,f50])).
% 31.50/4.49  
% 31.50/4.49  fof(f75,plain,(
% 31.50/4.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)))) )),
% 31.50/4.49    inference(definition_unfolding,[],[f53,f65,f65,f50])).
% 31.50/4.49  
% 31.50/4.49  fof(f9,axiom,(
% 31.50/4.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f54,plain,(
% 31.50/4.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 31.50/4.49    inference(cnf_transformation,[],[f9])).
% 31.50/4.49  
% 31.50/4.49  fof(f7,axiom,(
% 31.50/4.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f52,plain,(
% 31.50/4.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 31.50/4.49    inference(cnf_transformation,[],[f7])).
% 31.50/4.49  
% 31.50/4.49  fof(f6,axiom,(
% 31.50/4.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f21,plain,(
% 31.50/4.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 31.50/4.49    inference(ennf_transformation,[],[f6])).
% 31.50/4.49  
% 31.50/4.49  fof(f51,plain,(
% 31.50/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 31.50/4.49    inference(cnf_transformation,[],[f21])).
% 31.50/4.49  
% 31.50/4.49  fof(f42,plain,(
% 31.50/4.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 31.50/4.49    inference(cnf_transformation,[],[f32])).
% 31.50/4.49  
% 31.50/4.49  fof(f73,plain,(
% 31.50/4.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 31.50/4.49    inference(definition_unfolding,[],[f42,f50])).
% 31.50/4.49  
% 31.50/4.49  fof(f80,plain,(
% 31.50/4.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 31.50/4.49    inference(equality_resolution,[],[f73])).
% 31.50/4.49  
% 31.50/4.49  fof(f4,axiom,(
% 31.50/4.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f33,plain,(
% 31.50/4.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.50/4.49    inference(nnf_transformation,[],[f4])).
% 31.50/4.49  
% 31.50/4.49  fof(f34,plain,(
% 31.50/4.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.50/4.49    inference(flattening,[],[f33])).
% 31.50/4.49  
% 31.50/4.49  fof(f47,plain,(
% 31.50/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 31.50/4.49    inference(cnf_transformation,[],[f34])).
% 31.50/4.49  
% 31.50/4.49  fof(f83,plain,(
% 31.50/4.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 31.50/4.49    inference(equality_resolution,[],[f47])).
% 31.50/4.49  
% 31.50/4.49  fof(f41,plain,(
% 31.50/4.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 31.50/4.49    inference(cnf_transformation,[],[f32])).
% 31.50/4.49  
% 31.50/4.49  fof(f74,plain,(
% 31.50/4.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 31.50/4.49    inference(definition_unfolding,[],[f41,f50])).
% 31.50/4.49  
% 31.50/4.49  fof(f81,plain,(
% 31.50/4.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 31.50/4.49    inference(equality_resolution,[],[f74])).
% 31.50/4.49  
% 31.50/4.49  fof(f18,conjecture,(
% 31.50/4.49    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f19,negated_conjecture,(
% 31.50/4.49    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 31.50/4.49    inference(negated_conjecture,[],[f18])).
% 31.50/4.49  
% 31.50/4.49  fof(f23,plain,(
% 31.50/4.49    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 31.50/4.49    inference(ennf_transformation,[],[f19])).
% 31.50/4.49  
% 31.50/4.49  fof(f35,plain,(
% 31.50/4.49    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2))),
% 31.50/4.49    introduced(choice_axiom,[])).
% 31.50/4.49  
% 31.50/4.49  fof(f36,plain,(
% 31.50/4.49    sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 31.50/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f35])).
% 31.50/4.49  
% 31.50/4.49  fof(f63,plain,(
% 31.50/4.49    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 31.50/4.49    inference(cnf_transformation,[],[f36])).
% 31.50/4.49  
% 31.50/4.49  fof(f13,axiom,(
% 31.50/4.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f58,plain,(
% 31.50/4.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 31.50/4.49    inference(cnf_transformation,[],[f13])).
% 31.50/4.49  
% 31.50/4.49  fof(f14,axiom,(
% 31.50/4.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f59,plain,(
% 31.50/4.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 31.50/4.49    inference(cnf_transformation,[],[f14])).
% 31.50/4.49  
% 31.50/4.49  fof(f15,axiom,(
% 31.50/4.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f60,plain,(
% 31.50/4.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 31.50/4.49    inference(cnf_transformation,[],[f15])).
% 31.50/4.49  
% 31.50/4.49  fof(f16,axiom,(
% 31.50/4.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f61,plain,(
% 31.50/4.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 31.50/4.49    inference(cnf_transformation,[],[f16])).
% 31.50/4.49  
% 31.50/4.49  fof(f66,plain,(
% 31.50/4.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 31.50/4.49    inference(definition_unfolding,[],[f60,f61])).
% 31.50/4.49  
% 31.50/4.49  fof(f67,plain,(
% 31.50/4.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 31.50/4.49    inference(definition_unfolding,[],[f59,f66])).
% 31.50/4.49  
% 31.50/4.49  fof(f68,plain,(
% 31.50/4.49    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 31.50/4.49    inference(definition_unfolding,[],[f58,f67])).
% 31.50/4.49  
% 31.50/4.49  fof(f78,plain,(
% 31.50/4.49    k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)),
% 31.50/4.49    inference(definition_unfolding,[],[f63,f65,f68,f68,f68])).
% 31.50/4.49  
% 31.50/4.49  fof(f10,axiom,(
% 31.50/4.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f55,plain,(
% 31.50/4.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 31.50/4.49    inference(cnf_transformation,[],[f10])).
% 31.50/4.49  
% 31.50/4.49  fof(f76,plain,(
% 31.50/4.49    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 31.50/4.49    inference(definition_unfolding,[],[f55,f65])).
% 31.50/4.49  
% 31.50/4.49  fof(f2,axiom,(
% 31.50/4.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f20,plain,(
% 31.50/4.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 31.50/4.49    inference(ennf_transformation,[],[f2])).
% 31.50/4.49  
% 31.50/4.49  fof(f24,plain,(
% 31.50/4.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 31.50/4.49    inference(nnf_transformation,[],[f20])).
% 31.50/4.49  
% 31.50/4.49  fof(f25,plain,(
% 31.50/4.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 31.50/4.49    inference(rectify,[],[f24])).
% 31.50/4.49  
% 31.50/4.49  fof(f26,plain,(
% 31.50/4.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 31.50/4.49    introduced(choice_axiom,[])).
% 31.50/4.49  
% 31.50/4.49  fof(f27,plain,(
% 31.50/4.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 31.50/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 31.50/4.49  
% 31.50/4.49  fof(f39,plain,(
% 31.50/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 31.50/4.49    inference(cnf_transformation,[],[f27])).
% 31.50/4.49  
% 31.50/4.49  fof(f40,plain,(
% 31.50/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 31.50/4.49    inference(cnf_transformation,[],[f27])).
% 31.50/4.49  
% 31.50/4.49  fof(f17,axiom,(
% 31.50/4.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 31.50/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.50/4.49  
% 31.50/4.49  fof(f22,plain,(
% 31.50/4.49    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 31.50/4.49    inference(ennf_transformation,[],[f17])).
% 31.50/4.49  
% 31.50/4.49  fof(f62,plain,(
% 31.50/4.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1))) )),
% 31.50/4.49    inference(cnf_transformation,[],[f22])).
% 31.50/4.49  
% 31.50/4.49  fof(f77,plain,(
% 31.50/4.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) )),
% 31.50/4.49    inference(definition_unfolding,[],[f62,f68,f68])).
% 31.50/4.49  
% 31.50/4.49  fof(f64,plain,(
% 31.50/4.49    sK2 != sK3),
% 31.50/4.49    inference(cnf_transformation,[],[f36])).
% 31.50/4.49  
% 31.50/4.49  cnf(c_0,plain,
% 31.50/4.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 31.50/4.49      inference(cnf_transformation,[],[f37]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_6,plain,
% 31.50/4.49      ( r2_hidden(sK1(X0,X1,X2),X0)
% 31.50/4.49      | r2_hidden(sK1(X0,X1,X2),X2)
% 31.50/4.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 31.50/4.49      inference(cnf_transformation,[],[f71]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_540,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 31.50/4.49      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 31.50/4.49      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 31.50/4.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_18,plain,
% 31.50/4.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 31.50/4.49      inference(cnf_transformation,[],[f56]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_15,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 31.50/4.49      inference(cnf_transformation,[],[f75]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1108,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_18,c_15]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_7237,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_0,c_1108]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_16,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 31.50/4.49      inference(cnf_transformation,[],[f54]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_935,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_16,c_18]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_8660,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))))) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_7237,c_935]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_14,plain,
% 31.50/4.49      ( r1_tarski(k1_xboole_0,X0) ),
% 31.50/4.49      inference(cnf_transformation,[],[f52]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_533,plain,
% 31.50/4.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 31.50/4.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_13,plain,
% 31.50/4.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 31.50/4.49      inference(cnf_transformation,[],[f51]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_534,plain,
% 31.50/4.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 31.50/4.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1882,plain,
% 31.50/4.49      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_533,c_534]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_8700,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 31.50/4.49      inference(light_normalisation,[status(thm)],[c_8660,c_1882]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_8701,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_8700,c_16,c_935]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_8,plain,
% 31.50/4.49      ( ~ r2_hidden(X0,X1)
% 31.50/4.49      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 31.50/4.49      inference(cnf_transformation,[],[f80]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_538,plain,
% 31.50/4.49      ( r2_hidden(X0,X1) != iProver_top
% 31.50/4.49      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 31.50/4.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_3203,plain,
% 31.50/4.49      ( r2_hidden(X0,X1) != iProver_top
% 31.50/4.49      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X1,X2))) != iProver_top ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_0,c_538]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_8861,plain,
% 31.50/4.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_8701,c_3203]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_33924,plain,
% 31.50/4.49      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = X1
% 31.50/4.49      | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_540,c_8861]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_33926,plain,
% 31.50/4.49      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = X0
% 31.50/4.49      | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 31.50/4.49      inference(light_normalisation,[status(thm)],[c_33924,c_1882]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_33927,plain,
% 31.50/4.49      ( k1_xboole_0 = X0
% 31.50/4.49      | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_33926,c_16]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_12,plain,
% 31.50/4.49      ( r1_tarski(X0,X0) ),
% 31.50/4.49      inference(cnf_transformation,[],[f83]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_535,plain,
% 31.50/4.49      ( r1_tarski(X0,X0) = iProver_top ),
% 31.50/4.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1881,plain,
% 31.50/4.49      ( k3_xboole_0(X0,X0) = X0 ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_535,c_534]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_9,plain,
% 31.50/4.49      ( r2_hidden(X0,X1)
% 31.50/4.49      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 31.50/4.49      inference(cnf_transformation,[],[f81]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_537,plain,
% 31.50/4.49      ( r2_hidden(X0,X1) = iProver_top
% 31.50/4.49      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 31.50/4.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_2834,plain,
% 31.50/4.49      ( r2_hidden(X0,X1) = iProver_top
% 31.50/4.49      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))) != iProver_top ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_0,c_537]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_30091,plain,
% 31.50/4.49      ( r2_hidden(X0,X1) = iProver_top
% 31.50/4.49      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_1881,c_2834]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_30090,plain,
% 31.50/4.49      ( r2_hidden(X0,X1) != iProver_top
% 31.50/4.49      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_1881,c_538]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_38027,plain,
% 31.50/4.49      ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 31.50/4.49      inference(global_propositional_subsumption,
% 31.50/4.49                [status(thm)],
% 31.50/4.49                [c_30091,c_30090]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_38036,plain,
% 31.50/4.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_33927,c_38027]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1185,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_935,c_18]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1186,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_1185,c_935]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_38588,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_38036,c_18]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_38957,plain,
% 31.50/4.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k1_xboole_0,X2) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_1186,c_38588]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_38980,plain,
% 31.50/4.49      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_38036,c_38588]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_39262,plain,
% 31.50/4.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 31.50/4.49      inference(light_normalisation,[status(thm)],[c_38980,c_16]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_39501,plain,
% 31.50/4.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_38957,c_1186,c_39262]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47628,plain,
% 31.50/4.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k1_xboole_0) = X1 ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_38036,c_39501]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47714,plain,
% 31.50/4.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),X2) = k5_xboole_0(X1,X2) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_39501,c_39501]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47754,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_47714,c_1186]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_39011,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = k5_xboole_0(k1_xboole_0,X2) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_38588,c_1186]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_39443,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k5_xboole_0(k1_xboole_0,X2) ),
% 31.50/4.49      inference(light_normalisation,[status(thm)],[c_39011,c_1186]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_39444,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_39443,c_39262]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47425,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_39444,c_39444]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47549,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = sP0_iProver_split(X1,X2) ),
% 31.50/4.49      inference(splitting,
% 31.50/4.49                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 31.50/4.49                [c_47425]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47755,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,X1) = k5_xboole_0(X0,X1) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_47754,c_1186,c_47549]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48586,plain,
% 31.50/4.49      ( k5_xboole_0(k5_xboole_0(sP0_iProver_split(X0,X1),X0),k1_xboole_0) = X1 ),
% 31.50/4.49      inference(light_normalisation,[status(thm)],[c_47628,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48587,plain,
% 31.50/4.49      ( sP0_iProver_split(sP0_iProver_split(X0,X1),X0) = X1 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_48586,c_16,c_1186,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47666,plain,
% 31.50/4.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k1_xboole_0)) = X1 ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_38036,c_39501]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48454,plain,
% 31.50/4.49      ( k5_xboole_0(sP0_iProver_split(X0,X1),X0) = X1 ),
% 31.50/4.49      inference(light_normalisation,[status(thm)],[c_47666,c_16,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_39263,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_39262,c_38588]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_51790,plain,
% 31.50/4.49      ( k5_xboole_0(sP0_iProver_split(X0,X1),X1) = X0 ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_48454,c_39263]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_53502,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,X1) = k5_xboole_0(X1,X0) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_48587,c_51790]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_21,negated_conjecture,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 31.50/4.49      inference(cnf_transformation,[],[f78]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_826,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_0,c_21]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_936,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),X0)) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),X0) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_826,c_18]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1333,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),X0) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_936,c_1186]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_17,plain,
% 31.50/4.49      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 31.50/4.49      inference(cnf_transformation,[],[f76]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_532,plain,
% 31.50/4.49      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
% 31.50/4.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1196,plain,
% 31.50/4.49      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = iProver_top ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_0,c_532]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1318,plain,
% 31.50/4.49      ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X0,X1),X2))))) = iProver_top ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_18,c_1196]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_4029,plain,
% 31.50/4.49      ( r1_tarski(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = iProver_top ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_1333,c_1318]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_4387,plain,
% 31.50/4.49      ( k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_4029,c_534]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54513,plain,
% 31.50/4.49      ( k3_xboole_0(sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_53502,c_4387]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_7274,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_1108,c_1333]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_7289,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_7274,c_1333]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_7392,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_0,c_7289]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54521,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = sP0_iProver_split(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_53502,c_7392]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_38606,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_xboole_0)) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_38036,c_1333]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_38656,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_38606,c_16]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_44173,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_38656,c_39263]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_44421,plain,
% 31.50/4.49      ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_44173,c_39263]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54522,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = sP0_iProver_split(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 31.50/4.49      inference(light_normalisation,[status(thm)],[c_54521,c_44421]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54523,plain,
% 31.50/4.49      ( sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sP0_iProver_split(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_54522,c_1881,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1335,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_15,c_1333]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1343,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_1335,c_1333]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1344,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_1343,c_1186]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1473,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_0,c_1344]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1494,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0)))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_0,c_1473]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1700,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))))),X1)) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),X1) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_1494,c_18]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1703,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0)))),X1))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),X1))) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_1700,c_1186]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1704,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))),X1)))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),X1))) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_1703,c_1186]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_38610,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0)))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k1_xboole_0))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_38036,c_1704]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_38654,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0)))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_38610,c_16]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_41655,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0)))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_0,c_38654]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47657,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))))) = k5_xboole_0(k5_xboole_0(X1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X1,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_41655,c_39501]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48493,plain,
% 31.50/4.49      ( k5_xboole_0(k5_xboole_0(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X1,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1))))) = k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X1,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1))))) ),
% 31.50/4.49      inference(light_normalisation,[status(thm)],[c_47657,c_44421]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_8628,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_0,c_7237]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_44172,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_8628,c_39263]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_44450,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_44172,c_39263]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48494,plain,
% 31.50/4.49      ( sP0_iProver_split(sP0_iProver_split(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sP0_iProver_split(X0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X1,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1))))) = sP0_iProver_split(X1,k3_xboole_0(X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 31.50/4.49      inference(demodulation,
% 31.50/4.49                [status(thm)],
% 31.50/4.49                [c_48493,c_1186,c_44450,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47759,plain,
% 31.50/4.49      ( k5_xboole_0(sP0_iProver_split(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_47755,c_39501]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47784,plain,
% 31.50/4.49      ( sP0_iProver_split(sP0_iProver_split(X0,X1),sP0_iProver_split(X0,k5_xboole_0(X1,X2))) = X2 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_47759,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47785,plain,
% 31.50/4.49      ( sP0_iProver_split(sP0_iProver_split(X0,X1),sP0_iProver_split(X0,sP0_iProver_split(X1,X2))) = X2 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_47784,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48495,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,k3_xboole_0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(X0,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_48494,c_47755,c_47785]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54524,plain,
% 31.50/4.49      ( sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_54523,c_1881,c_48495]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_7390,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_0,c_7289]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_7505,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_0,c_7390]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47634,plain,
% 31.50/4.49      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_7505,c_39501]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48562,plain,
% 31.50/4.49      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sP0_iProver_split(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_47634,c_48495]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48563,plain,
% 31.50/4.49      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) ),
% 31.50/4.49      inference(light_normalisation,[status(thm)],[c_48562,c_44421]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48564,plain,
% 31.50/4.49      ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
% 31.50/4.49      inference(demodulation,
% 31.50/4.49                [status(thm)],
% 31.50/4.49                [c_48563,c_1186,c_1881,c_38036,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47672,plain,
% 31.50/4.49      ( k5_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) = k5_xboole_0(k5_xboole_0(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_7505,c_39501]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47677,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))))) = k5_xboole_0(k5_xboole_0(X1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X1,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_38654,c_39501]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_44175,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0)))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_38654,c_39263]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_44419,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0))))) = k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0)) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_44175,c_39263]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_44423,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0))))) = k5_xboole_0(X0,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_44421,c_44419]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48412,plain,
% 31.50/4.49      ( k5_xboole_0(k5_xboole_0(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X1,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1))))) = k5_xboole_0(X1,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1)) ),
% 31.50/4.49      inference(light_normalisation,
% 31.50/4.49                [status(thm)],
% 31.50/4.49                [c_47677,c_44421,c_44423]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48413,plain,
% 31.50/4.49      ( sP0_iProver_split(sP0_iProver_split(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sP0_iProver_split(X0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X1,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1))))) = sP0_iProver_split(X1,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1)) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_48412,c_1186,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48414,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)) = k5_xboole_0(X0,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_48413,c_47755,c_47785]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48426,plain,
% 31.50/4.49      ( k5_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sP0_iProver_split(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) = k5_xboole_0(k5_xboole_0(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_47672,c_48414]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48427,plain,
% 31.50/4.49      ( k5_xboole_0(k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = k5_xboole_0(k5_xboole_0(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(X0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
% 31.50/4.49      inference(light_normalisation,[status(thm)],[c_48426,c_44421]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48428,plain,
% 31.50/4.49      ( sP0_iProver_split(sP0_iProver_split(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sP0_iProver_split(X0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) ),
% 31.50/4.49      inference(demodulation,
% 31.50/4.49                [status(thm)],
% 31.50/4.49                [c_48427,c_1186,c_1881,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48429,plain,
% 31.50/4.49      ( sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_48428,c_47755,c_47785]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48430,plain,
% 31.50/4.49      ( sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_48429,c_1881]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48565,plain,
% 31.50/4.49      ( sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_xboole_0) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_48564,c_48430]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_51786,plain,
% 31.50/4.49      ( sP0_iProver_split(k1_xboole_0,X0) = X0 ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_16,c_48454]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_52605,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,k1_xboole_0) = X0 ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_51786,c_48587]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_53054,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,X0) = k1_xboole_0 ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_52605,c_48587]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54525,plain,
% 31.50/4.49      ( sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 31.50/4.49      inference(demodulation,
% 31.50/4.49                [status(thm)],
% 31.50/4.49                [c_54524,c_1881,c_1882,c_48565,c_53054]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54548,plain,
% 31.50/4.49      ( k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_54513,c_54525]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1475,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_18,c_1344]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1483,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_1475,c_1186]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1751,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_1483,c_1333]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1752,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_1751,c_1333]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1872,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_1752,c_1483]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1876,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_1872,c_1752]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1877,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))))) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_1876,c_1186]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1878,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))))) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_1877,c_1186]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_38959,plain,
% 31.50/4.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_826,c_38588]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_39500,plain,
% 31.50/4.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k1_xboole_0 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_38959,c_38036,c_39262]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_40343,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_39500,c_39262]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54154,plain,
% 31.50/4.49      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))))) = k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) ),
% 31.50/4.49      inference(light_normalisation,
% 31.50/4.49                [status(thm)],
% 31.50/4.49                [c_1878,c_1878,c_40343,c_44421]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47551,plain,
% 31.50/4.49      ( k5_xboole_0(X0,sP0_iProver_split(X0,X1)) = X1 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_47549,c_39444]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54155,plain,
% 31.50/4.49      ( k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))) = sP0_iProver_split(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 31.50/4.49      inference(demodulation,
% 31.50/4.49                [status(thm)],
% 31.50/4.49                [c_54154,c_1882,c_39262,c_39263,c_47551,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54156,plain,
% 31.50/4.49      ( sP0_iProver_split(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = sP0_iProver_split(k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 31.50/4.49      inference(demodulation,
% 31.50/4.49                [status(thm)],
% 31.50/4.49                [c_54155,c_1882,c_39262,c_39263,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54157,plain,
% 31.50/4.49      ( sP0_iProver_split(k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sP0_iProver_split(k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 31.50/4.49      inference(demodulation,
% 31.50/4.49                [status(thm)],
% 31.50/4.49                [c_54156,c_1882,c_39263,c_44421,c_47755,c_51786,c_52605]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54158,plain,
% 31.50/4.49      ( sP0_iProver_split(k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 31.50/4.49      inference(demodulation,
% 31.50/4.49                [status(thm)],
% 31.50/4.49                [c_54157,c_1882,c_47755,c_51786]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54159,plain,
% 31.50/4.49      ( sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sP0_iProver_split(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 31.50/4.49      inference(demodulation,
% 31.50/4.49                [status(thm)],
% 31.50/4.49                [c_54158,c_1882,c_44421,c_47755,c_52605]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54160,plain,
% 31.50/4.49      ( sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sP0_iProver_split(k3_xboole_0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 31.50/4.49      inference(demodulation,
% 31.50/4.49                [status(thm)],
% 31.50/4.49                [c_54159,c_1882,c_47755,c_51786]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54161,plain,
% 31.50/4.49      ( sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sP0_iProver_split(k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_54160,c_39263,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54162,plain,
% 31.50/4.49      ( sP0_iProver_split(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 31.50/4.49      inference(demodulation,
% 31.50/4.49                [status(thm)],
% 31.50/4.49                [c_54161,c_1882,c_44421,c_51786,c_52605]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54167,plain,
% 31.50/4.49      ( k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_54162,c_48454]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54172,plain,
% 31.50/4.49      ( k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_54167,c_38036]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54549,plain,
% 31.50/4.49      ( k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_xboole_0)) = sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 31.50/4.49      inference(light_normalisation,
% 31.50/4.49                [status(thm)],
% 31.50/4.49                [c_54548,c_44421,c_54172]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_54550,plain,
% 31.50/4.49      ( k3_xboole_0(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_54549,c_16]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_55207,plain,
% 31.50/4.49      ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_0,c_54550]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_2,plain,
% 31.50/4.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 31.50/4.49      inference(cnf_transformation,[],[f39]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_544,plain,
% 31.50/4.49      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 31.50/4.49      | r1_tarski(X0,X1) = iProver_top ),
% 31.50/4.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_2832,plain,
% 31.50/4.49      ( r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X0) = iProver_top
% 31.50/4.49      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_544,c_537]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47673,plain,
% 31.50/4.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_8628,c_39501]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48423,plain,
% 31.50/4.49      ( k5_xboole_0(sP0_iProver_split(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))) ),
% 31.50/4.49      inference(light_normalisation,[status(thm)],[c_47673,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48424,plain,
% 31.50/4.49      ( sP0_iProver_split(sP0_iProver_split(X0,X1),sP0_iProver_split(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = sP0_iProver_split(X2,k3_xboole_0(X2,X1)) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_48423,c_44450,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48425,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_48424,c_47755,c_47785]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_65865,plain,
% 31.50/4.49      ( r2_hidden(sK0(sP0_iProver_split(X0,k3_xboole_0(X0,X1)),X2),X0) = iProver_top
% 31.50/4.49      | r1_tarski(sP0_iProver_split(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
% 31.50/4.49      inference(light_normalisation,[status(thm)],[c_2832,c_48425]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_1,plain,
% 31.50/4.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 31.50/4.49      inference(cnf_transformation,[],[f40]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_545,plain,
% 31.50/4.49      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 31.50/4.49      | r1_tarski(X0,X1) = iProver_top ),
% 31.50/4.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_65896,plain,
% 31.50/4.49      ( r1_tarski(sP0_iProver_split(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_65865,c_545]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_66327,plain,
% 31.50/4.49      ( r1_tarski(sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sP0_iProver_split(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_55207,c_65896]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47422,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2))),X3)) = k5_xboole_0(X2,X3) ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_39444,c_18]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_49161,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3))) = sP0_iProver_split(X2,X3) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_47422,c_1186,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_49162,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3))) = sP0_iProver_split(X2,X3) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_49161,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_49163,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)))) = sP0_iProver_split(X2,X3) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_49162,c_1186]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_49164,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)))) = sP0_iProver_split(X2,X3) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_49163,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_49165,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))))) = sP0_iProver_split(X2,X3) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_49164,c_1186]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_49166,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X2,X3))))) = sP0_iProver_split(X2,X3) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_49165,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_49167,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,X3))))) = sP0_iProver_split(X2,X3) ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_49166,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_47680,plain,
% 31.50/4.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),X3))) = X3 ),
% 31.50/4.49      inference(superposition,[status(thm)],[c_39501,c_39501]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48401,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),X3)))) = X3 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_47680,c_1186,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48402,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),X3)))) = X3 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_48401,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48403,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),X3)))) = X3 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_48402,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48404,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X0),X3))))) = X3 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_48403,c_1186]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48405,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,sP0_iProver_split(X1,k5_xboole_0(k5_xboole_0(X2,X0),X3))))) = X3 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_48404,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48406,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,sP0_iProver_split(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3)))))) = X3 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_48405,c_1186]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48407,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,sP0_iProver_split(X1,sP0_iProver_split(X2,k5_xboole_0(X0,X3)))))) = X3 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_48406,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_48408,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,sP0_iProver_split(X1,sP0_iProver_split(X2,sP0_iProver_split(X0,X3)))))) = X3 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_48407,c_47755]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_49182,plain,
% 31.50/4.49      ( sP0_iProver_split(X0,sP0_iProver_split(X0,X1)) = X1 ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_49167,c_48408]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_66349,plain,
% 31.50/4.49      ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 31.50/4.49      inference(demodulation,[status(thm)],[c_66327,c_49182]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_19,plain,
% 31.50/4.49      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))
% 31.50/4.49      | X1 = X0 ),
% 31.50/4.49      inference(cnf_transformation,[],[f77]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_561,plain,
% 31.50/4.49      ( ~ r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 31.50/4.49      | sK2 = sK3 ),
% 31.50/4.49      inference(instantiation,[status(thm)],[c_19]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_565,plain,
% 31.50/4.49      ( sK2 = sK3
% 31.50/4.49      | r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 31.50/4.49      inference(predicate_to_equality,[status(thm)],[c_561]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(c_20,negated_conjecture,
% 31.50/4.49      ( sK2 != sK3 ),
% 31.50/4.49      inference(cnf_transformation,[],[f64]) ).
% 31.50/4.49  
% 31.50/4.49  cnf(contradiction,plain,
% 31.50/4.49      ( $false ),
% 31.50/4.49      inference(minisat,[status(thm)],[c_66349,c_565,c_20]) ).
% 31.50/4.49  
% 31.50/4.49  
% 31.50/4.49  % SZS output end CNFRefutation for theBenchmark.p
% 31.50/4.49  
% 31.50/4.49  ------                               Statistics
% 31.50/4.49  
% 31.50/4.49  ------ General
% 31.50/4.49  
% 31.50/4.49  abstr_ref_over_cycles:                  0
% 31.50/4.49  abstr_ref_under_cycles:                 0
% 31.50/4.49  gc_basic_clause_elim:                   0
% 31.50/4.49  forced_gc_time:                         0
% 31.50/4.49  parsing_time:                           0.006
% 31.50/4.49  unif_index_cands_time:                  0.
% 31.50/4.49  unif_index_add_time:                    0.
% 31.50/4.49  orderings_time:                         0.
% 31.50/4.49  out_proof_time:                         0.026
% 31.50/4.49  total_time:                             3.51
% 31.50/4.49  num_of_symbols:                         42
% 31.50/4.49  num_of_terms:                           148047
% 31.50/4.49  
% 31.50/4.49  ------ Preprocessing
% 31.50/4.49  
% 31.50/4.49  num_of_splits:                          0
% 31.50/4.49  num_of_split_atoms:                     1
% 31.50/4.49  num_of_reused_defs:                     0
% 31.50/4.49  num_eq_ax_congr_red:                    15
% 31.50/4.49  num_of_sem_filtered_clauses:            1
% 31.50/4.49  num_of_subtypes:                        0
% 31.50/4.49  monotx_restored_types:                  0
% 31.50/4.49  sat_num_of_epr_types:                   0
% 31.50/4.49  sat_num_of_non_cyclic_types:            0
% 31.50/4.49  sat_guarded_non_collapsed_types:        0
% 31.50/4.49  num_pure_diseq_elim:                    0
% 31.50/4.49  simp_replaced_by:                       0
% 31.50/4.49  res_preprocessed:                       99
% 31.50/4.49  prep_upred:                             0
% 31.50/4.49  prep_unflattend:                        0
% 31.50/4.49  smt_new_axioms:                         0
% 31.50/4.49  pred_elim_cands:                        2
% 31.50/4.49  pred_elim:                              0
% 31.50/4.49  pred_elim_cl:                           0
% 31.50/4.49  pred_elim_cycles:                       2
% 31.50/4.49  merged_defs:                            0
% 31.50/4.49  merged_defs_ncl:                        0
% 31.50/4.49  bin_hyper_res:                          0
% 31.50/4.49  prep_cycles:                            4
% 31.50/4.49  pred_elim_time:                         0.
% 31.50/4.49  splitting_time:                         0.
% 31.50/4.49  sem_filter_time:                        0.
% 31.50/4.49  monotx_time:                            0.
% 31.50/4.49  subtype_inf_time:                       0.
% 31.50/4.49  
% 31.50/4.49  ------ Problem properties
% 31.50/4.49  
% 31.50/4.49  clauses:                                21
% 31.50/4.49  conjectures:                            2
% 31.50/4.49  epr:                                    5
% 31.50/4.49  horn:                                   16
% 31.50/4.49  ground:                                 2
% 31.50/4.49  unary:                                  9
% 31.50/4.49  binary:                                 6
% 31.50/4.49  lits:                                   40
% 31.50/4.49  lits_eq:                                12
% 31.50/4.49  fd_pure:                                0
% 31.50/4.49  fd_pseudo:                              0
% 31.50/4.49  fd_cond:                                0
% 31.50/4.49  fd_pseudo_cond:                         5
% 31.50/4.49  ac_symbols:                             0
% 31.50/4.49  
% 31.50/4.49  ------ Propositional Solver
% 31.50/4.49  
% 31.50/4.49  prop_solver_calls:                      33
% 31.50/4.49  prop_fast_solver_calls:                 1184
% 31.50/4.49  smt_solver_calls:                       0
% 31.50/4.49  smt_fast_solver_calls:                  0
% 31.50/4.49  prop_num_of_clauses:                    19803
% 31.50/4.49  prop_preprocess_simplified:             28531
% 31.50/4.49  prop_fo_subsumed:                       3
% 31.50/4.49  prop_solver_time:                       0.
% 31.50/4.49  smt_solver_time:                        0.
% 31.50/4.49  smt_fast_solver_time:                   0.
% 31.50/4.49  prop_fast_solver_time:                  0.
% 31.50/4.49  prop_unsat_core_time:                   0.001
% 31.50/4.49  
% 31.50/4.49  ------ QBF
% 31.50/4.49  
% 31.50/4.49  qbf_q_res:                              0
% 31.50/4.49  qbf_num_tautologies:                    0
% 31.50/4.49  qbf_prep_cycles:                        0
% 31.50/4.49  
% 31.50/4.49  ------ BMC1
% 31.50/4.49  
% 31.50/4.49  bmc1_current_bound:                     -1
% 31.50/4.49  bmc1_last_solved_bound:                 -1
% 31.50/4.49  bmc1_unsat_core_size:                   -1
% 31.50/4.49  bmc1_unsat_core_parents_size:           -1
% 31.50/4.49  bmc1_merge_next_fun:                    0
% 31.50/4.49  bmc1_unsat_core_clauses_time:           0.
% 31.50/4.49  
% 31.50/4.49  ------ Instantiation
% 31.50/4.49  
% 31.50/4.49  inst_num_of_clauses:                    3783
% 31.50/4.49  inst_num_in_passive:                    1556
% 31.50/4.49  inst_num_in_active:                     1241
% 31.50/4.49  inst_num_in_unprocessed:                986
% 31.50/4.49  inst_num_of_loops:                      1660
% 31.50/4.49  inst_num_of_learning_restarts:          0
% 31.50/4.49  inst_num_moves_active_passive:          418
% 31.50/4.49  inst_lit_activity:                      0
% 31.50/4.49  inst_lit_activity_moves:                1
% 31.50/4.49  inst_num_tautologies:                   0
% 31.50/4.49  inst_num_prop_implied:                  0
% 31.50/4.49  inst_num_existing_simplified:           0
% 31.50/4.49  inst_num_eq_res_simplified:             0
% 31.50/4.49  inst_num_child_elim:                    0
% 31.50/4.49  inst_num_of_dismatching_blockings:      3557
% 31.50/4.49  inst_num_of_non_proper_insts:           4384
% 31.50/4.49  inst_num_of_duplicates:                 0
% 31.50/4.49  inst_inst_num_from_inst_to_res:         0
% 31.50/4.49  inst_dismatching_checking_time:         0.
% 31.50/4.49  
% 31.50/4.49  ------ Resolution
% 31.50/4.49  
% 31.50/4.49  res_num_of_clauses:                     0
% 31.50/4.49  res_num_in_passive:                     0
% 31.50/4.49  res_num_in_active:                      0
% 31.50/4.49  res_num_of_loops:                       103
% 31.50/4.49  res_forward_subset_subsumed:            499
% 31.50/4.49  res_backward_subset_subsumed:           0
% 31.50/4.49  res_forward_subsumed:                   0
% 31.50/4.49  res_backward_subsumed:                  0
% 31.50/4.49  res_forward_subsumption_resolution:     0
% 31.50/4.49  res_backward_subsumption_resolution:    0
% 31.50/4.49  res_clause_to_clause_subsumption:       27256
% 31.50/4.49  res_orphan_elimination:                 0
% 31.50/4.49  res_tautology_del:                      388
% 31.50/4.49  res_num_eq_res_simplified:              0
% 31.50/4.49  res_num_sel_changes:                    0
% 31.50/4.49  res_moves_from_active_to_pass:          0
% 31.50/4.49  
% 31.50/4.49  ------ Superposition
% 31.50/4.49  
% 31.50/4.49  sup_time_total:                         0.
% 31.50/4.49  sup_time_generating:                    0.
% 31.50/4.49  sup_time_sim_full:                      0.
% 31.50/4.49  sup_time_sim_immed:                     0.
% 31.50/4.49  
% 31.50/4.49  sup_num_of_clauses:                     3266
% 31.50/4.49  sup_num_in_active:                      90
% 31.50/4.49  sup_num_in_passive:                     3176
% 31.50/4.49  sup_num_of_loops:                       331
% 31.50/4.49  sup_fw_superposition:                   5984
% 31.50/4.49  sup_bw_superposition:                   7097
% 31.50/4.49  sup_immediate_simplified:               9561
% 31.50/4.49  sup_given_eliminated:                   12
% 31.50/4.49  comparisons_done:                       0
% 31.50/4.49  comparisons_avoided:                    0
% 31.50/4.49  
% 31.50/4.49  ------ Simplifications
% 31.50/4.49  
% 31.50/4.49  
% 31.50/4.49  sim_fw_subset_subsumed:                 13
% 31.50/4.49  sim_bw_subset_subsumed:                 13
% 31.50/4.49  sim_fw_subsumed:                        1020
% 31.50/4.49  sim_bw_subsumed:                        59
% 31.50/4.49  sim_fw_subsumption_res:                 0
% 31.50/4.49  sim_bw_subsumption_res:                 0
% 31.50/4.49  sim_tautology_del:                      57
% 31.50/4.49  sim_eq_tautology_del:                   1077
% 31.50/4.49  sim_eq_res_simp:                        1
% 31.50/4.49  sim_fw_demodulated:                     15451
% 31.50/4.49  sim_bw_demodulated:                     865
% 31.50/4.49  sim_light_normalised:                   2326
% 31.50/4.49  sim_joinable_taut:                      0
% 31.50/4.49  sim_joinable_simp:                      0
% 31.50/4.49  sim_ac_normalised:                      0
% 31.50/4.49  sim_smt_subsumption:                    0
% 31.50/4.49  
%------------------------------------------------------------------------------
