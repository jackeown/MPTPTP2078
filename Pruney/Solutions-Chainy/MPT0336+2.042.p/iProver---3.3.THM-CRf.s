%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:40 EST 2020

% Result     : Theorem 7.74s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 688 expanded)
%              Number of clauses        :   93 ( 218 expanded)
%              Number of leaves         :   21 ( 177 expanded)
%              Depth                    :   27
%              Number of atoms          :  408 (2009 expanded)
%              Number of equality atoms :  124 ( 446 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f21])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
      & r1_xboole_0(sK4,sK3)
      & r2_hidden(sK5,sK4)
      & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f33])).

fof(f60,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f64])).

fof(f70,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f60,f65])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f29])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f59,f48,f65])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f54,f48])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f48])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_327,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
    | k3_xboole_0(X1,X0) = X1
    | k3_xboole_0(sK2,sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_328,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1087,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1093,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3318,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),X2) = iProver_top
    | r2_hidden(sK1(k3_xboole_0(X0,X1),X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1087,c_1093])).

cnf(c_19609,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),X2) = iProver_top
    | r2_hidden(sK1(k3_xboole_0(X1,X0),X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3318])).

cnf(c_19781,plain,
    ( r1_xboole_0(k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)),X0) = iProver_top
    | r2_hidden(sK1(k3_xboole_0(sK2,sK3),X0),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_328,c_19609])).

cnf(c_545,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_541,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4351,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_545,c_541])).

cnf(c_542,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3074,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_542,c_541])).

cnf(c_6031,plain,
    ( k3_xboole_0(sK2,sK3) = k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(resolution,[status(thm)],[c_3074,c_328])).

cnf(c_8118,plain,
    ( ~ r1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)),X0)
    | r1_xboole_0(k3_xboole_0(sK2,sK3),X0) ),
    inference(resolution,[status(thm)],[c_4351,c_6031])).

cnf(c_8119,plain,
    ( r1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)),X0) != iProver_top
    | r1_xboole_0(k3_xboole_0(sK2,sK3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8118])).

cnf(c_3066,plain,
    ( X0 != k3_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) = X0 ),
    inference(resolution,[status(thm)],[c_542,c_0])).

cnf(c_10013,plain,
    ( k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)) = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_3066,c_6031])).

cnf(c_10706,plain,
    ( r1_xboole_0(k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)),X0)
    | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),X0) ),
    inference(resolution,[status(thm)],[c_10013,c_4351])).

cnf(c_10707,plain,
    ( r1_xboole_0(k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)),X0) = iProver_top
    | r1_xboole_0(k3_xboole_0(sK2,sK3),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10706])).

cnf(c_8106,plain,
    ( r1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)),X0)
    | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),X0) ),
    inference(resolution,[status(thm)],[c_4351,c_328])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1642,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X0)
    | ~ r2_hidden(sK1(X2,X0),X1) ),
    inference(resolution,[status(thm)],[c_10,c_11])).

cnf(c_2685,plain,
    ( ~ r1_xboole_0(X0,X0)
    | r1_xboole_0(X1,X0) ),
    inference(resolution,[status(thm)],[c_1642,c_11])).

cnf(c_8697,plain,
    ( r1_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)))
    | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(resolution,[status(thm)],[c_8106,c_2685])).

cnf(c_22,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_555,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_544,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6694,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)))
    | r2_hidden(X1,k3_xboole_0(sK2,sK3))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_6031,c_544])).

cnf(c_6700,plain,
    ( ~ r2_hidden(sK5,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)))
    | r2_hidden(sK5,k3_xboole_0(sK2,sK3))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_6694])).

cnf(c_4355,plain,
    ( r1_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)))
    | ~ r1_xboole_0(X1,k3_xboole_0(sK2,sK3))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_545,c_328])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1405,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),X2)
    | r2_hidden(sK1(k3_xboole_0(X0,X1),X2),X1) ),
    inference(resolution,[status(thm)],[c_5,c_12])).

cnf(c_2690,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X2,X1),X0) ),
    inference(resolution,[status(thm)],[c_1642,c_1405])).

cnf(c_4781,plain,
    ( r1_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)))
    | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),X1)
    | X0 != k3_xboole_0(X2,X1) ),
    inference(resolution,[status(thm)],[c_4355,c_2690])).

cnf(c_6704,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))
    | r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(resolution,[status(thm)],[c_6031,c_4781])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_17,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3085,plain,
    ( r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))
    | r2_hidden(X1,X0) ),
    inference(resolution,[status(thm)],[c_19,c_17])).

cnf(c_8984,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(X0,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(resolution,[status(thm)],[c_8118,c_3085])).

cnf(c_8986,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK5,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_8984])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_8683,plain,
    ( r1_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)))
    | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),X0) ),
    inference(resolution,[status(thm)],[c_8106,c_9])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1646,plain,
    ( ~ r1_xboole_0(sK4,X0)
    | ~ r2_hidden(sK5,X0) ),
    inference(resolution,[status(thm)],[c_10,c_23])).

cnf(c_9008,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK3),sK4)
    | ~ r2_hidden(sK5,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(resolution,[status(thm)],[c_8683,c_1646])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_9181,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK3),sK4)
    | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_9008,c_4])).

cnf(c_3397,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)))
    | ~ r2_hidden(X1,k3_xboole_0(sK2,sK3))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_544,c_328])).

cnf(c_3399,plain,
    ( r2_hidden(sK5,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)))
    | ~ r2_hidden(sK5,k3_xboole_0(sK2,sK3))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3397])).

cnf(c_9361,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK3),sK4)
    | ~ r2_hidden(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9181,c_555,c_3399,c_9008])).

cnf(c_9506,plain,
    ( ~ r1_xboole_0(sK4,sK3)
    | ~ r2_hidden(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_9361,c_2690])).

cnf(c_13864,plain,
    ( r1_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8697,c_22,c_555,c_6700,c_6704,c_8986,c_9506])).

cnf(c_13894,plain,
    ( r1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)),X0) ),
    inference(resolution,[status(thm)],[c_13864,c_9])).

cnf(c_13895,plain,
    ( r1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13894])).

cnf(c_20719,plain,
    ( r1_xboole_0(k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19781,c_8119,c_10707,c_13895])).

cnf(c_20726,plain,
    ( r1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_20719])).

cnf(c_20752,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,sK3),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20726,c_328])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1091,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_20770,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20752,c_1091])).

cnf(c_20864,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20770,c_328])).

cnf(c_1083,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2652,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1083])).

cnf(c_20951,plain,
    ( k5_xboole_0(sK3,k1_xboole_0) != sK3
    | r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_20864,c_2652])).

cnf(c_1078,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1090,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1393,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_1090])).

cnf(c_18,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1082,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1605,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = sK3 ),
    inference(superposition,[status(thm)],[c_1393,c_1082])).

cnf(c_1467,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1393,c_1091])).

cnf(c_2647,plain,
    ( k5_xboole_0(sK3,k1_xboole_0) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_1605,c_1467])).

cnf(c_20975,plain,
    ( sK3 != sK3
    | r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20951,c_2647])).

cnf(c_20976,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_20975])).

cnf(c_16,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1446,plain,
    ( ~ r1_xboole_0(sK3,X0)
    | r1_xboole_0(sK3,k2_xboole_0(X0,sK4))
    | ~ r1_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6866,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
    | ~ r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_6867,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = iProver_top
    | r1_xboole_0(sK3,sK4) != iProver_top
    | r1_xboole_0(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6866])).

cnf(c_2192,plain,
    ( r1_xboole_0(k2_xboole_0(X0,sK4),sK3)
    | ~ r1_xboole_0(sK3,k2_xboole_0(X0,sK4)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4265,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_2192])).

cnf(c_4266,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) = iProver_top
    | r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4265])).

cnf(c_1260,plain,
    ( r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1261,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top
    | r1_xboole_0(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1260])).

cnf(c_21,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_28,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_27,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20976,c_6867,c_4266,c_1261,c_28,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:41:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.74/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/1.48  
% 7.74/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.74/1.48  
% 7.74/1.48  ------  iProver source info
% 7.74/1.48  
% 7.74/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.74/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.74/1.48  git: non_committed_changes: false
% 7.74/1.48  git: last_make_outside_of_git: false
% 7.74/1.48  
% 7.74/1.48  ------ 
% 7.74/1.48  ------ Parsing...
% 7.74/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.74/1.48  
% 7.74/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.74/1.48  
% 7.74/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.74/1.48  
% 7.74/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.74/1.48  ------ Proving...
% 7.74/1.48  ------ Problem Properties 
% 7.74/1.48  
% 7.74/1.48  
% 7.74/1.48  clauses                                 24
% 7.74/1.48  conjectures                             3
% 7.74/1.48  EPR                                     4
% 7.74/1.48  Horn                                    19
% 7.74/1.48  unary                                   5
% 7.74/1.48  binary                                  13
% 7.74/1.48  lits                                    50
% 7.74/1.48  lits eq                                 11
% 7.74/1.48  fd_pure                                 0
% 7.74/1.48  fd_pseudo                               0
% 7.74/1.48  fd_cond                                 0
% 7.74/1.48  fd_pseudo_cond                          3
% 7.74/1.48  AC symbols                              0
% 7.74/1.48  
% 7.74/1.48  ------ Input Options Time Limit: Unbounded
% 7.74/1.48  
% 7.74/1.48  
% 7.74/1.48  ------ 
% 7.74/1.48  Current options:
% 7.74/1.48  ------ 
% 7.74/1.48  
% 7.74/1.48  
% 7.74/1.48  
% 7.74/1.48  
% 7.74/1.48  ------ Proving...
% 7.74/1.48  
% 7.74/1.48  
% 7.74/1.48  % SZS status Theorem for theBenchmark.p
% 7.74/1.48  
% 7.74/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.74/1.48  
% 7.74/1.48  fof(f1,axiom,(
% 7.74/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.74/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.48  
% 7.74/1.48  fof(f35,plain,(
% 7.74/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.74/1.48    inference(cnf_transformation,[],[f1])).
% 7.74/1.48  
% 7.74/1.48  fof(f7,axiom,(
% 7.74/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.74/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.48  
% 7.74/1.48  fof(f19,plain,(
% 7.74/1.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.74/1.48    inference(ennf_transformation,[],[f7])).
% 7.74/1.48  
% 7.74/1.48  fof(f49,plain,(
% 7.74/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.74/1.48    inference(cnf_transformation,[],[f19])).
% 7.74/1.48  
% 7.74/1.48  fof(f14,conjecture,(
% 7.74/1.48    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.74/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.48  
% 7.74/1.48  fof(f15,negated_conjecture,(
% 7.74/1.48    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.74/1.48    inference(negated_conjecture,[],[f14])).
% 7.74/1.48  
% 7.74/1.48  fof(f21,plain,(
% 7.74/1.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 7.74/1.48    inference(ennf_transformation,[],[f15])).
% 7.74/1.48  
% 7.74/1.48  fof(f22,plain,(
% 7.74/1.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 7.74/1.48    inference(flattening,[],[f21])).
% 7.74/1.48  
% 7.74/1.48  fof(f33,plain,(
% 7.74/1.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 7.74/1.48    introduced(choice_axiom,[])).
% 7.74/1.48  
% 7.74/1.48  fof(f34,plain,(
% 7.74/1.48    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 7.74/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f33])).
% 7.74/1.48  
% 7.74/1.48  fof(f60,plain,(
% 7.74/1.48    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 7.74/1.48    inference(cnf_transformation,[],[f34])).
% 7.74/1.48  
% 7.74/1.48  fof(f10,axiom,(
% 7.74/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.74/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.48  
% 7.74/1.48  fof(f55,plain,(
% 7.74/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.74/1.48    inference(cnf_transformation,[],[f10])).
% 7.74/1.48  
% 7.74/1.48  fof(f11,axiom,(
% 7.74/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.74/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.48  
% 7.74/1.48  fof(f56,plain,(
% 7.74/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.74/1.48    inference(cnf_transformation,[],[f11])).
% 7.74/1.48  
% 7.74/1.48  fof(f12,axiom,(
% 7.74/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.74/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.48  
% 7.74/1.48  fof(f57,plain,(
% 7.74/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.74/1.48    inference(cnf_transformation,[],[f12])).
% 7.74/1.48  
% 7.74/1.48  fof(f64,plain,(
% 7.74/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.74/1.48    inference(definition_unfolding,[],[f56,f57])).
% 7.74/1.48  
% 7.74/1.48  fof(f65,plain,(
% 7.74/1.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.74/1.48    inference(definition_unfolding,[],[f55,f64])).
% 7.74/1.48  
% 7.74/1.48  fof(f70,plain,(
% 7.74/1.48    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))),
% 7.74/1.48    inference(definition_unfolding,[],[f60,f65])).
% 7.74/1.48  
% 7.74/1.48  fof(f5,axiom,(
% 7.74/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.74/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.48  
% 7.74/1.48  fof(f16,plain,(
% 7.74/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.74/1.48    inference(rectify,[],[f5])).
% 7.74/1.48  
% 7.74/1.48  fof(f18,plain,(
% 7.74/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.74/1.48    inference(ennf_transformation,[],[f16])).
% 7.74/1.48  
% 7.74/1.48  fof(f29,plain,(
% 7.74/1.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.74/1.48    introduced(choice_axiom,[])).
% 7.74/1.48  
% 7.74/1.48  fof(f30,plain,(
% 7.74/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.74/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f29])).
% 7.74/1.48  
% 7.74/1.48  fof(f45,plain,(
% 7.74/1.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.74/1.48    inference(cnf_transformation,[],[f30])).
% 7.74/1.48  
% 7.74/1.48  fof(f2,axiom,(
% 7.74/1.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.74/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.48  
% 7.74/1.48  fof(f23,plain,(
% 7.74/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.74/1.48    inference(nnf_transformation,[],[f2])).
% 7.74/1.48  
% 7.74/1.48  fof(f24,plain,(
% 7.74/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.74/1.48    inference(flattening,[],[f23])).
% 7.74/1.48  
% 7.74/1.48  fof(f25,plain,(
% 7.74/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.74/1.48    inference(rectify,[],[f24])).
% 7.74/1.48  
% 7.74/1.48  fof(f26,plain,(
% 7.74/1.48    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.74/1.48    introduced(choice_axiom,[])).
% 7.74/1.48  
% 7.74/1.48  fof(f27,plain,(
% 7.74/1.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.74/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 7.74/1.48  
% 7.74/1.48  fof(f36,plain,(
% 7.74/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 7.74/1.48    inference(cnf_transformation,[],[f27])).
% 7.74/1.48  
% 7.74/1.48  fof(f73,plain,(
% 7.74/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 7.74/1.48    inference(equality_resolution,[],[f36])).
% 7.74/1.48  
% 7.74/1.48  fof(f47,plain,(
% 7.74/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.74/1.48    inference(cnf_transformation,[],[f30])).
% 7.74/1.48  
% 7.74/1.48  fof(f46,plain,(
% 7.74/1.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.74/1.48    inference(cnf_transformation,[],[f30])).
% 7.74/1.48  
% 7.74/1.48  fof(f62,plain,(
% 7.74/1.48    r1_xboole_0(sK4,sK3)),
% 7.74/1.48    inference(cnf_transformation,[],[f34])).
% 7.74/1.48  
% 7.74/1.48  fof(f37,plain,(
% 7.74/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 7.74/1.48    inference(cnf_transformation,[],[f27])).
% 7.74/1.48  
% 7.74/1.48  fof(f72,plain,(
% 7.74/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 7.74/1.48    inference(equality_resolution,[],[f37])).
% 7.74/1.48  
% 7.74/1.48  fof(f13,axiom,(
% 7.74/1.48    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 7.74/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.48  
% 7.74/1.48  fof(f32,plain,(
% 7.74/1.48    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 7.74/1.48    inference(nnf_transformation,[],[f13])).
% 7.74/1.48  
% 7.74/1.48  fof(f59,plain,(
% 7.74/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 7.74/1.48    inference(cnf_transformation,[],[f32])).
% 7.74/1.48  
% 7.74/1.48  fof(f6,axiom,(
% 7.74/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.74/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.48  
% 7.74/1.48  fof(f48,plain,(
% 7.74/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.74/1.48    inference(cnf_transformation,[],[f6])).
% 7.74/1.48  
% 7.74/1.48  fof(f68,plain,(
% 7.74/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0 | r2_hidden(X1,X0)) )),
% 7.74/1.48    inference(definition_unfolding,[],[f59,f48,f65])).
% 7.74/1.48  
% 7.74/1.48  fof(f9,axiom,(
% 7.74/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.74/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.48  
% 7.74/1.48  fof(f31,plain,(
% 7.74/1.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 7.74/1.48    inference(nnf_transformation,[],[f9])).
% 7.74/1.48  
% 7.74/1.48  fof(f54,plain,(
% 7.74/1.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 7.74/1.48    inference(cnf_transformation,[],[f31])).
% 7.74/1.48  
% 7.74/1.48  fof(f66,plain,(
% 7.74/1.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0) )),
% 7.74/1.48    inference(definition_unfolding,[],[f54,f48])).
% 7.74/1.48  
% 7.74/1.48  fof(f4,axiom,(
% 7.74/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.74/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.48  
% 7.74/1.48  fof(f17,plain,(
% 7.74/1.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.74/1.48    inference(ennf_transformation,[],[f4])).
% 7.74/1.48  
% 7.74/1.48  fof(f44,plain,(
% 7.74/1.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.74/1.48    inference(cnf_transformation,[],[f17])).
% 7.74/1.48  
% 7.74/1.48  fof(f61,plain,(
% 7.74/1.48    r2_hidden(sK5,sK4)),
% 7.74/1.48    inference(cnf_transformation,[],[f34])).
% 7.74/1.48  
% 7.74/1.48  fof(f38,plain,(
% 7.74/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 7.74/1.48    inference(cnf_transformation,[],[f27])).
% 7.74/1.48  
% 7.74/1.48  fof(f71,plain,(
% 7.74/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.74/1.48    inference(equality_resolution,[],[f38])).
% 7.74/1.48  
% 7.74/1.48  fof(f3,axiom,(
% 7.74/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.74/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.48  
% 7.74/1.48  fof(f28,plain,(
% 7.74/1.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.74/1.48    inference(nnf_transformation,[],[f3])).
% 7.74/1.48  
% 7.74/1.48  fof(f42,plain,(
% 7.74/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.74/1.48    inference(cnf_transformation,[],[f28])).
% 7.74/1.48  
% 7.74/1.48  fof(f53,plain,(
% 7.74/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.74/1.48    inference(cnf_transformation,[],[f31])).
% 7.74/1.48  
% 7.74/1.48  fof(f67,plain,(
% 7.74/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.74/1.48    inference(definition_unfolding,[],[f53,f48])).
% 7.74/1.48  
% 7.74/1.48  fof(f8,axiom,(
% 7.74/1.48    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.74/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.48  
% 7.74/1.48  fof(f20,plain,(
% 7.74/1.48    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.74/1.48    inference(ennf_transformation,[],[f8])).
% 7.74/1.48  
% 7.74/1.48  fof(f50,plain,(
% 7.74/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 7.74/1.48    inference(cnf_transformation,[],[f20])).
% 7.74/1.48  
% 7.74/1.48  fof(f63,plain,(
% 7.74/1.48    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 7.74/1.48    inference(cnf_transformation,[],[f34])).
% 7.74/1.48  
% 7.74/1.48  cnf(c_0,plain,
% 7.74/1.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.74/1.48      inference(cnf_transformation,[],[f35]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_13,plain,
% 7.74/1.48      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.74/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_24,negated_conjecture,
% 7.74/1.48      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 7.74/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_327,plain,
% 7.74/1.48      ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
% 7.74/1.48      | k3_xboole_0(X1,X0) = X1
% 7.74/1.48      | k3_xboole_0(sK2,sK3) != X1 ),
% 7.74/1.48      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_328,plain,
% 7.74/1.48      ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
% 7.74/1.48      inference(unflattening,[status(thm)],[c_327]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_12,plain,
% 7.74/1.48      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.74/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_1087,plain,
% 7.74/1.48      ( r1_xboole_0(X0,X1) = iProver_top
% 7.74/1.48      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 7.74/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_6,plain,
% 7.74/1.48      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 7.74/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_1093,plain,
% 7.74/1.48      ( r2_hidden(X0,X1) = iProver_top
% 7.74/1.48      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 7.74/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_3318,plain,
% 7.74/1.48      ( r1_xboole_0(k3_xboole_0(X0,X1),X2) = iProver_top
% 7.74/1.48      | r2_hidden(sK1(k3_xboole_0(X0,X1),X2),X0) = iProver_top ),
% 7.74/1.48      inference(superposition,[status(thm)],[c_1087,c_1093]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_19609,plain,
% 7.74/1.48      ( r1_xboole_0(k3_xboole_0(X0,X1),X2) = iProver_top
% 7.74/1.48      | r2_hidden(sK1(k3_xboole_0(X1,X0),X2),X0) = iProver_top ),
% 7.74/1.48      inference(superposition,[status(thm)],[c_0,c_3318]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_19781,plain,
% 7.74/1.48      ( r1_xboole_0(k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)),X0) = iProver_top
% 7.74/1.48      | r2_hidden(sK1(k3_xboole_0(sK2,sK3),X0),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 7.74/1.48      inference(superposition,[status(thm)],[c_328,c_19609]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_545,plain,
% 7.74/1.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.74/1.48      theory(equality) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_541,plain,( X0 = X0 ),theory(equality) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_4351,plain,
% 7.74/1.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_545,c_541]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_542,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_3074,plain,
% 7.74/1.48      ( X0 != X1 | X1 = X0 ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_542,c_541]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_6031,plain,
% 7.74/1.48      ( k3_xboole_0(sK2,sK3) = k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_3074,c_328]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_8118,plain,
% 7.74/1.48      ( ~ r1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)),X0)
% 7.74/1.48      | r1_xboole_0(k3_xboole_0(sK2,sK3),X0) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_4351,c_6031]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_8119,plain,
% 7.74/1.48      ( r1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)),X0) != iProver_top
% 7.74/1.48      | r1_xboole_0(k3_xboole_0(sK2,sK3),X0) = iProver_top ),
% 7.74/1.48      inference(predicate_to_equality,[status(thm)],[c_8118]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_3066,plain,
% 7.74/1.48      ( X0 != k3_xboole_0(X1,X2) | k3_xboole_0(X2,X1) = X0 ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_542,c_0]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_10013,plain,
% 7.74/1.48      ( k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)) = k3_xboole_0(sK2,sK3) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_3066,c_6031]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_10706,plain,
% 7.74/1.48      ( r1_xboole_0(k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)),X0)
% 7.74/1.48      | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),X0) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_10013,c_4351]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_10707,plain,
% 7.74/1.48      ( r1_xboole_0(k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)),X0) = iProver_top
% 7.74/1.48      | r1_xboole_0(k3_xboole_0(sK2,sK3),X0) != iProver_top ),
% 7.74/1.48      inference(predicate_to_equality,[status(thm)],[c_10706]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_8106,plain,
% 7.74/1.48      ( r1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)),X0)
% 7.74/1.48      | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),X0) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_4351,c_328]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_10,plain,
% 7.74/1.48      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 7.74/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_11,plain,
% 7.74/1.48      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 7.74/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_1642,plain,
% 7.74/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.74/1.48      | r1_xboole_0(X2,X0)
% 7.74/1.48      | ~ r2_hidden(sK1(X2,X0),X1) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_10,c_11]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_2685,plain,
% 7.74/1.48      ( ~ r1_xboole_0(X0,X0) | r1_xboole_0(X1,X0) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_1642,c_11]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_8697,plain,
% 7.74/1.48      ( r1_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)))
% 7.74/1.48      | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_8106,c_2685]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_22,negated_conjecture,
% 7.74/1.48      ( r1_xboole_0(sK4,sK3) ),
% 7.74/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_555,plain,
% 7.74/1.48      ( sK5 = sK5 ),
% 7.74/1.48      inference(instantiation,[status(thm)],[c_541]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_544,plain,
% 7.74/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.74/1.48      theory(equality) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_6694,plain,
% 7.74/1.48      ( ~ r2_hidden(X0,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)))
% 7.74/1.48      | r2_hidden(X1,k3_xboole_0(sK2,sK3))
% 7.74/1.48      | X1 != X0 ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_6031,c_544]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_6700,plain,
% 7.74/1.48      ( ~ r2_hidden(sK5,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)))
% 7.74/1.48      | r2_hidden(sK5,k3_xboole_0(sK2,sK3))
% 7.74/1.48      | sK5 != sK5 ),
% 7.74/1.48      inference(instantiation,[status(thm)],[c_6694]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_4355,plain,
% 7.74/1.48      ( r1_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)))
% 7.74/1.48      | ~ r1_xboole_0(X1,k3_xboole_0(sK2,sK3))
% 7.74/1.48      | X0 != X1 ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_545,c_328]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_5,plain,
% 7.74/1.48      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 7.74/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_1405,plain,
% 7.74/1.48      ( r1_xboole_0(k3_xboole_0(X0,X1),X2)
% 7.74/1.48      | r2_hidden(sK1(k3_xboole_0(X0,X1),X2),X1) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_5,c_12]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_2690,plain,
% 7.74/1.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X2,X1),X0) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_1642,c_1405]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_4781,plain,
% 7.74/1.48      ( r1_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)))
% 7.74/1.48      | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),X1)
% 7.74/1.48      | X0 != k3_xboole_0(X2,X1) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_4355,c_2690]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_6704,plain,
% 7.74/1.48      ( ~ r1_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))
% 7.74/1.48      | r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_6031,c_4781]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_19,plain,
% 7.74/1.48      ( r2_hidden(X0,X1)
% 7.74/1.48      | k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) = X1 ),
% 7.74/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_17,plain,
% 7.74/1.48      ( r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
% 7.74/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_3085,plain,
% 7.74/1.48      ( r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) | r2_hidden(X1,X0) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_19,c_17]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_8984,plain,
% 7.74/1.48      ( r1_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(X0,X0,X0,X0))
% 7.74/1.48      | r2_hidden(X0,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_8118,c_3085]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_8986,plain,
% 7.74/1.48      ( r1_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))
% 7.74/1.48      | r2_hidden(sK5,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 7.74/1.48      inference(instantiation,[status(thm)],[c_8984]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_9,plain,
% 7.74/1.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.74/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_8683,plain,
% 7.74/1.48      ( r1_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)))
% 7.74/1.48      | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),X0) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_8106,c_9]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_23,negated_conjecture,
% 7.74/1.48      ( r2_hidden(sK5,sK4) ),
% 7.74/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_1646,plain,
% 7.74/1.48      ( ~ r1_xboole_0(sK4,X0) | ~ r2_hidden(sK5,X0) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_10,c_23]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_9008,plain,
% 7.74/1.48      ( ~ r1_xboole_0(k3_xboole_0(sK2,sK3),sK4)
% 7.74/1.48      | ~ r2_hidden(sK5,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_8683,c_1646]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_4,plain,
% 7.74/1.48      ( ~ r2_hidden(X0,X1)
% 7.74/1.48      | ~ r2_hidden(X0,X2)
% 7.74/1.48      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 7.74/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_9181,plain,
% 7.74/1.48      ( ~ r1_xboole_0(k3_xboole_0(sK2,sK3),sK4)
% 7.74/1.48      | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 7.74/1.48      | ~ r2_hidden(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_9008,c_4]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_3397,plain,
% 7.74/1.48      ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)))
% 7.74/1.48      | ~ r2_hidden(X1,k3_xboole_0(sK2,sK3))
% 7.74/1.48      | X0 != X1 ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_544,c_328]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_3399,plain,
% 7.74/1.48      ( r2_hidden(sK5,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)))
% 7.74/1.48      | ~ r2_hidden(sK5,k3_xboole_0(sK2,sK3))
% 7.74/1.48      | sK5 != sK5 ),
% 7.74/1.48      inference(instantiation,[status(thm)],[c_3397]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_9361,plain,
% 7.74/1.48      ( ~ r1_xboole_0(k3_xboole_0(sK2,sK3),sK4)
% 7.74/1.48      | ~ r2_hidden(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.74/1.48      inference(global_propositional_subsumption,
% 7.74/1.48                [status(thm)],
% 7.74/1.48                [c_9181,c_555,c_3399,c_9008]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_9506,plain,
% 7.74/1.48      ( ~ r1_xboole_0(sK4,sK3) | ~ r2_hidden(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_9361,c_2690]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_13864,plain,
% 7.74/1.48      ( r1_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 7.74/1.48      inference(global_propositional_subsumption,
% 7.74/1.48                [status(thm)],
% 7.74/1.48                [c_8697,c_22,c_555,c_6700,c_6704,c_8986,c_9506]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_13894,plain,
% 7.74/1.48      ( r1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)),X0) ),
% 7.74/1.48      inference(resolution,[status(thm)],[c_13864,c_9]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_13895,plain,
% 7.74/1.48      ( r1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)),X0) = iProver_top ),
% 7.74/1.48      inference(predicate_to_equality,[status(thm)],[c_13894]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_20719,plain,
% 7.74/1.48      ( r1_xboole_0(k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)),X0) = iProver_top ),
% 7.74/1.48      inference(global_propositional_subsumption,
% 7.74/1.48                [status(thm)],
% 7.74/1.48                [c_19781,c_8119,c_10707,c_13895]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_20726,plain,
% 7.74/1.48      ( r1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)),X0) = iProver_top ),
% 7.74/1.48      inference(superposition,[status(thm)],[c_0,c_20719]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_20752,plain,
% 7.74/1.48      ( r1_xboole_0(k3_xboole_0(sK2,sK3),X0) = iProver_top ),
% 7.74/1.48      inference(light_normalisation,[status(thm)],[c_20726,c_328]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_8,plain,
% 7.74/1.48      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.74/1.48      inference(cnf_transformation,[],[f42]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_1091,plain,
% 7.74/1.48      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 7.74/1.48      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.74/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_20770,plain,
% 7.74/1.48      ( k3_xboole_0(k3_xboole_0(sK2,sK3),X0) = k1_xboole_0 ),
% 7.74/1.48      inference(superposition,[status(thm)],[c_20752,c_1091]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_20864,plain,
% 7.74/1.48      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.74/1.48      inference(demodulation,[status(thm)],[c_20770,c_328]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_1083,plain,
% 7.74/1.48      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
% 7.74/1.48      | r1_xboole_0(X0,X1) = iProver_top ),
% 7.74/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_2652,plain,
% 7.74/1.48      ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) != X0
% 7.74/1.48      | r1_xboole_0(X0,X1) = iProver_top ),
% 7.74/1.48      inference(superposition,[status(thm)],[c_0,c_1083]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_20951,plain,
% 7.74/1.48      ( k5_xboole_0(sK3,k1_xboole_0) != sK3
% 7.74/1.48      | r1_xboole_0(sK3,sK2) = iProver_top ),
% 7.74/1.48      inference(superposition,[status(thm)],[c_20864,c_2652]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_1078,plain,
% 7.74/1.48      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 7.74/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_1090,plain,
% 7.74/1.48      ( r1_xboole_0(X0,X1) != iProver_top
% 7.74/1.48      | r1_xboole_0(X1,X0) = iProver_top ),
% 7.74/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_1393,plain,
% 7.74/1.48      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 7.74/1.48      inference(superposition,[status(thm)],[c_1078,c_1090]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_18,plain,
% 7.74/1.48      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 7.74/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_1082,plain,
% 7.74/1.48      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 7.74/1.48      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.74/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_1605,plain,
% 7.74/1.48      ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) = sK3 ),
% 7.74/1.48      inference(superposition,[status(thm)],[c_1393,c_1082]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_1467,plain,
% 7.74/1.48      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 7.74/1.48      inference(superposition,[status(thm)],[c_1393,c_1091]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_2647,plain,
% 7.74/1.48      ( k5_xboole_0(sK3,k1_xboole_0) = sK3 ),
% 7.74/1.48      inference(light_normalisation,[status(thm)],[c_1605,c_1467]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_20975,plain,
% 7.74/1.48      ( sK3 != sK3 | r1_xboole_0(sK3,sK2) = iProver_top ),
% 7.74/1.48      inference(light_normalisation,[status(thm)],[c_20951,c_2647]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_20976,plain,
% 7.74/1.48      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 7.74/1.48      inference(equality_resolution_simp,[status(thm)],[c_20975]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_16,plain,
% 7.74/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.74/1.48      | ~ r1_xboole_0(X0,X2)
% 7.74/1.48      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.74/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_1446,plain,
% 7.74/1.48      ( ~ r1_xboole_0(sK3,X0)
% 7.74/1.48      | r1_xboole_0(sK3,k2_xboole_0(X0,sK4))
% 7.74/1.48      | ~ r1_xboole_0(sK3,sK4) ),
% 7.74/1.48      inference(instantiation,[status(thm)],[c_16]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_6866,plain,
% 7.74/1.48      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
% 7.74/1.48      | ~ r1_xboole_0(sK3,sK4)
% 7.74/1.48      | ~ r1_xboole_0(sK3,sK2) ),
% 7.74/1.48      inference(instantiation,[status(thm)],[c_1446]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_6867,plain,
% 7.74/1.48      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = iProver_top
% 7.74/1.48      | r1_xboole_0(sK3,sK4) != iProver_top
% 7.74/1.48      | r1_xboole_0(sK3,sK2) != iProver_top ),
% 7.74/1.48      inference(predicate_to_equality,[status(thm)],[c_6866]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_2192,plain,
% 7.74/1.48      ( r1_xboole_0(k2_xboole_0(X0,sK4),sK3)
% 7.74/1.48      | ~ r1_xboole_0(sK3,k2_xboole_0(X0,sK4)) ),
% 7.74/1.48      inference(instantiation,[status(thm)],[c_9]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_4265,plain,
% 7.74/1.48      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
% 7.74/1.48      | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
% 7.74/1.48      inference(instantiation,[status(thm)],[c_2192]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_4266,plain,
% 7.74/1.48      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) = iProver_top
% 7.74/1.48      | r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != iProver_top ),
% 7.74/1.48      inference(predicate_to_equality,[status(thm)],[c_4265]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_1260,plain,
% 7.74/1.48      ( r1_xboole_0(sK3,sK4) | ~ r1_xboole_0(sK4,sK3) ),
% 7.74/1.48      inference(instantiation,[status(thm)],[c_9]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_1261,plain,
% 7.74/1.48      ( r1_xboole_0(sK3,sK4) = iProver_top
% 7.74/1.48      | r1_xboole_0(sK4,sK3) != iProver_top ),
% 7.74/1.48      inference(predicate_to_equality,[status(thm)],[c_1260]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_21,negated_conjecture,
% 7.74/1.48      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
% 7.74/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_28,plain,
% 7.74/1.48      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) != iProver_top ),
% 7.74/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(c_27,plain,
% 7.74/1.48      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 7.74/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.74/1.48  
% 7.74/1.48  cnf(contradiction,plain,
% 7.74/1.48      ( $false ),
% 7.74/1.48      inference(minisat,
% 7.74/1.48                [status(thm)],
% 7.74/1.48                [c_20976,c_6867,c_4266,c_1261,c_28,c_27]) ).
% 7.74/1.48  
% 7.74/1.48  
% 7.74/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.74/1.48  
% 7.74/1.48  ------                               Statistics
% 7.74/1.48  
% 7.74/1.48  ------ Selected
% 7.74/1.48  
% 7.74/1.48  total_time:                             0.806
% 7.74/1.48  
%------------------------------------------------------------------------------
