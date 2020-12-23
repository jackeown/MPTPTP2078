%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:05 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  124 (1211 expanded)
%              Number of clauses        :   51 ( 185 expanded)
%              Number of leaves         :   20 ( 370 expanded)
%              Depth                    :   18
%              Number of atoms          :  297 (1917 expanded)
%              Number of equality atoms :  124 (1227 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK2),sK3) != sK3
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k2_xboole_0(k1_tarski(sK2),sK3) != sK3
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f36])).

fof(f66,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f69])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f65,f70])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f56,f50])).

fof(f83,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f68,f70])).

fof(f3,axiom,(
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

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f29])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f82,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f57,f70,f70])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f78,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f51,f68])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f79,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) ),
    inference(definition_unfolding,[],[f53,f68,f68,f50])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f50])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f67,plain,(
    k2_xboole_0(k1_tarski(sK2),sK3) != sK3 ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f70])).

fof(f87,plain,(
    k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
    inference(definition_unfolding,[],[f67,f68,f71])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_984,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_987,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_990,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3430,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_990])).

cnf(c_6688,plain,
    ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,X0),sK3) = k3_enumset1(sK2,sK2,sK2,sK2,X0)
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_984,c_3430])).

cnf(c_7411,plain,
    ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_984,c_6688])).

cnf(c_18,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_7437,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(superposition,[status(thm)],[c_7411,c_18])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_993,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_17,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1613,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_17,c_18])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1617,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_18,c_12])).

cnf(c_2176,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_1613,c_1617])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2698,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2176,c_14])).

cnf(c_2701,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_2698,c_2176])).

cnf(c_2702,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_2701,c_2176])).

cnf(c_2705,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_2702,c_12])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_997,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3733,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2705,c_997])).

cnf(c_3752,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_3733])).

cnf(c_16,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_988,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3894,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3752,c_988])).

cnf(c_3905,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3894,c_2702])).

cnf(c_4041,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_3905,c_2705])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_999,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4468,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_999,c_3733])).

cnf(c_10,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_991,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1335,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_991,c_990])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_996,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3604,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1335,c_996])).

cnf(c_3734,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1335,c_997])).

cnf(c_4182,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3604,c_3734])).

cnf(c_5969,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4468,c_4182])).

cnf(c_4189,plain,
    ( r1_xboole_0(k5_xboole_0(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_4182])).

cnf(c_4731,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1)) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4189,c_988])).

cnf(c_5981,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5969,c_4731])).

cnf(c_7438,plain,
    ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_7437,c_4041,c_5981])).

cnf(c_22,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2166,plain,
    ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != sK3 ),
    inference(demodulation,[status(thm)],[c_1613,c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7438,c_2166])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:12:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.71/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.03  
% 3.71/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/1.03  
% 3.71/1.03  ------  iProver source info
% 3.71/1.03  
% 3.71/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.71/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/1.03  git: non_committed_changes: false
% 3.71/1.03  git: last_make_outside_of_git: false
% 3.71/1.03  
% 3.71/1.03  ------ 
% 3.71/1.03  
% 3.71/1.03  ------ Input Options
% 3.71/1.03  
% 3.71/1.03  --out_options                           all
% 3.71/1.03  --tptp_safe_out                         true
% 3.71/1.03  --problem_path                          ""
% 3.71/1.03  --include_path                          ""
% 3.71/1.03  --clausifier                            res/vclausify_rel
% 3.71/1.03  --clausifier_options                    ""
% 3.71/1.03  --stdin                                 false
% 3.71/1.03  --stats_out                             all
% 3.71/1.03  
% 3.71/1.03  ------ General Options
% 3.71/1.03  
% 3.71/1.03  --fof                                   false
% 3.71/1.03  --time_out_real                         305.
% 3.71/1.03  --time_out_virtual                      -1.
% 3.71/1.03  --symbol_type_check                     false
% 3.71/1.03  --clausify_out                          false
% 3.71/1.03  --sig_cnt_out                           false
% 3.71/1.03  --trig_cnt_out                          false
% 3.71/1.03  --trig_cnt_out_tolerance                1.
% 3.71/1.03  --trig_cnt_out_sk_spl                   false
% 3.71/1.03  --abstr_cl_out                          false
% 3.71/1.03  
% 3.71/1.03  ------ Global Options
% 3.71/1.03  
% 3.71/1.03  --schedule                              default
% 3.71/1.03  --add_important_lit                     false
% 3.71/1.03  --prop_solver_per_cl                    1000
% 3.71/1.03  --min_unsat_core                        false
% 3.71/1.03  --soft_assumptions                      false
% 3.71/1.03  --soft_lemma_size                       3
% 3.71/1.03  --prop_impl_unit_size                   0
% 3.71/1.03  --prop_impl_unit                        []
% 3.71/1.03  --share_sel_clauses                     true
% 3.71/1.03  --reset_solvers                         false
% 3.71/1.03  --bc_imp_inh                            [conj_cone]
% 3.71/1.03  --conj_cone_tolerance                   3.
% 3.71/1.03  --extra_neg_conj                        none
% 3.71/1.03  --large_theory_mode                     true
% 3.71/1.03  --prolific_symb_bound                   200
% 3.71/1.03  --lt_threshold                          2000
% 3.71/1.03  --clause_weak_htbl                      true
% 3.71/1.03  --gc_record_bc_elim                     false
% 3.71/1.03  
% 3.71/1.03  ------ Preprocessing Options
% 3.71/1.03  
% 3.71/1.03  --preprocessing_flag                    true
% 3.71/1.03  --time_out_prep_mult                    0.1
% 3.71/1.03  --splitting_mode                        input
% 3.71/1.03  --splitting_grd                         true
% 3.71/1.03  --splitting_cvd                         false
% 3.71/1.03  --splitting_cvd_svl                     false
% 3.71/1.03  --splitting_nvd                         32
% 3.71/1.03  --sub_typing                            true
% 3.71/1.03  --prep_gs_sim                           true
% 3.71/1.03  --prep_unflatten                        true
% 3.71/1.03  --prep_res_sim                          true
% 3.71/1.03  --prep_upred                            true
% 3.71/1.03  --prep_sem_filter                       exhaustive
% 3.71/1.03  --prep_sem_filter_out                   false
% 3.71/1.03  --pred_elim                             true
% 3.71/1.03  --res_sim_input                         true
% 3.71/1.03  --eq_ax_congr_red                       true
% 3.71/1.03  --pure_diseq_elim                       true
% 3.71/1.03  --brand_transform                       false
% 3.71/1.03  --non_eq_to_eq                          false
% 3.71/1.03  --prep_def_merge                        true
% 3.71/1.03  --prep_def_merge_prop_impl              false
% 3.71/1.03  --prep_def_merge_mbd                    true
% 3.71/1.03  --prep_def_merge_tr_red                 false
% 3.71/1.03  --prep_def_merge_tr_cl                  false
% 3.71/1.03  --smt_preprocessing                     true
% 3.71/1.03  --smt_ac_axioms                         fast
% 3.71/1.03  --preprocessed_out                      false
% 3.71/1.03  --preprocessed_stats                    false
% 3.71/1.03  
% 3.71/1.03  ------ Abstraction refinement Options
% 3.71/1.03  
% 3.71/1.03  --abstr_ref                             []
% 3.71/1.03  --abstr_ref_prep                        false
% 3.71/1.03  --abstr_ref_until_sat                   false
% 3.71/1.03  --abstr_ref_sig_restrict                funpre
% 3.71/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.03  --abstr_ref_under                       []
% 3.71/1.03  
% 3.71/1.03  ------ SAT Options
% 3.71/1.03  
% 3.71/1.03  --sat_mode                              false
% 3.71/1.03  --sat_fm_restart_options                ""
% 3.71/1.03  --sat_gr_def                            false
% 3.71/1.03  --sat_epr_types                         true
% 3.71/1.03  --sat_non_cyclic_types                  false
% 3.71/1.03  --sat_finite_models                     false
% 3.71/1.03  --sat_fm_lemmas                         false
% 3.71/1.03  --sat_fm_prep                           false
% 3.71/1.03  --sat_fm_uc_incr                        true
% 3.71/1.03  --sat_out_model                         small
% 3.71/1.03  --sat_out_clauses                       false
% 3.71/1.03  
% 3.71/1.03  ------ QBF Options
% 3.71/1.03  
% 3.71/1.03  --qbf_mode                              false
% 3.71/1.03  --qbf_elim_univ                         false
% 3.71/1.03  --qbf_dom_inst                          none
% 3.71/1.03  --qbf_dom_pre_inst                      false
% 3.71/1.03  --qbf_sk_in                             false
% 3.71/1.03  --qbf_pred_elim                         true
% 3.71/1.03  --qbf_split                             512
% 3.71/1.03  
% 3.71/1.03  ------ BMC1 Options
% 3.71/1.03  
% 3.71/1.03  --bmc1_incremental                      false
% 3.71/1.03  --bmc1_axioms                           reachable_all
% 3.71/1.03  --bmc1_min_bound                        0
% 3.71/1.03  --bmc1_max_bound                        -1
% 3.71/1.03  --bmc1_max_bound_default                -1
% 3.71/1.03  --bmc1_symbol_reachability              true
% 3.71/1.03  --bmc1_property_lemmas                  false
% 3.71/1.03  --bmc1_k_induction                      false
% 3.71/1.03  --bmc1_non_equiv_states                 false
% 3.71/1.03  --bmc1_deadlock                         false
% 3.71/1.03  --bmc1_ucm                              false
% 3.71/1.03  --bmc1_add_unsat_core                   none
% 3.71/1.03  --bmc1_unsat_core_children              false
% 3.71/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.03  --bmc1_out_stat                         full
% 3.71/1.03  --bmc1_ground_init                      false
% 3.71/1.03  --bmc1_pre_inst_next_state              false
% 3.71/1.03  --bmc1_pre_inst_state                   false
% 3.71/1.03  --bmc1_pre_inst_reach_state             false
% 3.71/1.03  --bmc1_out_unsat_core                   false
% 3.71/1.03  --bmc1_aig_witness_out                  false
% 3.71/1.03  --bmc1_verbose                          false
% 3.71/1.03  --bmc1_dump_clauses_tptp                false
% 3.71/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.03  --bmc1_dump_file                        -
% 3.71/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.03  --bmc1_ucm_extend_mode                  1
% 3.71/1.03  --bmc1_ucm_init_mode                    2
% 3.71/1.03  --bmc1_ucm_cone_mode                    none
% 3.71/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.03  --bmc1_ucm_relax_model                  4
% 3.71/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.03  --bmc1_ucm_layered_model                none
% 3.71/1.03  --bmc1_ucm_max_lemma_size               10
% 3.71/1.03  
% 3.71/1.03  ------ AIG Options
% 3.71/1.03  
% 3.71/1.03  --aig_mode                              false
% 3.71/1.03  
% 3.71/1.03  ------ Instantiation Options
% 3.71/1.03  
% 3.71/1.03  --instantiation_flag                    true
% 3.71/1.03  --inst_sos_flag                         true
% 3.71/1.03  --inst_sos_phase                        true
% 3.71/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.03  --inst_lit_sel_side                     num_symb
% 3.71/1.03  --inst_solver_per_active                1400
% 3.71/1.03  --inst_solver_calls_frac                1.
% 3.71/1.03  --inst_passive_queue_type               priority_queues
% 3.71/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.03  --inst_passive_queues_freq              [25;2]
% 3.71/1.03  --inst_dismatching                      true
% 3.71/1.03  --inst_eager_unprocessed_to_passive     true
% 3.71/1.03  --inst_prop_sim_given                   true
% 3.71/1.03  --inst_prop_sim_new                     false
% 3.71/1.03  --inst_subs_new                         false
% 3.71/1.03  --inst_eq_res_simp                      false
% 3.71/1.03  --inst_subs_given                       false
% 3.71/1.03  --inst_orphan_elimination               true
% 3.71/1.03  --inst_learning_loop_flag               true
% 3.71/1.03  --inst_learning_start                   3000
% 3.71/1.03  --inst_learning_factor                  2
% 3.71/1.03  --inst_start_prop_sim_after_learn       3
% 3.71/1.03  --inst_sel_renew                        solver
% 3.71/1.03  --inst_lit_activity_flag                true
% 3.71/1.03  --inst_restr_to_given                   false
% 3.71/1.03  --inst_activity_threshold               500
% 3.71/1.03  --inst_out_proof                        true
% 3.71/1.03  
% 3.71/1.03  ------ Resolution Options
% 3.71/1.03  
% 3.71/1.03  --resolution_flag                       true
% 3.71/1.03  --res_lit_sel                           adaptive
% 3.71/1.03  --res_lit_sel_side                      none
% 3.71/1.03  --res_ordering                          kbo
% 3.71/1.03  --res_to_prop_solver                    active
% 3.71/1.03  --res_prop_simpl_new                    false
% 3.71/1.03  --res_prop_simpl_given                  true
% 3.71/1.03  --res_passive_queue_type                priority_queues
% 3.71/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.03  --res_passive_queues_freq               [15;5]
% 3.71/1.03  --res_forward_subs                      full
% 3.71/1.03  --res_backward_subs                     full
% 3.71/1.03  --res_forward_subs_resolution           true
% 3.71/1.03  --res_backward_subs_resolution          true
% 3.71/1.03  --res_orphan_elimination                true
% 3.71/1.03  --res_time_limit                        2.
% 3.71/1.03  --res_out_proof                         true
% 3.71/1.03  
% 3.71/1.03  ------ Superposition Options
% 3.71/1.03  
% 3.71/1.03  --superposition_flag                    true
% 3.71/1.03  --sup_passive_queue_type                priority_queues
% 3.71/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.71/1.03  --demod_completeness_check              fast
% 3.71/1.03  --demod_use_ground                      true
% 3.71/1.03  --sup_to_prop_solver                    passive
% 3.71/1.03  --sup_prop_simpl_new                    true
% 3.71/1.03  --sup_prop_simpl_given                  true
% 3.71/1.03  --sup_fun_splitting                     true
% 3.71/1.03  --sup_smt_interval                      50000
% 3.71/1.03  
% 3.71/1.03  ------ Superposition Simplification Setup
% 3.71/1.03  
% 3.71/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.71/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.71/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.71/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.71/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.71/1.03  --sup_immed_triv                        [TrivRules]
% 3.71/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.03  --sup_immed_bw_main                     []
% 3.71/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.71/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.03  --sup_input_bw                          []
% 3.71/1.03  
% 3.71/1.03  ------ Combination Options
% 3.71/1.03  
% 3.71/1.03  --comb_res_mult                         3
% 3.71/1.03  --comb_sup_mult                         2
% 3.71/1.03  --comb_inst_mult                        10
% 3.71/1.03  
% 3.71/1.03  ------ Debug Options
% 3.71/1.03  
% 3.71/1.03  --dbg_backtrace                         false
% 3.71/1.03  --dbg_dump_prop_clauses                 false
% 3.71/1.03  --dbg_dump_prop_clauses_file            -
% 3.71/1.03  --dbg_out_stat                          false
% 3.71/1.03  ------ Parsing...
% 3.71/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/1.03  
% 3.71/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.71/1.03  
% 3.71/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/1.03  
% 3.71/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/1.03  ------ Proving...
% 3.71/1.03  ------ Problem Properties 
% 3.71/1.03  
% 3.71/1.03  
% 3.71/1.03  clauses                                 23
% 3.71/1.03  conjectures                             2
% 3.71/1.03  EPR                                     4
% 3.71/1.03  Horn                                    17
% 3.71/1.03  unary                                   7
% 3.71/1.03  binary                                  9
% 3.71/1.03  lits                                    47
% 3.71/1.03  lits eq                                 12
% 3.71/1.03  fd_pure                                 0
% 3.71/1.03  fd_pseudo                               0
% 3.71/1.03  fd_cond                                 0
% 3.71/1.03  fd_pseudo_cond                          4
% 3.71/1.03  AC symbols                              0
% 3.71/1.03  
% 3.71/1.03  ------ Schedule dynamic 5 is on 
% 3.71/1.03  
% 3.71/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.71/1.03  
% 3.71/1.03  
% 3.71/1.03  ------ 
% 3.71/1.03  Current options:
% 3.71/1.03  ------ 
% 3.71/1.03  
% 3.71/1.03  ------ Input Options
% 3.71/1.03  
% 3.71/1.03  --out_options                           all
% 3.71/1.03  --tptp_safe_out                         true
% 3.71/1.03  --problem_path                          ""
% 3.71/1.03  --include_path                          ""
% 3.71/1.03  --clausifier                            res/vclausify_rel
% 3.71/1.03  --clausifier_options                    ""
% 3.71/1.03  --stdin                                 false
% 3.71/1.03  --stats_out                             all
% 3.71/1.03  
% 3.71/1.03  ------ General Options
% 3.71/1.03  
% 3.71/1.03  --fof                                   false
% 3.71/1.03  --time_out_real                         305.
% 3.71/1.03  --time_out_virtual                      -1.
% 3.71/1.03  --symbol_type_check                     false
% 3.71/1.03  --clausify_out                          false
% 3.71/1.03  --sig_cnt_out                           false
% 3.71/1.03  --trig_cnt_out                          false
% 3.71/1.03  --trig_cnt_out_tolerance                1.
% 3.71/1.03  --trig_cnt_out_sk_spl                   false
% 3.71/1.03  --abstr_cl_out                          false
% 3.71/1.03  
% 3.71/1.03  ------ Global Options
% 3.71/1.03  
% 3.71/1.03  --schedule                              default
% 3.71/1.03  --add_important_lit                     false
% 3.71/1.03  --prop_solver_per_cl                    1000
% 3.71/1.03  --min_unsat_core                        false
% 3.71/1.03  --soft_assumptions                      false
% 3.71/1.03  --soft_lemma_size                       3
% 3.71/1.03  --prop_impl_unit_size                   0
% 3.71/1.03  --prop_impl_unit                        []
% 3.71/1.03  --share_sel_clauses                     true
% 3.71/1.03  --reset_solvers                         false
% 3.71/1.03  --bc_imp_inh                            [conj_cone]
% 3.71/1.03  --conj_cone_tolerance                   3.
% 3.71/1.03  --extra_neg_conj                        none
% 3.71/1.03  --large_theory_mode                     true
% 3.71/1.03  --prolific_symb_bound                   200
% 3.71/1.03  --lt_threshold                          2000
% 3.71/1.03  --clause_weak_htbl                      true
% 3.71/1.03  --gc_record_bc_elim                     false
% 3.71/1.03  
% 3.71/1.03  ------ Preprocessing Options
% 3.71/1.03  
% 3.71/1.03  --preprocessing_flag                    true
% 3.71/1.03  --time_out_prep_mult                    0.1
% 3.71/1.03  --splitting_mode                        input
% 3.71/1.03  --splitting_grd                         true
% 3.71/1.03  --splitting_cvd                         false
% 3.71/1.03  --splitting_cvd_svl                     false
% 3.71/1.03  --splitting_nvd                         32
% 3.71/1.03  --sub_typing                            true
% 3.71/1.03  --prep_gs_sim                           true
% 3.71/1.03  --prep_unflatten                        true
% 3.71/1.03  --prep_res_sim                          true
% 3.71/1.03  --prep_upred                            true
% 3.71/1.03  --prep_sem_filter                       exhaustive
% 3.71/1.03  --prep_sem_filter_out                   false
% 3.71/1.03  --pred_elim                             true
% 3.71/1.03  --res_sim_input                         true
% 3.71/1.03  --eq_ax_congr_red                       true
% 3.71/1.03  --pure_diseq_elim                       true
% 3.71/1.03  --brand_transform                       false
% 3.71/1.03  --non_eq_to_eq                          false
% 3.71/1.03  --prep_def_merge                        true
% 3.71/1.03  --prep_def_merge_prop_impl              false
% 3.71/1.03  --prep_def_merge_mbd                    true
% 3.71/1.03  --prep_def_merge_tr_red                 false
% 3.71/1.03  --prep_def_merge_tr_cl                  false
% 3.71/1.03  --smt_preprocessing                     true
% 3.71/1.03  --smt_ac_axioms                         fast
% 3.71/1.03  --preprocessed_out                      false
% 3.71/1.03  --preprocessed_stats                    false
% 3.71/1.03  
% 3.71/1.03  ------ Abstraction refinement Options
% 3.71/1.03  
% 3.71/1.03  --abstr_ref                             []
% 3.71/1.03  --abstr_ref_prep                        false
% 3.71/1.03  --abstr_ref_until_sat                   false
% 3.71/1.03  --abstr_ref_sig_restrict                funpre
% 3.71/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.03  --abstr_ref_under                       []
% 3.71/1.03  
% 3.71/1.03  ------ SAT Options
% 3.71/1.03  
% 3.71/1.03  --sat_mode                              false
% 3.71/1.03  --sat_fm_restart_options                ""
% 3.71/1.03  --sat_gr_def                            false
% 3.71/1.03  --sat_epr_types                         true
% 3.71/1.03  --sat_non_cyclic_types                  false
% 3.71/1.03  --sat_finite_models                     false
% 3.71/1.03  --sat_fm_lemmas                         false
% 3.71/1.03  --sat_fm_prep                           false
% 3.71/1.03  --sat_fm_uc_incr                        true
% 3.71/1.03  --sat_out_model                         small
% 3.71/1.03  --sat_out_clauses                       false
% 3.71/1.03  
% 3.71/1.03  ------ QBF Options
% 3.71/1.03  
% 3.71/1.03  --qbf_mode                              false
% 3.71/1.03  --qbf_elim_univ                         false
% 3.71/1.03  --qbf_dom_inst                          none
% 3.71/1.03  --qbf_dom_pre_inst                      false
% 3.71/1.03  --qbf_sk_in                             false
% 3.71/1.03  --qbf_pred_elim                         true
% 3.71/1.03  --qbf_split                             512
% 3.71/1.03  
% 3.71/1.03  ------ BMC1 Options
% 3.71/1.03  
% 3.71/1.03  --bmc1_incremental                      false
% 3.71/1.03  --bmc1_axioms                           reachable_all
% 3.71/1.03  --bmc1_min_bound                        0
% 3.71/1.03  --bmc1_max_bound                        -1
% 3.71/1.03  --bmc1_max_bound_default                -1
% 3.71/1.03  --bmc1_symbol_reachability              true
% 3.71/1.03  --bmc1_property_lemmas                  false
% 3.71/1.03  --bmc1_k_induction                      false
% 3.71/1.03  --bmc1_non_equiv_states                 false
% 3.71/1.03  --bmc1_deadlock                         false
% 3.71/1.03  --bmc1_ucm                              false
% 3.71/1.03  --bmc1_add_unsat_core                   none
% 3.71/1.03  --bmc1_unsat_core_children              false
% 3.71/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.03  --bmc1_out_stat                         full
% 3.71/1.03  --bmc1_ground_init                      false
% 3.71/1.03  --bmc1_pre_inst_next_state              false
% 3.71/1.03  --bmc1_pre_inst_state                   false
% 3.71/1.03  --bmc1_pre_inst_reach_state             false
% 3.71/1.03  --bmc1_out_unsat_core                   false
% 3.71/1.03  --bmc1_aig_witness_out                  false
% 3.71/1.03  --bmc1_verbose                          false
% 3.71/1.03  --bmc1_dump_clauses_tptp                false
% 3.71/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.03  --bmc1_dump_file                        -
% 3.71/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.03  --bmc1_ucm_extend_mode                  1
% 3.71/1.03  --bmc1_ucm_init_mode                    2
% 3.71/1.03  --bmc1_ucm_cone_mode                    none
% 3.71/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.03  --bmc1_ucm_relax_model                  4
% 3.71/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.03  --bmc1_ucm_layered_model                none
% 3.71/1.03  --bmc1_ucm_max_lemma_size               10
% 3.71/1.03  
% 3.71/1.03  ------ AIG Options
% 3.71/1.03  
% 3.71/1.03  --aig_mode                              false
% 3.71/1.03  
% 3.71/1.03  ------ Instantiation Options
% 3.71/1.03  
% 3.71/1.03  --instantiation_flag                    true
% 3.71/1.03  --inst_sos_flag                         true
% 3.71/1.03  --inst_sos_phase                        true
% 3.71/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.03  --inst_lit_sel_side                     none
% 3.71/1.03  --inst_solver_per_active                1400
% 3.71/1.03  --inst_solver_calls_frac                1.
% 3.71/1.03  --inst_passive_queue_type               priority_queues
% 3.71/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.03  --inst_passive_queues_freq              [25;2]
% 3.71/1.03  --inst_dismatching                      true
% 3.71/1.03  --inst_eager_unprocessed_to_passive     true
% 3.71/1.03  --inst_prop_sim_given                   true
% 3.71/1.03  --inst_prop_sim_new                     false
% 3.71/1.03  --inst_subs_new                         false
% 3.71/1.03  --inst_eq_res_simp                      false
% 3.71/1.03  --inst_subs_given                       false
% 3.71/1.03  --inst_orphan_elimination               true
% 3.71/1.03  --inst_learning_loop_flag               true
% 3.71/1.03  --inst_learning_start                   3000
% 3.71/1.03  --inst_learning_factor                  2
% 3.71/1.03  --inst_start_prop_sim_after_learn       3
% 3.71/1.03  --inst_sel_renew                        solver
% 3.71/1.03  --inst_lit_activity_flag                true
% 3.71/1.03  --inst_restr_to_given                   false
% 3.71/1.03  --inst_activity_threshold               500
% 3.71/1.03  --inst_out_proof                        true
% 3.71/1.03  
% 3.71/1.03  ------ Resolution Options
% 3.71/1.03  
% 3.71/1.03  --resolution_flag                       false
% 3.71/1.03  --res_lit_sel                           adaptive
% 3.71/1.03  --res_lit_sel_side                      none
% 3.71/1.03  --res_ordering                          kbo
% 3.71/1.03  --res_to_prop_solver                    active
% 3.71/1.03  --res_prop_simpl_new                    false
% 3.71/1.03  --res_prop_simpl_given                  true
% 3.71/1.03  --res_passive_queue_type                priority_queues
% 3.71/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.03  --res_passive_queues_freq               [15;5]
% 3.71/1.03  --res_forward_subs                      full
% 3.71/1.03  --res_backward_subs                     full
% 3.71/1.03  --res_forward_subs_resolution           true
% 3.71/1.03  --res_backward_subs_resolution          true
% 3.71/1.03  --res_orphan_elimination                true
% 3.71/1.03  --res_time_limit                        2.
% 3.71/1.03  --res_out_proof                         true
% 3.71/1.03  
% 3.71/1.03  ------ Superposition Options
% 3.71/1.03  
% 3.71/1.03  --superposition_flag                    true
% 3.71/1.03  --sup_passive_queue_type                priority_queues
% 3.71/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.71/1.03  --demod_completeness_check              fast
% 3.71/1.03  --demod_use_ground                      true
% 3.71/1.03  --sup_to_prop_solver                    passive
% 3.71/1.03  --sup_prop_simpl_new                    true
% 3.71/1.03  --sup_prop_simpl_given                  true
% 3.71/1.03  --sup_fun_splitting                     true
% 3.71/1.03  --sup_smt_interval                      50000
% 3.71/1.03  
% 3.71/1.03  ------ Superposition Simplification Setup
% 3.71/1.03  
% 3.71/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.71/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.71/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.71/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.71/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.71/1.03  --sup_immed_triv                        [TrivRules]
% 3.71/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.03  --sup_immed_bw_main                     []
% 3.71/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.71/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.03  --sup_input_bw                          []
% 3.71/1.03  
% 3.71/1.03  ------ Combination Options
% 3.71/1.03  
% 3.71/1.03  --comb_res_mult                         3
% 3.71/1.03  --comb_sup_mult                         2
% 3.71/1.03  --comb_inst_mult                        10
% 3.71/1.03  
% 3.71/1.03  ------ Debug Options
% 3.71/1.03  
% 3.71/1.03  --dbg_backtrace                         false
% 3.71/1.03  --dbg_dump_prop_clauses                 false
% 3.71/1.03  --dbg_dump_prop_clauses_file            -
% 3.71/1.03  --dbg_out_stat                          false
% 3.71/1.03  
% 3.71/1.03  
% 3.71/1.03  
% 3.71/1.03  
% 3.71/1.03  ------ Proving...
% 3.71/1.03  
% 3.71/1.03  
% 3.71/1.03  % SZS status Theorem for theBenchmark.p
% 3.71/1.03  
% 3.71/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/1.03  
% 3.71/1.03  fof(f18,conjecture,(
% 3.71/1.03    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.03  
% 3.71/1.03  fof(f19,negated_conjecture,(
% 3.71/1.03    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.71/1.03    inference(negated_conjecture,[],[f18])).
% 3.71/1.03  
% 3.71/1.03  fof(f23,plain,(
% 3.71/1.03    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 3.71/1.03    inference(ennf_transformation,[],[f19])).
% 3.71/1.03  
% 3.71/1.03  fof(f36,plain,(
% 3.71/1.03    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK2),sK3) != sK3 & r2_hidden(sK2,sK3))),
% 3.71/1.03    introduced(choice_axiom,[])).
% 3.71/1.03  
% 3.71/1.03  fof(f37,plain,(
% 3.71/1.03    k2_xboole_0(k1_tarski(sK2),sK3) != sK3 & r2_hidden(sK2,sK3)),
% 3.71/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f36])).
% 3.71/1.03  
% 3.71/1.03  fof(f66,plain,(
% 3.71/1.03    r2_hidden(sK2,sK3)),
% 3.71/1.03    inference(cnf_transformation,[],[f37])).
% 3.71/1.03  
% 3.71/1.03  fof(f17,axiom,(
% 3.71/1.03    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.03  
% 3.71/1.03  fof(f34,plain,(
% 3.71/1.03    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.71/1.03    inference(nnf_transformation,[],[f17])).
% 3.71/1.03  
% 3.71/1.03  fof(f35,plain,(
% 3.71/1.03    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.71/1.03    inference(flattening,[],[f34])).
% 3.71/1.03  
% 3.71/1.03  fof(f65,plain,(
% 3.71/1.03    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.71/1.03    inference(cnf_transformation,[],[f35])).
% 3.71/1.03  
% 3.71/1.03  fof(f13,axiom,(
% 3.71/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.03  
% 3.71/1.03  fof(f59,plain,(
% 3.71/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.71/1.03    inference(cnf_transformation,[],[f13])).
% 3.71/1.03  
% 3.71/1.03  fof(f14,axiom,(
% 3.71/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.03  
% 3.71/1.03  fof(f60,plain,(
% 3.71/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.71/1.03    inference(cnf_transformation,[],[f14])).
% 3.71/1.03  
% 3.71/1.03  fof(f15,axiom,(
% 3.71/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.03  
% 3.71/1.03  fof(f61,plain,(
% 3.71/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.71/1.03    inference(cnf_transformation,[],[f15])).
% 3.71/1.03  
% 3.71/1.03  fof(f69,plain,(
% 3.71/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.71/1.03    inference(definition_unfolding,[],[f60,f61])).
% 3.71/1.03  
% 3.71/1.03  fof(f70,plain,(
% 3.71/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.71/1.03    inference(definition_unfolding,[],[f59,f69])).
% 3.71/1.03  
% 3.71/1.03  fof(f84,plain,(
% 3.71/1.03    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.71/1.03    inference(definition_unfolding,[],[f65,f70])).
% 3.71/1.03  
% 3.71/1.03  fof(f7,axiom,(
% 3.71/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.03  
% 3.71/1.03  fof(f22,plain,(
% 3.71/1.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.71/1.03    inference(ennf_transformation,[],[f7])).
% 3.71/1.03  
% 3.71/1.03  fof(f52,plain,(
% 3.71/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.71/1.03    inference(cnf_transformation,[],[f22])).
% 3.71/1.03  
% 3.71/1.03  fof(f16,axiom,(
% 3.71/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.03  
% 3.71/1.03  fof(f62,plain,(
% 3.71/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.71/1.03    inference(cnf_transformation,[],[f16])).
% 3.71/1.03  
% 3.71/1.03  fof(f10,axiom,(
% 3.71/1.03    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.03  
% 3.71/1.03  fof(f56,plain,(
% 3.71/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.71/1.03    inference(cnf_transformation,[],[f10])).
% 3.71/1.03  
% 3.71/1.03  fof(f5,axiom,(
% 3.71/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.03  
% 3.71/1.03  fof(f50,plain,(
% 3.71/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.71/1.03    inference(cnf_transformation,[],[f5])).
% 3.71/1.03  
% 3.71/1.03  fof(f68,plain,(
% 3.71/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.71/1.03    inference(definition_unfolding,[],[f56,f50])).
% 3.71/1.03  
% 3.71/1.03  fof(f83,plain,(
% 3.71/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.71/1.03    inference(definition_unfolding,[],[f62,f68,f70])).
% 3.71/1.03  
% 3.71/1.03  fof(f3,axiom,(
% 3.71/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.03  
% 3.71/1.03  fof(f20,plain,(
% 3.71/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.71/1.03    inference(rectify,[],[f3])).
% 3.71/1.03  
% 3.71/1.03  fof(f21,plain,(
% 3.71/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.71/1.03    inference(ennf_transformation,[],[f20])).
% 3.71/1.03  
% 3.71/1.03  fof(f29,plain,(
% 3.71/1.03    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.71/1.03    introduced(choice_axiom,[])).
% 3.71/1.03  
% 3.71/1.03  fof(f30,plain,(
% 3.71/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.71/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f29])).
% 3.71/1.03  
% 3.71/1.03  fof(f44,plain,(
% 3.71/1.03    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.71/1.03    inference(cnf_transformation,[],[f30])).
% 3.71/1.03  
% 3.71/1.03  fof(f11,axiom,(
% 3.71/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.03  
% 3.71/1.03  fof(f57,plain,(
% 3.71/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.71/1.03    inference(cnf_transformation,[],[f11])).
% 3.71/1.03  
% 3.71/1.03  fof(f82,plain,(
% 3.71/1.03    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 3.71/1.03    inference(definition_unfolding,[],[f57,f70,f70])).
% 3.71/1.03  
% 3.71/1.03  fof(f6,axiom,(
% 3.71/1.03    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.03  
% 3.71/1.03  fof(f51,plain,(
% 3.71/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.71/1.03    inference(cnf_transformation,[],[f6])).
% 3.71/1.03  
% 3.71/1.03  fof(f78,plain,(
% 3.71/1.03    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 3.71/1.03    inference(definition_unfolding,[],[f51,f68])).
% 3.71/1.03  
% 3.71/1.03  fof(f8,axiom,(
% 3.71/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.03  
% 3.71/1.03  fof(f53,plain,(
% 3.71/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.71/1.03    inference(cnf_transformation,[],[f8])).
% 3.71/1.03  
% 3.71/1.03  fof(f79,plain,(
% 3.71/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)))) )),
% 3.71/1.03    inference(definition_unfolding,[],[f53,f68,f68,f50])).
% 3.71/1.03  
% 3.71/1.03  fof(f2,axiom,(
% 3.71/1.03    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.03  
% 3.71/1.03  fof(f24,plain,(
% 3.71/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.71/1.03    inference(nnf_transformation,[],[f2])).
% 3.71/1.03  
% 3.71/1.03  fof(f25,plain,(
% 3.71/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.71/1.03    inference(flattening,[],[f24])).
% 3.71/1.03  
% 3.71/1.03  fof(f26,plain,(
% 3.71/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.71/1.03    inference(rectify,[],[f25])).
% 3.71/1.03  
% 3.71/1.03  fof(f27,plain,(
% 3.71/1.03    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.71/1.03    introduced(choice_axiom,[])).
% 3.71/1.03  
% 3.71/1.03  fof(f28,plain,(
% 3.71/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.71/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.71/1.03  
% 3.71/1.03  fof(f39,plain,(
% 3.71/1.03    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.71/1.03    inference(cnf_transformation,[],[f28])).
% 3.71/1.03  
% 3.71/1.03  fof(f76,plain,(
% 3.71/1.03    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.71/1.03    inference(definition_unfolding,[],[f39,f50])).
% 3.71/1.03  
% 3.71/1.03  fof(f89,plain,(
% 3.71/1.03    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.71/1.03    inference(equality_resolution,[],[f76])).
% 3.71/1.03  
% 3.71/1.03  fof(f9,axiom,(
% 3.71/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.03  
% 3.71/1.03  fof(f33,plain,(
% 3.71/1.03    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.71/1.03    inference(nnf_transformation,[],[f9])).
% 3.71/1.03  
% 3.71/1.03  fof(f54,plain,(
% 3.71/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.71/1.03    inference(cnf_transformation,[],[f33])).
% 3.71/1.03  
% 3.71/1.03  fof(f81,plain,(
% 3.71/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.71/1.03    inference(definition_unfolding,[],[f54,f50])).
% 3.71/1.03  
% 3.71/1.03  fof(f41,plain,(
% 3.71/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.71/1.03    inference(cnf_transformation,[],[f28])).
% 3.71/1.03  
% 3.71/1.03  fof(f74,plain,(
% 3.71/1.03    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.71/1.03    inference(definition_unfolding,[],[f41,f50])).
% 3.71/1.03  
% 3.71/1.03  fof(f4,axiom,(
% 3.71/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.03  
% 3.71/1.03  fof(f31,plain,(
% 3.71/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.71/1.03    inference(nnf_transformation,[],[f4])).
% 3.71/1.03  
% 3.71/1.03  fof(f32,plain,(
% 3.71/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.71/1.03    inference(flattening,[],[f31])).
% 3.71/1.03  
% 3.71/1.03  fof(f48,plain,(
% 3.71/1.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.71/1.03    inference(cnf_transformation,[],[f32])).
% 3.71/1.03  
% 3.71/1.03  fof(f91,plain,(
% 3.71/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.71/1.03    inference(equality_resolution,[],[f48])).
% 3.71/1.03  
% 3.71/1.03  fof(f38,plain,(
% 3.71/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.71/1.03    inference(cnf_transformation,[],[f28])).
% 3.71/1.03  
% 3.71/1.03  fof(f77,plain,(
% 3.71/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.71/1.03    inference(definition_unfolding,[],[f38,f50])).
% 3.71/1.03  
% 3.71/1.03  fof(f90,plain,(
% 3.71/1.03    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.71/1.03    inference(equality_resolution,[],[f77])).
% 3.71/1.03  
% 3.71/1.03  fof(f67,plain,(
% 3.71/1.03    k2_xboole_0(k1_tarski(sK2),sK3) != sK3),
% 3.71/1.03    inference(cnf_transformation,[],[f37])).
% 3.71/1.03  
% 3.71/1.03  fof(f12,axiom,(
% 3.71/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.03  
% 3.71/1.03  fof(f58,plain,(
% 3.71/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.71/1.03    inference(cnf_transformation,[],[f12])).
% 3.71/1.03  
% 3.71/1.03  fof(f71,plain,(
% 3.71/1.03    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.71/1.03    inference(definition_unfolding,[],[f58,f70])).
% 3.71/1.03  
% 3.71/1.03  fof(f87,plain,(
% 3.71/1.03    k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != sK3),
% 3.71/1.03    inference(definition_unfolding,[],[f67,f68,f71])).
% 3.71/1.03  
% 3.71/1.03  cnf(c_23,negated_conjecture,
% 3.71/1.03      ( r2_hidden(sK2,sK3) ),
% 3.71/1.03      inference(cnf_transformation,[],[f66]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_984,plain,
% 3.71/1.03      ( r2_hidden(sK2,sK3) = iProver_top ),
% 3.71/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_19,plain,
% 3.71/1.03      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
% 3.71/1.03      | ~ r2_hidden(X1,X2)
% 3.71/1.03      | ~ r2_hidden(X0,X2) ),
% 3.71/1.03      inference(cnf_transformation,[],[f84]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_987,plain,
% 3.71/1.03      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) = iProver_top
% 3.71/1.03      | r2_hidden(X0,X2) != iProver_top
% 3.71/1.03      | r2_hidden(X1,X2) != iProver_top ),
% 3.71/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_13,plain,
% 3.71/1.03      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.71/1.03      inference(cnf_transformation,[],[f52]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_990,plain,
% 3.71/1.03      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.71/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_3430,plain,
% 3.71/1.03      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
% 3.71/1.03      | r2_hidden(X1,X2) != iProver_top
% 3.71/1.03      | r2_hidden(X0,X2) != iProver_top ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_987,c_990]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_6688,plain,
% 3.71/1.03      ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,X0),sK3) = k3_enumset1(sK2,sK2,sK2,sK2,X0)
% 3.71/1.03      | r2_hidden(X0,sK3) != iProver_top ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_984,c_3430]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_7411,plain,
% 3.71/1.03      ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_984,c_6688]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_18,plain,
% 3.71/1.03      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 3.71/1.03      inference(cnf_transformation,[],[f83]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_7437,plain,
% 3.71/1.03      ( k5_xboole_0(sK3,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_7411,c_18]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_8,plain,
% 3.71/1.03      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.71/1.03      inference(cnf_transformation,[],[f44]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_993,plain,
% 3.71/1.03      ( r1_xboole_0(X0,X1) = iProver_top
% 3.71/1.03      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.71/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_17,plain,
% 3.71/1.03      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 3.71/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_1613,plain,
% 3.71/1.03      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_17,c_18]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_12,plain,
% 3.71/1.03      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 3.71/1.03      inference(cnf_transformation,[],[f78]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_1617,plain,
% 3.71/1.03      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_18,c_12]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_2176,plain,
% 3.71/1.03      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_1613,c_1617]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_14,plain,
% 3.71/1.03      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 3.71/1.03      inference(cnf_transformation,[],[f79]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_2698,plain,
% 3.71/1.03      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_2176,c_14]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_2701,plain,
% 3.71/1.03      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.71/1.03      inference(demodulation,[status(thm)],[c_2698,c_2176]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_2702,plain,
% 3.71/1.03      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.71/1.03      inference(demodulation,[status(thm)],[c_2701,c_2176]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_2705,plain,
% 3.71/1.03      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 3.71/1.03      inference(demodulation,[status(thm)],[c_2702,c_12]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_4,plain,
% 3.71/1.03      ( ~ r2_hidden(X0,X1)
% 3.71/1.03      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.71/1.03      inference(cnf_transformation,[],[f89]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_997,plain,
% 3.71/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.71/1.03      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 3.71/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_3733,plain,
% 3.71/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_2705,c_997]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_3752,plain,
% 3.71/1.03      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_993,c_3733]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_16,plain,
% 3.71/1.03      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 3.71/1.03      inference(cnf_transformation,[],[f81]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_988,plain,
% 3.71/1.03      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 3.71/1.03      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.71/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_3894,plain,
% 3.71/1.03      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_3752,c_988]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_3905,plain,
% 3.71/1.03      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_3894,c_2702]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_4041,plain,
% 3.71/1.03      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.71/1.03      inference(demodulation,[status(thm)],[c_3905,c_2705]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_2,plain,
% 3.71/1.03      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.71/1.03      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.71/1.03      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 3.71/1.03      inference(cnf_transformation,[],[f74]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_999,plain,
% 3.71/1.03      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 3.71/1.03      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 3.71/1.03      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 3.71/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_4468,plain,
% 3.71/1.03      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 3.71/1.03      | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_999,c_3733]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_10,plain,
% 3.71/1.03      ( r1_tarski(X0,X0) ),
% 3.71/1.03      inference(cnf_transformation,[],[f91]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_991,plain,
% 3.71/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 3.71/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_1335,plain,
% 3.71/1.03      ( k3_xboole_0(X0,X0) = X0 ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_991,c_990]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_5,plain,
% 3.71/1.03      ( r2_hidden(X0,X1)
% 3.71/1.03      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.71/1.03      inference(cnf_transformation,[],[f90]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_996,plain,
% 3.71/1.03      ( r2_hidden(X0,X1) = iProver_top
% 3.71/1.03      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 3.71/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_3604,plain,
% 3.71/1.03      ( r2_hidden(X0,X1) = iProver_top
% 3.71/1.03      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_1335,c_996]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_3734,plain,
% 3.71/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.71/1.03      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_1335,c_997]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_4182,plain,
% 3.71/1.03      ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 3.71/1.03      inference(global_propositional_subsumption,
% 3.71/1.03                [status(thm)],
% 3.71/1.03                [c_3604,c_3734]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_5969,plain,
% 3.71/1.03      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1)) = k1_xboole_0 ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_4468,c_4182]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_4189,plain,
% 3.71/1.03      ( r1_xboole_0(k5_xboole_0(X0,X0),X1) = iProver_top ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_993,c_4182]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_4731,plain,
% 3.71/1.03      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1)) = k5_xboole_0(X0,X0) ),
% 3.71/1.03      inference(superposition,[status(thm)],[c_4189,c_988]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_5981,plain,
% 3.71/1.03      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.71/1.03      inference(demodulation,[status(thm)],[c_5969,c_4731]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_7438,plain,
% 3.71/1.03      ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = sK3 ),
% 3.71/1.03      inference(demodulation,[status(thm)],[c_7437,c_4041,c_5981]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_22,negated_conjecture,
% 3.71/1.03      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
% 3.71/1.03      inference(cnf_transformation,[],[f87]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(c_2166,plain,
% 3.71/1.03      ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != sK3 ),
% 3.71/1.03      inference(demodulation,[status(thm)],[c_1613,c_22]) ).
% 3.71/1.03  
% 3.71/1.03  cnf(contradiction,plain,
% 3.71/1.03      ( $false ),
% 3.71/1.03      inference(minisat,[status(thm)],[c_7438,c_2166]) ).
% 3.71/1.03  
% 3.71/1.03  
% 3.71/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/1.03  
% 3.71/1.03  ------                               Statistics
% 3.71/1.03  
% 3.71/1.03  ------ General
% 3.71/1.03  
% 3.71/1.03  abstr_ref_over_cycles:                  0
% 3.71/1.03  abstr_ref_under_cycles:                 0
% 3.71/1.03  gc_basic_clause_elim:                   0
% 3.71/1.03  forced_gc_time:                         0
% 3.71/1.03  parsing_time:                           0.016
% 3.71/1.03  unif_index_cands_time:                  0.
% 3.71/1.03  unif_index_add_time:                    0.
% 3.71/1.03  orderings_time:                         0.
% 3.71/1.03  out_proof_time:                         0.025
% 3.71/1.03  total_time:                             0.266
% 3.71/1.03  num_of_symbols:                         43
% 3.71/1.03  num_of_terms:                           8686
% 3.71/1.03  
% 3.71/1.03  ------ Preprocessing
% 3.71/1.03  
% 3.71/1.03  num_of_splits:                          0
% 3.71/1.03  num_of_split_atoms:                     0
% 3.71/1.03  num_of_reused_defs:                     0
% 3.71/1.03  num_eq_ax_congr_red:                    24
% 3.71/1.03  num_of_sem_filtered_clauses:            1
% 3.71/1.03  num_of_subtypes:                        0
% 3.71/1.03  monotx_restored_types:                  0
% 3.71/1.03  sat_num_of_epr_types:                   0
% 3.71/1.03  sat_num_of_non_cyclic_types:            0
% 3.71/1.03  sat_guarded_non_collapsed_types:        0
% 3.71/1.03  num_pure_diseq_elim:                    0
% 3.71/1.03  simp_replaced_by:                       0
% 3.71/1.03  res_preprocessed:                       109
% 3.71/1.03  prep_upred:                             0
% 3.71/1.03  prep_unflattend:                        0
% 3.71/1.03  smt_new_axioms:                         0
% 3.71/1.03  pred_elim_cands:                        3
% 3.71/1.03  pred_elim:                              0
% 3.71/1.03  pred_elim_cl:                           0
% 3.71/1.03  pred_elim_cycles:                       2
% 3.71/1.03  merged_defs:                            8
% 3.71/1.03  merged_defs_ncl:                        0
% 3.71/1.03  bin_hyper_res:                          8
% 3.71/1.03  prep_cycles:                            4
% 3.71/1.03  pred_elim_time:                         0.002
% 3.71/1.03  splitting_time:                         0.
% 3.71/1.03  sem_filter_time:                        0.
% 3.71/1.03  monotx_time:                            0.001
% 3.71/1.03  subtype_inf_time:                       0.
% 3.71/1.03  
% 3.71/1.03  ------ Problem properties
% 3.71/1.03  
% 3.71/1.03  clauses:                                23
% 3.71/1.03  conjectures:                            2
% 3.71/1.03  epr:                                    4
% 3.71/1.03  horn:                                   17
% 3.71/1.03  ground:                                 2
% 3.71/1.03  unary:                                  7
% 3.71/1.03  binary:                                 9
% 3.71/1.03  lits:                                   47
% 3.71/1.03  lits_eq:                                12
% 3.71/1.03  fd_pure:                                0
% 3.71/1.03  fd_pseudo:                              0
% 3.71/1.03  fd_cond:                                0
% 3.71/1.03  fd_pseudo_cond:                         4
% 3.71/1.03  ac_symbols:                             0
% 3.71/1.03  
% 3.71/1.03  ------ Propositional Solver
% 3.71/1.03  
% 3.71/1.03  prop_solver_calls:                      29
% 3.71/1.03  prop_fast_solver_calls:                 626
% 3.71/1.03  smt_solver_calls:                       0
% 3.71/1.03  smt_fast_solver_calls:                  0
% 3.71/1.03  prop_num_of_clauses:                    2660
% 3.71/1.03  prop_preprocess_simplified:             8412
% 3.71/1.03  prop_fo_subsumed:                       4
% 3.71/1.03  prop_solver_time:                       0.
% 3.71/1.03  smt_solver_time:                        0.
% 3.71/1.03  smt_fast_solver_time:                   0.
% 3.71/1.03  prop_fast_solver_time:                  0.
% 3.71/1.03  prop_unsat_core_time:                   0.
% 3.71/1.03  
% 3.71/1.03  ------ QBF
% 3.71/1.03  
% 3.71/1.03  qbf_q_res:                              0
% 3.71/1.03  qbf_num_tautologies:                    0
% 3.71/1.03  qbf_prep_cycles:                        0
% 3.71/1.03  
% 3.71/1.03  ------ BMC1
% 3.71/1.03  
% 3.71/1.03  bmc1_current_bound:                     -1
% 3.71/1.03  bmc1_last_solved_bound:                 -1
% 3.71/1.03  bmc1_unsat_core_size:                   -1
% 3.71/1.03  bmc1_unsat_core_parents_size:           -1
% 3.71/1.03  bmc1_merge_next_fun:                    0
% 3.71/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.71/1.03  
% 3.71/1.03  ------ Instantiation
% 3.71/1.03  
% 3.71/1.03  inst_num_of_clauses:                    707
% 3.71/1.03  inst_num_in_passive:                    369
% 3.71/1.03  inst_num_in_active:                     311
% 3.71/1.03  inst_num_in_unprocessed:                27
% 3.71/1.03  inst_num_of_loops:                      360
% 3.71/1.03  inst_num_of_learning_restarts:          0
% 3.71/1.03  inst_num_moves_active_passive:          49
% 3.71/1.03  inst_lit_activity:                      0
% 3.71/1.03  inst_lit_activity_moves:                0
% 3.71/1.03  inst_num_tautologies:                   0
% 3.71/1.03  inst_num_prop_implied:                  0
% 3.71/1.03  inst_num_existing_simplified:           0
% 3.71/1.03  inst_num_eq_res_simplified:             0
% 3.71/1.03  inst_num_child_elim:                    0
% 3.71/1.03  inst_num_of_dismatching_blockings:      835
% 3.71/1.03  inst_num_of_non_proper_insts:           982
% 3.71/1.03  inst_num_of_duplicates:                 0
% 3.71/1.03  inst_inst_num_from_inst_to_res:         0
% 3.71/1.03  inst_dismatching_checking_time:         0.
% 3.71/1.03  
% 3.71/1.03  ------ Resolution
% 3.71/1.03  
% 3.71/1.03  res_num_of_clauses:                     0
% 3.71/1.03  res_num_in_passive:                     0
% 3.71/1.03  res_num_in_active:                      0
% 3.71/1.03  res_num_of_loops:                       113
% 3.71/1.03  res_forward_subset_subsumed:            34
% 3.71/1.03  res_backward_subset_subsumed:           2
% 3.71/1.03  res_forward_subsumed:                   0
% 3.71/1.03  res_backward_subsumed:                  0
% 3.71/1.03  res_forward_subsumption_resolution:     0
% 3.71/1.03  res_backward_subsumption_resolution:    0
% 3.71/1.03  res_clause_to_clause_subsumption:       435
% 3.71/1.03  res_orphan_elimination:                 0
% 3.71/1.03  res_tautology_del:                      86
% 3.71/1.03  res_num_eq_res_simplified:              0
% 3.71/1.03  res_num_sel_changes:                    0
% 3.71/1.03  res_moves_from_active_to_pass:          0
% 3.71/1.03  
% 3.71/1.03  ------ Superposition
% 3.71/1.03  
% 3.71/1.03  sup_time_total:                         0.
% 3.71/1.03  sup_time_generating:                    0.
% 3.71/1.03  sup_time_sim_full:                      0.
% 3.71/1.03  sup_time_sim_immed:                     0.
% 3.71/1.03  
% 3.71/1.03  sup_num_of_clauses:                     90
% 3.71/1.03  sup_num_in_active:                      49
% 3.71/1.03  sup_num_in_passive:                     41
% 3.71/1.03  sup_num_of_loops:                       71
% 3.71/1.03  sup_fw_superposition:                   233
% 3.71/1.03  sup_bw_superposition:                   194
% 3.71/1.03  sup_immediate_simplified:               122
% 3.71/1.03  sup_given_eliminated:                   2
% 3.71/1.03  comparisons_done:                       0
% 3.71/1.03  comparisons_avoided:                    0
% 3.71/1.03  
% 3.71/1.03  ------ Simplifications
% 3.71/1.03  
% 3.71/1.03  
% 3.71/1.03  sim_fw_subset_subsumed:                 6
% 3.71/1.03  sim_bw_subset_subsumed:                 1
% 3.71/1.03  sim_fw_subsumed:                        23
% 3.71/1.03  sim_bw_subsumed:                        2
% 3.71/1.03  sim_fw_subsumption_res:                 0
% 3.71/1.03  sim_bw_subsumption_res:                 0
% 3.71/1.03  sim_tautology_del:                      19
% 3.71/1.03  sim_eq_tautology_del:                   55
% 3.71/1.03  sim_eq_res_simp:                        1
% 3.71/1.03  sim_fw_demodulated:                     73
% 3.71/1.03  sim_bw_demodulated:                     21
% 3.71/1.03  sim_light_normalised:                   56
% 3.71/1.03  sim_joinable_taut:                      0
% 3.71/1.03  sim_joinable_simp:                      0
% 3.71/1.03  sim_ac_normalised:                      0
% 3.71/1.03  sim_smt_subsumption:                    0
% 3.71/1.03  
%------------------------------------------------------------------------------
