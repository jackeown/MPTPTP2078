%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:06 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 457 expanded)
%              Number of clauses        :   52 ( 112 expanded)
%              Number of leaves         :   21 ( 111 expanded)
%              Depth                    :   18
%              Number of atoms          :  315 (1137 expanded)
%              Number of equality atoms :  123 ( 439 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK3),sK4) != sK4
      & r2_hidden(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k2_xboole_0(k1_tarski(sK3),sK4) != sK4
    & r2_hidden(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f38])).

fof(f67,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f69])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f70])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f72])).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

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

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

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
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f43,f54])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f54])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f33])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f70])).

fof(f80,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f57,f71,f71,f54])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f79,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f55,f71])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f81,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f59,f70,f70])).

fof(f68,plain,(
    k2_xboole_0(k1_tarski(sK3),sK4) != sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4 ),
    inference(definition_unfolding,[],[f68,f71,f72])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_843,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_845,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_846,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2060,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_845,c_846])).

cnf(c_8594,plain,
    ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_843,c_2060])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_856,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_850,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2870,plain,
    ( r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X1) != iProver_top
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_856,c_850])).

cnf(c_12902,plain,
    ( r2_hidden(sK0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),sK4) != iProver_top
    | r1_tarski(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8594,c_2870])).

cnf(c_12917,plain,
    ( r2_hidden(sK0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),sK4) != iProver_top
    | r1_tarski(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12902,c_8594])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_849,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2031,plain,
    ( r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X0) = iProver_top
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_856,c_849])).

cnf(c_8740,plain,
    ( r2_hidden(sK0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r1_tarski(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8594,c_2031])).

cnf(c_8823,plain,
    ( r2_hidden(sK0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r1_tarski(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8740,c_8594])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_851,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8755,plain,
    ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_8594,c_851])).

cnf(c_13,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_847,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1042,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_847,c_846])).

cnf(c_2033,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_849])).

cnf(c_2871,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_850])).

cnf(c_4647,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2033,c_2871])).

cnf(c_11631,plain,
    ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8755,c_4647])).

cnf(c_11831,plain,
    ( r2_hidden(sK0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),sK4) = iProver_top
    | r1_tarski(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8823,c_11631])).

cnf(c_13131,plain,
    ( r1_tarski(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12917,c_11831])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_265,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_266,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_841,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_266])).

cnf(c_1146,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_841])).

cnf(c_1438,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_856,c_1146])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_848,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2342,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1438,c_848])).

cnf(c_13145,plain,
    ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13131,c_2342])).

cnf(c_16,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_8761,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_8594,c_16])).

cnf(c_13171,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_13145,c_8761])).

cnf(c_14,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_13173,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sK4 ),
    inference(demodulation,[status(thm)],[c_13171,c_14])).

cnf(c_18,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_21,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1251,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != sK4 ),
    inference(demodulation,[status(thm)],[c_18,c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13173,c_1251])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.53/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.01  
% 3.53/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.53/1.01  
% 3.53/1.01  ------  iProver source info
% 3.53/1.01  
% 3.53/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.53/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.53/1.01  git: non_committed_changes: false
% 3.53/1.01  git: last_make_outside_of_git: false
% 3.53/1.01  
% 3.53/1.01  ------ 
% 3.53/1.01  
% 3.53/1.01  ------ Input Options
% 3.53/1.01  
% 3.53/1.01  --out_options                           all
% 3.53/1.01  --tptp_safe_out                         true
% 3.53/1.01  --problem_path                          ""
% 3.53/1.01  --include_path                          ""
% 3.53/1.01  --clausifier                            res/vclausify_rel
% 3.53/1.01  --clausifier_options                    --mode clausify
% 3.53/1.01  --stdin                                 false
% 3.53/1.01  --stats_out                             all
% 3.53/1.01  
% 3.53/1.01  ------ General Options
% 3.53/1.01  
% 3.53/1.01  --fof                                   false
% 3.53/1.01  --time_out_real                         305.
% 3.53/1.01  --time_out_virtual                      -1.
% 3.53/1.01  --symbol_type_check                     false
% 3.53/1.01  --clausify_out                          false
% 3.53/1.01  --sig_cnt_out                           false
% 3.53/1.01  --trig_cnt_out                          false
% 3.53/1.01  --trig_cnt_out_tolerance                1.
% 3.53/1.01  --trig_cnt_out_sk_spl                   false
% 3.53/1.01  --abstr_cl_out                          false
% 3.53/1.01  
% 3.53/1.01  ------ Global Options
% 3.53/1.01  
% 3.53/1.01  --schedule                              default
% 3.53/1.01  --add_important_lit                     false
% 3.53/1.01  --prop_solver_per_cl                    1000
% 3.53/1.01  --min_unsat_core                        false
% 3.53/1.01  --soft_assumptions                      false
% 3.53/1.01  --soft_lemma_size                       3
% 3.53/1.01  --prop_impl_unit_size                   0
% 3.53/1.01  --prop_impl_unit                        []
% 3.53/1.01  --share_sel_clauses                     true
% 3.53/1.01  --reset_solvers                         false
% 3.53/1.01  --bc_imp_inh                            [conj_cone]
% 3.53/1.01  --conj_cone_tolerance                   3.
% 3.53/1.01  --extra_neg_conj                        none
% 3.53/1.01  --large_theory_mode                     true
% 3.53/1.01  --prolific_symb_bound                   200
% 3.53/1.01  --lt_threshold                          2000
% 3.53/1.01  --clause_weak_htbl                      true
% 3.53/1.01  --gc_record_bc_elim                     false
% 3.53/1.01  
% 3.53/1.01  ------ Preprocessing Options
% 3.53/1.01  
% 3.53/1.01  --preprocessing_flag                    true
% 3.53/1.01  --time_out_prep_mult                    0.1
% 3.53/1.01  --splitting_mode                        input
% 3.53/1.01  --splitting_grd                         true
% 3.53/1.01  --splitting_cvd                         false
% 3.53/1.01  --splitting_cvd_svl                     false
% 3.53/1.01  --splitting_nvd                         32
% 3.53/1.01  --sub_typing                            true
% 3.53/1.01  --prep_gs_sim                           true
% 3.53/1.01  --prep_unflatten                        true
% 3.53/1.01  --prep_res_sim                          true
% 3.53/1.01  --prep_upred                            true
% 3.53/1.01  --prep_sem_filter                       exhaustive
% 3.53/1.01  --prep_sem_filter_out                   false
% 3.53/1.01  --pred_elim                             true
% 3.53/1.01  --res_sim_input                         true
% 3.53/1.01  --eq_ax_congr_red                       true
% 3.53/1.01  --pure_diseq_elim                       true
% 3.53/1.01  --brand_transform                       false
% 3.53/1.01  --non_eq_to_eq                          false
% 3.53/1.01  --prep_def_merge                        true
% 3.53/1.01  --prep_def_merge_prop_impl              false
% 3.53/1.01  --prep_def_merge_mbd                    true
% 3.53/1.01  --prep_def_merge_tr_red                 false
% 3.53/1.01  --prep_def_merge_tr_cl                  false
% 3.53/1.01  --smt_preprocessing                     true
% 3.53/1.01  --smt_ac_axioms                         fast
% 3.53/1.01  --preprocessed_out                      false
% 3.53/1.01  --preprocessed_stats                    false
% 3.53/1.01  
% 3.53/1.01  ------ Abstraction refinement Options
% 3.53/1.01  
% 3.53/1.01  --abstr_ref                             []
% 3.53/1.01  --abstr_ref_prep                        false
% 3.53/1.01  --abstr_ref_until_sat                   false
% 3.53/1.01  --abstr_ref_sig_restrict                funpre
% 3.53/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/1.01  --abstr_ref_under                       []
% 3.53/1.01  
% 3.53/1.01  ------ SAT Options
% 3.53/1.01  
% 3.53/1.01  --sat_mode                              false
% 3.53/1.01  --sat_fm_restart_options                ""
% 3.53/1.01  --sat_gr_def                            false
% 3.53/1.01  --sat_epr_types                         true
% 3.53/1.01  --sat_non_cyclic_types                  false
% 3.53/1.01  --sat_finite_models                     false
% 3.53/1.01  --sat_fm_lemmas                         false
% 3.53/1.01  --sat_fm_prep                           false
% 3.53/1.01  --sat_fm_uc_incr                        true
% 3.53/1.01  --sat_out_model                         small
% 3.53/1.01  --sat_out_clauses                       false
% 3.53/1.01  
% 3.53/1.01  ------ QBF Options
% 3.53/1.01  
% 3.53/1.01  --qbf_mode                              false
% 3.53/1.01  --qbf_elim_univ                         false
% 3.53/1.01  --qbf_dom_inst                          none
% 3.53/1.01  --qbf_dom_pre_inst                      false
% 3.53/1.01  --qbf_sk_in                             false
% 3.53/1.01  --qbf_pred_elim                         true
% 3.53/1.01  --qbf_split                             512
% 3.53/1.01  
% 3.53/1.01  ------ BMC1 Options
% 3.53/1.01  
% 3.53/1.01  --bmc1_incremental                      false
% 3.53/1.01  --bmc1_axioms                           reachable_all
% 3.53/1.01  --bmc1_min_bound                        0
% 3.53/1.01  --bmc1_max_bound                        -1
% 3.53/1.01  --bmc1_max_bound_default                -1
% 3.53/1.01  --bmc1_symbol_reachability              true
% 3.53/1.01  --bmc1_property_lemmas                  false
% 3.53/1.01  --bmc1_k_induction                      false
% 3.53/1.01  --bmc1_non_equiv_states                 false
% 3.53/1.01  --bmc1_deadlock                         false
% 3.53/1.01  --bmc1_ucm                              false
% 3.53/1.01  --bmc1_add_unsat_core                   none
% 3.53/1.01  --bmc1_unsat_core_children              false
% 3.53/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/1.01  --bmc1_out_stat                         full
% 3.53/1.01  --bmc1_ground_init                      false
% 3.53/1.01  --bmc1_pre_inst_next_state              false
% 3.53/1.01  --bmc1_pre_inst_state                   false
% 3.53/1.01  --bmc1_pre_inst_reach_state             false
% 3.53/1.01  --bmc1_out_unsat_core                   false
% 3.53/1.01  --bmc1_aig_witness_out                  false
% 3.53/1.01  --bmc1_verbose                          false
% 3.53/1.01  --bmc1_dump_clauses_tptp                false
% 3.53/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.53/1.01  --bmc1_dump_file                        -
% 3.53/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.53/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.53/1.01  --bmc1_ucm_extend_mode                  1
% 3.53/1.01  --bmc1_ucm_init_mode                    2
% 3.53/1.01  --bmc1_ucm_cone_mode                    none
% 3.53/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.53/1.01  --bmc1_ucm_relax_model                  4
% 3.53/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.53/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/1.01  --bmc1_ucm_layered_model                none
% 3.53/1.01  --bmc1_ucm_max_lemma_size               10
% 3.53/1.01  
% 3.53/1.01  ------ AIG Options
% 3.53/1.01  
% 3.53/1.01  --aig_mode                              false
% 3.53/1.01  
% 3.53/1.01  ------ Instantiation Options
% 3.53/1.01  
% 3.53/1.01  --instantiation_flag                    true
% 3.53/1.01  --inst_sos_flag                         false
% 3.53/1.01  --inst_sos_phase                        true
% 3.53/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/1.01  --inst_lit_sel_side                     num_symb
% 3.53/1.01  --inst_solver_per_active                1400
% 3.53/1.01  --inst_solver_calls_frac                1.
% 3.53/1.01  --inst_passive_queue_type               priority_queues
% 3.53/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/1.01  --inst_passive_queues_freq              [25;2]
% 3.53/1.01  --inst_dismatching                      true
% 3.53/1.01  --inst_eager_unprocessed_to_passive     true
% 3.53/1.01  --inst_prop_sim_given                   true
% 3.53/1.01  --inst_prop_sim_new                     false
% 3.53/1.01  --inst_subs_new                         false
% 3.53/1.01  --inst_eq_res_simp                      false
% 3.53/1.01  --inst_subs_given                       false
% 3.53/1.01  --inst_orphan_elimination               true
% 3.53/1.01  --inst_learning_loop_flag               true
% 3.53/1.01  --inst_learning_start                   3000
% 3.53/1.01  --inst_learning_factor                  2
% 3.53/1.01  --inst_start_prop_sim_after_learn       3
% 3.53/1.01  --inst_sel_renew                        solver
% 3.53/1.01  --inst_lit_activity_flag                true
% 3.53/1.01  --inst_restr_to_given                   false
% 3.53/1.01  --inst_activity_threshold               500
% 3.53/1.01  --inst_out_proof                        true
% 3.53/1.01  
% 3.53/1.01  ------ Resolution Options
% 3.53/1.01  
% 3.53/1.01  --resolution_flag                       true
% 3.53/1.01  --res_lit_sel                           adaptive
% 3.53/1.01  --res_lit_sel_side                      none
% 3.53/1.01  --res_ordering                          kbo
% 3.53/1.01  --res_to_prop_solver                    active
% 3.53/1.01  --res_prop_simpl_new                    false
% 3.53/1.01  --res_prop_simpl_given                  true
% 3.53/1.01  --res_passive_queue_type                priority_queues
% 3.53/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/1.01  --res_passive_queues_freq               [15;5]
% 3.53/1.01  --res_forward_subs                      full
% 3.53/1.01  --res_backward_subs                     full
% 3.53/1.01  --res_forward_subs_resolution           true
% 3.53/1.01  --res_backward_subs_resolution          true
% 3.53/1.01  --res_orphan_elimination                true
% 3.53/1.01  --res_time_limit                        2.
% 3.53/1.01  --res_out_proof                         true
% 3.53/1.01  
% 3.53/1.01  ------ Superposition Options
% 3.53/1.01  
% 3.53/1.01  --superposition_flag                    true
% 3.53/1.01  --sup_passive_queue_type                priority_queues
% 3.53/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.53/1.01  --demod_completeness_check              fast
% 3.53/1.01  --demod_use_ground                      true
% 3.53/1.01  --sup_to_prop_solver                    passive
% 3.53/1.01  --sup_prop_simpl_new                    true
% 3.53/1.01  --sup_prop_simpl_given                  true
% 3.53/1.01  --sup_fun_splitting                     false
% 3.53/1.01  --sup_smt_interval                      50000
% 3.53/1.01  
% 3.53/1.01  ------ Superposition Simplification Setup
% 3.53/1.01  
% 3.53/1.01  --sup_indices_passive                   []
% 3.53/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.01  --sup_full_bw                           [BwDemod]
% 3.53/1.01  --sup_immed_triv                        [TrivRules]
% 3.53/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.01  --sup_immed_bw_main                     []
% 3.53/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.01  
% 3.53/1.01  ------ Combination Options
% 3.53/1.01  
% 3.53/1.01  --comb_res_mult                         3
% 3.53/1.01  --comb_sup_mult                         2
% 3.53/1.01  --comb_inst_mult                        10
% 3.53/1.01  
% 3.53/1.01  ------ Debug Options
% 3.53/1.01  
% 3.53/1.01  --dbg_backtrace                         false
% 3.53/1.01  --dbg_dump_prop_clauses                 false
% 3.53/1.01  --dbg_dump_prop_clauses_file            -
% 3.53/1.01  --dbg_out_stat                          false
% 3.53/1.01  ------ Parsing...
% 3.53/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/1.01  
% 3.53/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.53/1.01  
% 3.53/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/1.01  
% 3.53/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/1.01  ------ Proving...
% 3.53/1.01  ------ Problem Properties 
% 3.53/1.01  
% 3.53/1.01  
% 3.53/1.01  clauses                                 21
% 3.53/1.01  conjectures                             2
% 3.53/1.01  EPR                                     4
% 3.53/1.01  Horn                                    16
% 3.53/1.01  unary                                   7
% 3.53/1.01  binary                                  8
% 3.53/1.01  lits                                    42
% 3.53/1.01  lits eq                                 9
% 3.53/1.01  fd_pure                                 0
% 3.53/1.01  fd_pseudo                               0
% 3.53/1.01  fd_cond                                 0
% 3.53/1.01  fd_pseudo_cond                          4
% 3.53/1.01  AC symbols                              0
% 3.53/1.01  
% 3.53/1.01  ------ Schedule dynamic 5 is on 
% 3.53/1.01  
% 3.53/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.53/1.01  
% 3.53/1.01  
% 3.53/1.01  ------ 
% 3.53/1.01  Current options:
% 3.53/1.01  ------ 
% 3.53/1.01  
% 3.53/1.01  ------ Input Options
% 3.53/1.01  
% 3.53/1.01  --out_options                           all
% 3.53/1.01  --tptp_safe_out                         true
% 3.53/1.01  --problem_path                          ""
% 3.53/1.01  --include_path                          ""
% 3.53/1.01  --clausifier                            res/vclausify_rel
% 3.53/1.01  --clausifier_options                    --mode clausify
% 3.53/1.01  --stdin                                 false
% 3.53/1.01  --stats_out                             all
% 3.53/1.01  
% 3.53/1.01  ------ General Options
% 3.53/1.01  
% 3.53/1.01  --fof                                   false
% 3.53/1.01  --time_out_real                         305.
% 3.53/1.01  --time_out_virtual                      -1.
% 3.53/1.01  --symbol_type_check                     false
% 3.53/1.01  --clausify_out                          false
% 3.53/1.01  --sig_cnt_out                           false
% 3.53/1.01  --trig_cnt_out                          false
% 3.53/1.01  --trig_cnt_out_tolerance                1.
% 3.53/1.01  --trig_cnt_out_sk_spl                   false
% 3.53/1.01  --abstr_cl_out                          false
% 3.53/1.01  
% 3.53/1.01  ------ Global Options
% 3.53/1.01  
% 3.53/1.01  --schedule                              default
% 3.53/1.01  --add_important_lit                     false
% 3.53/1.01  --prop_solver_per_cl                    1000
% 3.53/1.01  --min_unsat_core                        false
% 3.53/1.01  --soft_assumptions                      false
% 3.53/1.01  --soft_lemma_size                       3
% 3.53/1.01  --prop_impl_unit_size                   0
% 3.53/1.01  --prop_impl_unit                        []
% 3.53/1.01  --share_sel_clauses                     true
% 3.53/1.01  --reset_solvers                         false
% 3.53/1.01  --bc_imp_inh                            [conj_cone]
% 3.53/1.01  --conj_cone_tolerance                   3.
% 3.53/1.01  --extra_neg_conj                        none
% 3.53/1.01  --large_theory_mode                     true
% 3.53/1.01  --prolific_symb_bound                   200
% 3.53/1.01  --lt_threshold                          2000
% 3.53/1.01  --clause_weak_htbl                      true
% 3.53/1.01  --gc_record_bc_elim                     false
% 3.53/1.01  
% 3.53/1.01  ------ Preprocessing Options
% 3.53/1.01  
% 3.53/1.01  --preprocessing_flag                    true
% 3.53/1.01  --time_out_prep_mult                    0.1
% 3.53/1.01  --splitting_mode                        input
% 3.53/1.01  --splitting_grd                         true
% 3.53/1.01  --splitting_cvd                         false
% 3.53/1.01  --splitting_cvd_svl                     false
% 3.53/1.01  --splitting_nvd                         32
% 3.53/1.01  --sub_typing                            true
% 3.53/1.01  --prep_gs_sim                           true
% 3.53/1.01  --prep_unflatten                        true
% 3.53/1.01  --prep_res_sim                          true
% 3.53/1.01  --prep_upred                            true
% 3.53/1.01  --prep_sem_filter                       exhaustive
% 3.53/1.01  --prep_sem_filter_out                   false
% 3.53/1.01  --pred_elim                             true
% 3.53/1.01  --res_sim_input                         true
% 3.53/1.01  --eq_ax_congr_red                       true
% 3.53/1.01  --pure_diseq_elim                       true
% 3.53/1.01  --brand_transform                       false
% 3.53/1.01  --non_eq_to_eq                          false
% 3.53/1.01  --prep_def_merge                        true
% 3.53/1.01  --prep_def_merge_prop_impl              false
% 3.53/1.01  --prep_def_merge_mbd                    true
% 3.53/1.01  --prep_def_merge_tr_red                 false
% 3.53/1.01  --prep_def_merge_tr_cl                  false
% 3.53/1.01  --smt_preprocessing                     true
% 3.53/1.01  --smt_ac_axioms                         fast
% 3.53/1.01  --preprocessed_out                      false
% 3.53/1.01  --preprocessed_stats                    false
% 3.53/1.01  
% 3.53/1.01  ------ Abstraction refinement Options
% 3.53/1.01  
% 3.53/1.01  --abstr_ref                             []
% 3.53/1.01  --abstr_ref_prep                        false
% 3.53/1.01  --abstr_ref_until_sat                   false
% 3.53/1.01  --abstr_ref_sig_restrict                funpre
% 3.53/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/1.01  --abstr_ref_under                       []
% 3.53/1.01  
% 3.53/1.01  ------ SAT Options
% 3.53/1.01  
% 3.53/1.01  --sat_mode                              false
% 3.53/1.01  --sat_fm_restart_options                ""
% 3.53/1.01  --sat_gr_def                            false
% 3.53/1.01  --sat_epr_types                         true
% 3.53/1.01  --sat_non_cyclic_types                  false
% 3.53/1.01  --sat_finite_models                     false
% 3.53/1.01  --sat_fm_lemmas                         false
% 3.53/1.01  --sat_fm_prep                           false
% 3.53/1.01  --sat_fm_uc_incr                        true
% 3.53/1.01  --sat_out_model                         small
% 3.53/1.01  --sat_out_clauses                       false
% 3.53/1.01  
% 3.53/1.01  ------ QBF Options
% 3.53/1.01  
% 3.53/1.01  --qbf_mode                              false
% 3.53/1.01  --qbf_elim_univ                         false
% 3.53/1.01  --qbf_dom_inst                          none
% 3.53/1.01  --qbf_dom_pre_inst                      false
% 3.53/1.01  --qbf_sk_in                             false
% 3.53/1.01  --qbf_pred_elim                         true
% 3.53/1.01  --qbf_split                             512
% 3.53/1.01  
% 3.53/1.01  ------ BMC1 Options
% 3.53/1.01  
% 3.53/1.01  --bmc1_incremental                      false
% 3.53/1.01  --bmc1_axioms                           reachable_all
% 3.53/1.01  --bmc1_min_bound                        0
% 3.53/1.01  --bmc1_max_bound                        -1
% 3.53/1.01  --bmc1_max_bound_default                -1
% 3.53/1.01  --bmc1_symbol_reachability              true
% 3.53/1.01  --bmc1_property_lemmas                  false
% 3.53/1.01  --bmc1_k_induction                      false
% 3.53/1.01  --bmc1_non_equiv_states                 false
% 3.53/1.01  --bmc1_deadlock                         false
% 3.53/1.01  --bmc1_ucm                              false
% 3.53/1.01  --bmc1_add_unsat_core                   none
% 3.53/1.01  --bmc1_unsat_core_children              false
% 3.53/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/1.01  --bmc1_out_stat                         full
% 3.53/1.01  --bmc1_ground_init                      false
% 3.53/1.01  --bmc1_pre_inst_next_state              false
% 3.53/1.01  --bmc1_pre_inst_state                   false
% 3.53/1.01  --bmc1_pre_inst_reach_state             false
% 3.53/1.01  --bmc1_out_unsat_core                   false
% 3.53/1.01  --bmc1_aig_witness_out                  false
% 3.53/1.01  --bmc1_verbose                          false
% 3.53/1.01  --bmc1_dump_clauses_tptp                false
% 3.53/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.53/1.01  --bmc1_dump_file                        -
% 3.53/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.53/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.53/1.01  --bmc1_ucm_extend_mode                  1
% 3.53/1.01  --bmc1_ucm_init_mode                    2
% 3.53/1.01  --bmc1_ucm_cone_mode                    none
% 3.53/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.53/1.01  --bmc1_ucm_relax_model                  4
% 3.53/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.53/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/1.01  --bmc1_ucm_layered_model                none
% 3.53/1.01  --bmc1_ucm_max_lemma_size               10
% 3.53/1.01  
% 3.53/1.01  ------ AIG Options
% 3.53/1.01  
% 3.53/1.01  --aig_mode                              false
% 3.53/1.01  
% 3.53/1.01  ------ Instantiation Options
% 3.53/1.01  
% 3.53/1.01  --instantiation_flag                    true
% 3.53/1.01  --inst_sos_flag                         false
% 3.53/1.01  --inst_sos_phase                        true
% 3.53/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/1.01  --inst_lit_sel_side                     none
% 3.53/1.01  --inst_solver_per_active                1400
% 3.53/1.01  --inst_solver_calls_frac                1.
% 3.53/1.01  --inst_passive_queue_type               priority_queues
% 3.53/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/1.01  --inst_passive_queues_freq              [25;2]
% 3.53/1.01  --inst_dismatching                      true
% 3.53/1.01  --inst_eager_unprocessed_to_passive     true
% 3.53/1.01  --inst_prop_sim_given                   true
% 3.53/1.01  --inst_prop_sim_new                     false
% 3.53/1.01  --inst_subs_new                         false
% 3.53/1.01  --inst_eq_res_simp                      false
% 3.53/1.01  --inst_subs_given                       false
% 3.53/1.01  --inst_orphan_elimination               true
% 3.53/1.01  --inst_learning_loop_flag               true
% 3.53/1.01  --inst_learning_start                   3000
% 3.53/1.01  --inst_learning_factor                  2
% 3.53/1.01  --inst_start_prop_sim_after_learn       3
% 3.53/1.01  --inst_sel_renew                        solver
% 3.53/1.01  --inst_lit_activity_flag                true
% 3.53/1.01  --inst_restr_to_given                   false
% 3.53/1.01  --inst_activity_threshold               500
% 3.53/1.01  --inst_out_proof                        true
% 3.53/1.01  
% 3.53/1.01  ------ Resolution Options
% 3.53/1.01  
% 3.53/1.01  --resolution_flag                       false
% 3.53/1.01  --res_lit_sel                           adaptive
% 3.53/1.01  --res_lit_sel_side                      none
% 3.53/1.01  --res_ordering                          kbo
% 3.53/1.01  --res_to_prop_solver                    active
% 3.53/1.01  --res_prop_simpl_new                    false
% 3.53/1.01  --res_prop_simpl_given                  true
% 3.53/1.01  --res_passive_queue_type                priority_queues
% 3.53/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/1.01  --res_passive_queues_freq               [15;5]
% 3.53/1.01  --res_forward_subs                      full
% 3.53/1.01  --res_backward_subs                     full
% 3.53/1.01  --res_forward_subs_resolution           true
% 3.53/1.01  --res_backward_subs_resolution          true
% 3.53/1.01  --res_orphan_elimination                true
% 3.53/1.01  --res_time_limit                        2.
% 3.53/1.01  --res_out_proof                         true
% 3.53/1.01  
% 3.53/1.01  ------ Superposition Options
% 3.53/1.01  
% 3.53/1.01  --superposition_flag                    true
% 3.53/1.01  --sup_passive_queue_type                priority_queues
% 3.53/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.53/1.01  --demod_completeness_check              fast
% 3.53/1.01  --demod_use_ground                      true
% 3.53/1.01  --sup_to_prop_solver                    passive
% 3.53/1.01  --sup_prop_simpl_new                    true
% 3.53/1.01  --sup_prop_simpl_given                  true
% 3.53/1.01  --sup_fun_splitting                     false
% 3.53/1.01  --sup_smt_interval                      50000
% 3.53/1.01  
% 3.53/1.01  ------ Superposition Simplification Setup
% 3.53/1.01  
% 3.53/1.01  --sup_indices_passive                   []
% 3.53/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.01  --sup_full_bw                           [BwDemod]
% 3.53/1.01  --sup_immed_triv                        [TrivRules]
% 3.53/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.01  --sup_immed_bw_main                     []
% 3.53/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.01  
% 3.53/1.01  ------ Combination Options
% 3.53/1.01  
% 3.53/1.01  --comb_res_mult                         3
% 3.53/1.01  --comb_sup_mult                         2
% 3.53/1.01  --comb_inst_mult                        10
% 3.53/1.01  
% 3.53/1.01  ------ Debug Options
% 3.53/1.01  
% 3.53/1.01  --dbg_backtrace                         false
% 3.53/1.01  --dbg_dump_prop_clauses                 false
% 3.53/1.01  --dbg_dump_prop_clauses_file            -
% 3.53/1.01  --dbg_out_stat                          false
% 3.53/1.01  
% 3.53/1.01  
% 3.53/1.01  
% 3.53/1.01  
% 3.53/1.01  ------ Proving...
% 3.53/1.01  
% 3.53/1.01  
% 3.53/1.01  % SZS status Theorem for theBenchmark.p
% 3.53/1.01  
% 3.53/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/1.01  
% 3.53/1.01  fof(f17,conjecture,(
% 3.53/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.01  
% 3.53/1.01  fof(f18,negated_conjecture,(
% 3.53/1.01    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.53/1.01    inference(negated_conjecture,[],[f17])).
% 3.53/1.01  
% 3.53/1.01  fof(f23,plain,(
% 3.53/1.01    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 3.53/1.01    inference(ennf_transformation,[],[f18])).
% 3.53/1.01  
% 3.53/1.01  fof(f38,plain,(
% 3.53/1.01    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK3),sK4) != sK4 & r2_hidden(sK3,sK4))),
% 3.53/1.01    introduced(choice_axiom,[])).
% 3.53/1.01  
% 3.53/1.01  fof(f39,plain,(
% 3.53/1.01    k2_xboole_0(k1_tarski(sK3),sK4) != sK4 & r2_hidden(sK3,sK4)),
% 3.53/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f38])).
% 3.53/1.01  
% 3.53/1.01  fof(f67,plain,(
% 3.53/1.01    r2_hidden(sK3,sK4)),
% 3.53/1.01    inference(cnf_transformation,[],[f39])).
% 3.53/1.01  
% 3.53/1.01  fof(f15,axiom,(
% 3.53/1.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.01  
% 3.53/1.01  fof(f37,plain,(
% 3.53/1.01    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.53/1.01    inference(nnf_transformation,[],[f15])).
% 3.53/1.01  
% 3.53/1.01  fof(f65,plain,(
% 3.53/1.01    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.53/1.01    inference(cnf_transformation,[],[f37])).
% 3.53/1.01  
% 3.53/1.01  fof(f11,axiom,(
% 3.53/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.01  
% 3.53/1.01  fof(f60,plain,(
% 3.53/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.53/1.01    inference(cnf_transformation,[],[f11])).
% 3.53/1.01  
% 3.53/1.01  fof(f12,axiom,(
% 3.53/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.01  
% 3.53/1.01  fof(f61,plain,(
% 3.53/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.53/1.01    inference(cnf_transformation,[],[f12])).
% 3.53/1.01  
% 3.53/1.01  fof(f13,axiom,(
% 3.53/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.01  
% 3.53/1.01  fof(f62,plain,(
% 3.53/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.53/1.01    inference(cnf_transformation,[],[f13])).
% 3.53/1.01  
% 3.53/1.01  fof(f14,axiom,(
% 3.53/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.01  
% 3.53/1.01  fof(f63,plain,(
% 3.53/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.53/1.01    inference(cnf_transformation,[],[f14])).
% 3.53/1.01  
% 3.53/1.01  fof(f69,plain,(
% 3.53/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.53/1.01    inference(definition_unfolding,[],[f62,f63])).
% 3.53/1.01  
% 3.53/1.01  fof(f70,plain,(
% 3.53/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.53/1.01    inference(definition_unfolding,[],[f61,f69])).
% 3.53/1.01  
% 3.53/1.01  fof(f72,plain,(
% 3.53/1.01    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.53/1.01    inference(definition_unfolding,[],[f60,f70])).
% 3.53/1.01  
% 3.53/1.01  fof(f82,plain,(
% 3.53/1.01    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.53/1.01    inference(definition_unfolding,[],[f65,f72])).
% 3.53/1.01  
% 3.53/1.01  fof(f7,axiom,(
% 3.53/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.01  
% 3.53/1.01  fof(f22,plain,(
% 3.53/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.53/1.01    inference(ennf_transformation,[],[f7])).
% 3.53/1.01  
% 3.53/1.01  fof(f56,plain,(
% 3.53/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.53/1.01    inference(cnf_transformation,[],[f22])).
% 3.53/1.01  
% 3.53/1.01  fof(f1,axiom,(
% 3.53/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.01  
% 3.53/1.01  fof(f20,plain,(
% 3.53/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.53/1.01    inference(ennf_transformation,[],[f1])).
% 3.53/1.01  
% 3.53/1.01  fof(f24,plain,(
% 3.53/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.53/1.01    inference(nnf_transformation,[],[f20])).
% 3.53/1.01  
% 3.53/1.01  fof(f25,plain,(
% 3.53/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.53/1.01    inference(rectify,[],[f24])).
% 3.53/1.01  
% 3.53/1.01  fof(f26,plain,(
% 3.53/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.53/1.01    introduced(choice_axiom,[])).
% 3.53/1.01  
% 3.53/1.01  fof(f27,plain,(
% 3.53/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.53/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 3.53/1.01  
% 3.53/1.01  fof(f41,plain,(
% 3.53/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.53/1.01    inference(cnf_transformation,[],[f27])).
% 3.53/1.01  
% 3.53/1.01  fof(f2,axiom,(
% 3.53/1.01    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.01  
% 3.53/1.01  fof(f28,plain,(
% 3.53/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.53/1.01    inference(nnf_transformation,[],[f2])).
% 3.53/1.01  
% 3.53/1.01  fof(f29,plain,(
% 3.53/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.53/1.01    inference(flattening,[],[f28])).
% 3.53/1.01  
% 3.53/1.01  fof(f30,plain,(
% 3.53/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.53/1.01    inference(rectify,[],[f29])).
% 3.53/1.01  
% 3.53/1.01  fof(f31,plain,(
% 3.53/1.01    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.53/1.02    introduced(choice_axiom,[])).
% 3.53/1.02  
% 3.53/1.02  fof(f32,plain,(
% 3.53/1.02    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.53/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 3.53/1.02  
% 3.53/1.02  fof(f44,plain,(
% 3.53/1.02    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.53/1.02    inference(cnf_transformation,[],[f32])).
% 3.53/1.02  
% 3.53/1.02  fof(f5,axiom,(
% 3.53/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.02  
% 3.53/1.02  fof(f54,plain,(
% 3.53/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.53/1.02    inference(cnf_transformation,[],[f5])).
% 3.53/1.02  
% 3.53/1.02  fof(f77,plain,(
% 3.53/1.02    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.53/1.02    inference(definition_unfolding,[],[f44,f54])).
% 3.53/1.02  
% 3.53/1.02  fof(f86,plain,(
% 3.53/1.02    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.53/1.02    inference(equality_resolution,[],[f77])).
% 3.53/1.02  
% 3.53/1.02  fof(f43,plain,(
% 3.53/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.53/1.02    inference(cnf_transformation,[],[f32])).
% 3.53/1.02  
% 3.53/1.02  fof(f78,plain,(
% 3.53/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.53/1.02    inference(definition_unfolding,[],[f43,f54])).
% 3.53/1.02  
% 3.53/1.02  fof(f87,plain,(
% 3.53/1.02    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.53/1.02    inference(equality_resolution,[],[f78])).
% 3.53/1.02  
% 3.53/1.02  fof(f45,plain,(
% 3.53/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.53/1.02    inference(cnf_transformation,[],[f32])).
% 3.53/1.02  
% 3.53/1.02  fof(f76,plain,(
% 3.53/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.53/1.02    inference(definition_unfolding,[],[f45,f54])).
% 3.53/1.02  
% 3.53/1.02  fof(f85,plain,(
% 3.53/1.02    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.53/1.02    inference(equality_resolution,[],[f76])).
% 3.53/1.02  
% 3.53/1.02  fof(f4,axiom,(
% 3.53/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.02  
% 3.53/1.02  fof(f35,plain,(
% 3.53/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.53/1.02    inference(nnf_transformation,[],[f4])).
% 3.53/1.02  
% 3.53/1.02  fof(f36,plain,(
% 3.53/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.53/1.02    inference(flattening,[],[f35])).
% 3.53/1.02  
% 3.53/1.02  fof(f51,plain,(
% 3.53/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.53/1.02    inference(cnf_transformation,[],[f36])).
% 3.53/1.02  
% 3.53/1.02  fof(f89,plain,(
% 3.53/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.53/1.02    inference(equality_resolution,[],[f51])).
% 3.53/1.02  
% 3.53/1.02  fof(f3,axiom,(
% 3.53/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.02  
% 3.53/1.02  fof(f19,plain,(
% 3.53/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.53/1.02    inference(rectify,[],[f3])).
% 3.53/1.02  
% 3.53/1.02  fof(f21,plain,(
% 3.53/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.53/1.02    inference(ennf_transformation,[],[f19])).
% 3.53/1.02  
% 3.53/1.02  fof(f33,plain,(
% 3.53/1.02    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 3.53/1.02    introduced(choice_axiom,[])).
% 3.53/1.02  
% 3.53/1.02  fof(f34,plain,(
% 3.53/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.53/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f33])).
% 3.53/1.02  
% 3.53/1.02  fof(f50,plain,(
% 3.53/1.02    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.53/1.02    inference(cnf_transformation,[],[f34])).
% 3.53/1.02  
% 3.53/1.02  fof(f9,axiom,(
% 3.53/1.02    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.02  
% 3.53/1.02  fof(f58,plain,(
% 3.53/1.02    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.53/1.02    inference(cnf_transformation,[],[f9])).
% 3.53/1.02  
% 3.53/1.02  fof(f53,plain,(
% 3.53/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.53/1.02    inference(cnf_transformation,[],[f36])).
% 3.53/1.02  
% 3.53/1.02  fof(f8,axiom,(
% 3.53/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.02  
% 3.53/1.02  fof(f57,plain,(
% 3.53/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.53/1.02    inference(cnf_transformation,[],[f8])).
% 3.53/1.02  
% 3.53/1.02  fof(f16,axiom,(
% 3.53/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.02  
% 3.53/1.02  fof(f66,plain,(
% 3.53/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.53/1.02    inference(cnf_transformation,[],[f16])).
% 3.53/1.02  
% 3.53/1.02  fof(f71,plain,(
% 3.53/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.53/1.02    inference(definition_unfolding,[],[f66,f70])).
% 3.53/1.02  
% 3.53/1.02  fof(f80,plain,(
% 3.53/1.02    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 3.53/1.02    inference(definition_unfolding,[],[f57,f71,f71,f54])).
% 3.53/1.02  
% 3.53/1.02  fof(f6,axiom,(
% 3.53/1.02    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.02  
% 3.53/1.02  fof(f55,plain,(
% 3.53/1.02    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.53/1.02    inference(cnf_transformation,[],[f6])).
% 3.53/1.02  
% 3.53/1.02  fof(f79,plain,(
% 3.53/1.02    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 3.53/1.02    inference(definition_unfolding,[],[f55,f71])).
% 3.53/1.02  
% 3.53/1.02  fof(f10,axiom,(
% 3.53/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.02  
% 3.53/1.02  fof(f59,plain,(
% 3.53/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.53/1.02    inference(cnf_transformation,[],[f10])).
% 3.53/1.02  
% 3.53/1.02  fof(f81,plain,(
% 3.53/1.02    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 3.53/1.02    inference(definition_unfolding,[],[f59,f70,f70])).
% 3.53/1.02  
% 3.53/1.02  fof(f68,plain,(
% 3.53/1.02    k2_xboole_0(k1_tarski(sK3),sK4) != sK4),
% 3.53/1.02    inference(cnf_transformation,[],[f39])).
% 3.53/1.02  
% 3.53/1.02  fof(f84,plain,(
% 3.53/1.02    k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4),
% 3.53/1.02    inference(definition_unfolding,[],[f68,f71,f72])).
% 3.53/1.02  
% 3.53/1.02  cnf(c_22,negated_conjecture,
% 3.53/1.02      ( r2_hidden(sK3,sK4) ),
% 3.53/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_843,plain,
% 3.53/1.02      ( r2_hidden(sK3,sK4) = iProver_top ),
% 3.53/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_19,plain,
% 3.53/1.02      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 3.53/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_845,plain,
% 3.53/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.53/1.02      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
% 3.53/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_15,plain,
% 3.53/1.02      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.53/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_846,plain,
% 3.53/1.02      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.53/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_2060,plain,
% 3.53/1.02      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
% 3.53/1.02      | r2_hidden(X0,X1) != iProver_top ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_845,c_846]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_8594,plain,
% 3.53/1.02      ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_843,c_2060]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1,plain,
% 3.53/1.02      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.53/1.02      inference(cnf_transformation,[],[f41]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_856,plain,
% 3.53/1.02      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.53/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 3.53/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_7,plain,
% 3.53/1.02      ( ~ r2_hidden(X0,X1)
% 3.53/1.02      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.53/1.02      inference(cnf_transformation,[],[f86]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_850,plain,
% 3.53/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.53/1.02      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 3.53/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_2870,plain,
% 3.53/1.02      ( r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X1) != iProver_top
% 3.53/1.02      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_856,c_850]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_12902,plain,
% 3.53/1.02      ( r2_hidden(sK0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),sK4) != iProver_top
% 3.53/1.02      | r1_tarski(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),X0) = iProver_top ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_8594,c_2870]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_12917,plain,
% 3.53/1.02      ( r2_hidden(sK0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),sK4) != iProver_top
% 3.53/1.02      | r1_tarski(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0) = iProver_top ),
% 3.53/1.02      inference(light_normalisation,[status(thm)],[c_12902,c_8594]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_8,plain,
% 3.53/1.02      ( r2_hidden(X0,X1)
% 3.53/1.02      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.53/1.02      inference(cnf_transformation,[],[f87]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_849,plain,
% 3.53/1.02      ( r2_hidden(X0,X1) = iProver_top
% 3.53/1.02      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 3.53/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_2031,plain,
% 3.53/1.02      ( r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X0) = iProver_top
% 3.53/1.02      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_856,c_849]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_8740,plain,
% 3.53/1.02      ( r2_hidden(sK0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 3.53/1.02      | r1_tarski(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)),X0) = iProver_top ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_8594,c_2031]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_8823,plain,
% 3.53/1.02      ( r2_hidden(sK0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 3.53/1.02      | r1_tarski(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0) = iProver_top ),
% 3.53/1.02      inference(light_normalisation,[status(thm)],[c_8740,c_8594]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_6,plain,
% 3.53/1.02      ( ~ r2_hidden(X0,X1)
% 3.53/1.02      | r2_hidden(X0,X2)
% 3.53/1.02      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.53/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_851,plain,
% 3.53/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.53/1.02      | r2_hidden(X0,X2) = iProver_top
% 3.53/1.02      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 3.53/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_8755,plain,
% 3.53/1.02      ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 3.53/1.02      | r2_hidden(X0,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = iProver_top
% 3.53/1.02      | r2_hidden(X0,sK4) = iProver_top ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_8594,c_851]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_13,plain,
% 3.53/1.02      ( r1_tarski(X0,X0) ),
% 3.53/1.02      inference(cnf_transformation,[],[f89]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_847,plain,
% 3.53/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 3.53/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1042,plain,
% 3.53/1.02      ( k3_xboole_0(X0,X0) = X0 ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_847,c_846]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_2033,plain,
% 3.53/1.02      ( r2_hidden(X0,X1) = iProver_top
% 3.53/1.02      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_1042,c_849]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_2871,plain,
% 3.53/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.53/1.02      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_1042,c_850]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_4647,plain,
% 3.53/1.02      ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 3.53/1.02      inference(global_propositional_subsumption,
% 3.53/1.02                [status(thm)],
% 3.53/1.02                [c_2033,c_2871]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_11631,plain,
% 3.53/1.02      ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 3.53/1.02      | r2_hidden(X0,sK4) = iProver_top ),
% 3.53/1.02      inference(forward_subsumption_resolution,
% 3.53/1.02                [status(thm)],
% 3.53/1.02                [c_8755,c_4647]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_11831,plain,
% 3.53/1.02      ( r2_hidden(sK0(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0),sK4) = iProver_top
% 3.53/1.02      | r1_tarski(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0) = iProver_top ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_8823,c_11631]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_13131,plain,
% 3.53/1.02      ( r1_tarski(k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0) = iProver_top ),
% 3.53/1.02      inference(global_propositional_subsumption,
% 3.53/1.02                [status(thm)],
% 3.53/1.02                [c_12917,c_11831]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_9,plain,
% 3.53/1.02      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 3.53/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_17,plain,
% 3.53/1.02      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.53/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_265,plain,
% 3.53/1.02      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 3.53/1.02      | X3 != X1
% 3.53/1.02      | k1_xboole_0 != X2 ),
% 3.53/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_266,plain,
% 3.53/1.02      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 3.53/1.02      inference(unflattening,[status(thm)],[c_265]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_841,plain,
% 3.53/1.02      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 3.53/1.02      inference(predicate_to_equality,[status(thm)],[c_266]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1146,plain,
% 3.53/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_1042,c_841]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1438,plain,
% 3.53/1.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_856,c_1146]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_11,plain,
% 3.53/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.53/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_848,plain,
% 3.53/1.02      ( X0 = X1
% 3.53/1.02      | r1_tarski(X1,X0) != iProver_top
% 3.53/1.02      | r1_tarski(X0,X1) != iProver_top ),
% 3.53/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_2342,plain,
% 3.53/1.02      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_1438,c_848]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_13145,plain,
% 3.53/1.02      ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0 ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_13131,c_2342]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_16,plain,
% 3.53/1.02      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 3.53/1.02      inference(cnf_transformation,[],[f80]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_8761,plain,
% 3.53/1.02      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 3.53/1.02      inference(superposition,[status(thm)],[c_8594,c_16]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_13171,plain,
% 3.53/1.02      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k1_xboole_0)) ),
% 3.53/1.02      inference(demodulation,[status(thm)],[c_13145,c_8761]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_14,plain,
% 3.53/1.02      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 3.53/1.02      inference(cnf_transformation,[],[f79]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_13173,plain,
% 3.53/1.02      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sK4 ),
% 3.53/1.02      inference(demodulation,[status(thm)],[c_13171,c_14]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_18,plain,
% 3.53/1.02      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 3.53/1.02      inference(cnf_transformation,[],[f81]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_21,negated_conjecture,
% 3.53/1.02      ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4 ),
% 3.53/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(c_1251,plain,
% 3.53/1.02      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != sK4 ),
% 3.53/1.02      inference(demodulation,[status(thm)],[c_18,c_21]) ).
% 3.53/1.02  
% 3.53/1.02  cnf(contradiction,plain,
% 3.53/1.02      ( $false ),
% 3.53/1.02      inference(minisat,[status(thm)],[c_13173,c_1251]) ).
% 3.53/1.02  
% 3.53/1.02  
% 3.53/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/1.02  
% 3.53/1.02  ------                               Statistics
% 3.53/1.02  
% 3.53/1.02  ------ General
% 3.53/1.02  
% 3.53/1.02  abstr_ref_over_cycles:                  0
% 3.53/1.02  abstr_ref_under_cycles:                 0
% 3.53/1.02  gc_basic_clause_elim:                   0
% 3.53/1.02  forced_gc_time:                         0
% 3.53/1.02  parsing_time:                           0.009
% 3.53/1.02  unif_index_cands_time:                  0.
% 3.53/1.02  unif_index_add_time:                    0.
% 3.53/1.02  orderings_time:                         0.
% 3.53/1.02  out_proof_time:                         0.008
% 3.53/1.02  total_time:                             0.475
% 3.53/1.02  num_of_symbols:                         44
% 3.53/1.02  num_of_terms:                           15898
% 3.53/1.02  
% 3.53/1.02  ------ Preprocessing
% 3.53/1.02  
% 3.53/1.02  num_of_splits:                          0
% 3.53/1.02  num_of_split_atoms:                     0
% 3.53/1.02  num_of_reused_defs:                     0
% 3.53/1.02  num_eq_ax_congr_red:                    32
% 3.53/1.02  num_of_sem_filtered_clauses:            1
% 3.53/1.02  num_of_subtypes:                        0
% 3.53/1.02  monotx_restored_types:                  0
% 3.53/1.02  sat_num_of_epr_types:                   0
% 3.53/1.02  sat_num_of_non_cyclic_types:            0
% 3.53/1.02  sat_guarded_non_collapsed_types:        0
% 3.53/1.02  num_pure_diseq_elim:                    0
% 3.53/1.02  simp_replaced_by:                       0
% 3.53/1.02  res_preprocessed:                       102
% 3.53/1.02  prep_upred:                             0
% 3.53/1.02  prep_unflattend:                        2
% 3.53/1.02  smt_new_axioms:                         0
% 3.53/1.02  pred_elim_cands:                        2
% 3.53/1.02  pred_elim:                              1
% 3.53/1.02  pred_elim_cl:                           1
% 3.53/1.02  pred_elim_cycles:                       3
% 3.53/1.02  merged_defs:                            8
% 3.53/1.02  merged_defs_ncl:                        0
% 3.53/1.02  bin_hyper_res:                          8
% 3.53/1.02  prep_cycles:                            4
% 3.53/1.02  pred_elim_time:                         0.001
% 3.53/1.02  splitting_time:                         0.
% 3.53/1.02  sem_filter_time:                        0.
% 3.53/1.02  monotx_time:                            0.
% 3.53/1.02  subtype_inf_time:                       0.
% 3.53/1.02  
% 3.53/1.02  ------ Problem properties
% 3.53/1.02  
% 3.53/1.02  clauses:                                21
% 3.53/1.02  conjectures:                            2
% 3.53/1.02  epr:                                    4
% 3.53/1.02  horn:                                   16
% 3.53/1.02  ground:                                 2
% 3.53/1.02  unary:                                  7
% 3.53/1.02  binary:                                 8
% 3.53/1.02  lits:                                   42
% 3.53/1.02  lits_eq:                                9
% 3.53/1.02  fd_pure:                                0
% 3.53/1.02  fd_pseudo:                              0
% 3.53/1.02  fd_cond:                                0
% 3.53/1.02  fd_pseudo_cond:                         4
% 3.53/1.02  ac_symbols:                             0
% 3.53/1.02  
% 3.53/1.02  ------ Propositional Solver
% 3.53/1.02  
% 3.53/1.02  prop_solver_calls:                      29
% 3.53/1.02  prop_fast_solver_calls:                 655
% 3.53/1.02  smt_solver_calls:                       0
% 3.53/1.02  smt_fast_solver_calls:                  0
% 3.53/1.02  prop_num_of_clauses:                    4900
% 3.53/1.02  prop_preprocess_simplified:             11307
% 3.53/1.02  prop_fo_subsumed:                       6
% 3.53/1.02  prop_solver_time:                       0.
% 3.53/1.02  smt_solver_time:                        0.
% 3.53/1.02  smt_fast_solver_time:                   0.
% 3.53/1.02  prop_fast_solver_time:                  0.
% 3.53/1.02  prop_unsat_core_time:                   0.
% 3.53/1.02  
% 3.53/1.02  ------ QBF
% 3.53/1.02  
% 3.53/1.02  qbf_q_res:                              0
% 3.53/1.02  qbf_num_tautologies:                    0
% 3.53/1.02  qbf_prep_cycles:                        0
% 3.53/1.02  
% 3.53/1.02  ------ BMC1
% 3.53/1.02  
% 3.53/1.02  bmc1_current_bound:                     -1
% 3.53/1.02  bmc1_last_solved_bound:                 -1
% 3.53/1.02  bmc1_unsat_core_size:                   -1
% 3.53/1.02  bmc1_unsat_core_parents_size:           -1
% 3.53/1.02  bmc1_merge_next_fun:                    0
% 3.53/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.53/1.02  
% 3.53/1.02  ------ Instantiation
% 3.53/1.02  
% 3.53/1.02  inst_num_of_clauses:                    1217
% 3.53/1.02  inst_num_in_passive:                    574
% 3.53/1.02  inst_num_in_active:                     454
% 3.53/1.02  inst_num_in_unprocessed:                189
% 3.53/1.02  inst_num_of_loops:                      530
% 3.53/1.02  inst_num_of_learning_restarts:          0
% 3.53/1.02  inst_num_moves_active_passive:          74
% 3.53/1.02  inst_lit_activity:                      0
% 3.53/1.02  inst_lit_activity_moves:                0
% 3.53/1.02  inst_num_tautologies:                   0
% 3.53/1.02  inst_num_prop_implied:                  0
% 3.53/1.02  inst_num_existing_simplified:           0
% 3.53/1.02  inst_num_eq_res_simplified:             0
% 3.53/1.02  inst_num_child_elim:                    0
% 3.53/1.02  inst_num_of_dismatching_blockings:      1073
% 3.53/1.02  inst_num_of_non_proper_insts:           1408
% 3.53/1.02  inst_num_of_duplicates:                 0
% 3.53/1.02  inst_inst_num_from_inst_to_res:         0
% 3.53/1.02  inst_dismatching_checking_time:         0.
% 3.53/1.02  
% 3.53/1.02  ------ Resolution
% 3.53/1.02  
% 3.53/1.02  res_num_of_clauses:                     0
% 3.53/1.02  res_num_in_passive:                     0
% 3.53/1.02  res_num_in_active:                      0
% 3.53/1.02  res_num_of_loops:                       106
% 3.53/1.02  res_forward_subset_subsumed:            72
% 3.53/1.02  res_backward_subset_subsumed:           0
% 3.53/1.02  res_forward_subsumed:                   0
% 3.53/1.02  res_backward_subsumed:                  0
% 3.53/1.02  res_forward_subsumption_resolution:     0
% 3.53/1.02  res_backward_subsumption_resolution:    0
% 3.53/1.02  res_clause_to_clause_subsumption:       2064
% 3.53/1.02  res_orphan_elimination:                 0
% 3.53/1.02  res_tautology_del:                      151
% 3.53/1.02  res_num_eq_res_simplified:              0
% 3.53/1.02  res_num_sel_changes:                    0
% 3.53/1.02  res_moves_from_active_to_pass:          0
% 3.53/1.02  
% 3.53/1.02  ------ Superposition
% 3.53/1.02  
% 3.53/1.02  sup_time_total:                         0.
% 3.53/1.02  sup_time_generating:                    0.
% 3.53/1.02  sup_time_sim_full:                      0.
% 3.53/1.02  sup_time_sim_immed:                     0.
% 3.53/1.02  
% 3.53/1.02  sup_num_of_clauses:                     296
% 3.53/1.02  sup_num_in_active:                      93
% 3.53/1.02  sup_num_in_passive:                     203
% 3.53/1.02  sup_num_of_loops:                       105
% 3.53/1.02  sup_fw_superposition:                   348
% 3.53/1.02  sup_bw_superposition:                   430
% 3.53/1.02  sup_immediate_simplified:               357
% 3.53/1.02  sup_given_eliminated:                   2
% 3.53/1.02  comparisons_done:                       0
% 3.53/1.02  comparisons_avoided:                    0
% 3.53/1.02  
% 3.53/1.02  ------ Simplifications
% 3.53/1.02  
% 3.53/1.02  
% 3.53/1.02  sim_fw_subset_subsumed:                 47
% 3.53/1.02  sim_bw_subset_subsumed:                 8
% 3.53/1.02  sim_fw_subsumed:                        166
% 3.53/1.02  sim_bw_subsumed:                        5
% 3.53/1.02  sim_fw_subsumption_res:                 1
% 3.53/1.02  sim_bw_subsumption_res:                 0
% 3.53/1.02  sim_tautology_del:                      11
% 3.53/1.02  sim_eq_tautology_del:                   18
% 3.53/1.02  sim_eq_res_simp:                        1
% 3.53/1.02  sim_fw_demodulated:                     28
% 3.53/1.02  sim_bw_demodulated:                     14
% 3.53/1.02  sim_light_normalised:                   189
% 3.53/1.02  sim_joinable_taut:                      0
% 3.53/1.02  sim_joinable_simp:                      0
% 3.53/1.02  sim_ac_normalised:                      0
% 3.53/1.02  sim_smt_subsumption:                    0
% 3.53/1.02  
%------------------------------------------------------------------------------
