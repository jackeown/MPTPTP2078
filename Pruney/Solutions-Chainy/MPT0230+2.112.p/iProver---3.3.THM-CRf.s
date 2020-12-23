%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:56 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 918 expanded)
%              Number of clauses        :   51 ( 183 expanded)
%              Number of leaves         :   22 ( 271 expanded)
%              Depth                    :   21
%              Number of atoms          :  311 (1626 expanded)
%              Number of equality atoms :  222 (1255 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f31])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f29])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f43,f48])).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK3 != sK5
      & sK3 != sK4
      & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( sK3 != sK5
    & sK3 != sK4
    & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f39])).

fof(f69,plain,(
    r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f62,f73])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f73,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f63,f72])).

fof(f91,plain,(
    r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f69,f74,f73])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f52,f65,f74])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f72])).

fof(f98,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f56,f72])).

fof(f92,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f86])).

fof(f93,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f92])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f54,f72])).

fof(f96,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f88])).

fof(f97,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f96])).

fof(f71,plain,(
    sK3 != sK5 ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1664,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1666,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3438,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1666])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1663,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2856,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1663])).

cnf(c_3922,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3438,c_2856])).

cnf(c_3926,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1664,c_3922])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1993,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_225,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK5) != X0
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != X1
    | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_226,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_1994,plain,
    ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_226,c_0])).

cnf(c_2009,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(demodulation,[status(thm)],[c_1993,c_1994])).

cnf(c_1,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2427,plain,
    ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK5),k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK4,sK4,sK4,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_2009,c_1])).

cnf(c_4084,plain,
    ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK5),k1_xboole_0) = k3_enumset1(sK4,sK4,sK4,sK5,sK3) ),
    inference(demodulation,[status(thm)],[c_3926,c_2427])).

cnf(c_4293,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK5,sK3) = k3_enumset1(sK4,sK4,sK4,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_8,c_4084])).

cnf(c_4755,plain,
    ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK5,sK3),k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(sK4,sK4,sK4,sK5,sK3))) = k3_enumset1(sK4,sK4,sK4,sK5,X0) ),
    inference(superposition,[status(thm)],[c_4293,c_1])).

cnf(c_4770,plain,
    ( k3_enumset1(sK4,sK4,sK5,sK3,X0) = k3_enumset1(sK4,sK4,sK4,sK5,X0) ),
    inference(demodulation,[status(thm)],[c_4755,c_1])).

cnf(c_4772,plain,
    ( k3_enumset1(sK4,sK4,sK5,sK3,sK3) = k3_enumset1(sK4,sK4,sK4,sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_4770,c_4293])).

cnf(c_6712,plain,
    ( k5_xboole_0(k3_enumset1(sK4,sK4,sK5,sK3,X0),k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(sK4,sK4,sK5,sK3,X0))) = k3_enumset1(sK4,sK4,sK5,X0,X1) ),
    inference(superposition,[status(thm)],[c_4770,c_1])).

cnf(c_6776,plain,
    ( k3_enumset1(sK4,sK5,sK3,X0,X1) = k3_enumset1(sK4,sK4,sK5,X0,X1) ),
    inference(demodulation,[status(thm)],[c_6712,c_1])).

cnf(c_9121,plain,
    ( k3_enumset1(sK4,sK5,sK3,sK3,sK3) = k3_enumset1(sK4,sK4,sK4,sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_4772,c_6776])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1654,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9144,plain,
    ( sK4 = X0
    | sK5 = X0
    | r2_hidden(X0,k3_enumset1(sK4,sK5,sK3,sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9121,c_1654])).

cnf(c_9239,plain,
    ( sK4 = sK3
    | sK5 = sK3
    | r2_hidden(sK3,k3_enumset1(sK4,sK5,sK3,sK3,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9144])).

cnf(c_15,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1657,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6722,plain,
    ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK5,sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4770,c_1657])).

cnf(c_6836,plain,
    ( r2_hidden(X0,k3_enumset1(sK4,sK5,sK3,sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6722,c_6776])).

cnf(c_6953,plain,
    ( r2_hidden(sK3,k3_enumset1(sK4,sK5,sK3,sK3,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6836])).

cnf(c_1327,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1792,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1327])).

cnf(c_1793,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1792])).

cnf(c_1790,plain,
    ( sK5 != X0
    | sK3 != X0
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_1327])).

cnf(c_1791,plain,
    ( sK5 != sK3
    | sK3 = sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1790])).

cnf(c_17,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_29,plain,
    ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_26,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_20,negated_conjecture,
    ( sK3 != sK5 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_21,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f70])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9239,c_6953,c_1793,c_1791,c_29,c_26,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:22 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 3.20/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.20/0.99  
% 3.20/0.99  ------  iProver source info
% 3.20/0.99  
% 3.20/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.20/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.20/0.99  git: non_committed_changes: false
% 3.20/0.99  git: last_make_outside_of_git: false
% 3.20/0.99  
% 3.20/0.99  ------ 
% 3.20/0.99  
% 3.20/0.99  ------ Input Options
% 3.20/0.99  
% 3.20/0.99  --out_options                           all
% 3.20/0.99  --tptp_safe_out                         true
% 3.20/0.99  --problem_path                          ""
% 3.20/0.99  --include_path                          ""
% 3.20/0.99  --clausifier                            res/vclausify_rel
% 3.20/0.99  --clausifier_options                    --mode clausify
% 3.20/0.99  --stdin                                 false
% 3.20/0.99  --stats_out                             all
% 3.20/0.99  
% 3.20/0.99  ------ General Options
% 3.20/0.99  
% 3.20/0.99  --fof                                   false
% 3.20/0.99  --time_out_real                         305.
% 3.20/0.99  --time_out_virtual                      -1.
% 3.20/0.99  --symbol_type_check                     false
% 3.20/0.99  --clausify_out                          false
% 3.20/0.99  --sig_cnt_out                           false
% 3.20/0.99  --trig_cnt_out                          false
% 3.20/0.99  --trig_cnt_out_tolerance                1.
% 3.20/0.99  --trig_cnt_out_sk_spl                   false
% 3.20/0.99  --abstr_cl_out                          false
% 3.20/0.99  
% 3.20/0.99  ------ Global Options
% 3.20/0.99  
% 3.20/0.99  --schedule                              default
% 3.20/0.99  --add_important_lit                     false
% 3.20/0.99  --prop_solver_per_cl                    1000
% 3.20/0.99  --min_unsat_core                        false
% 3.20/0.99  --soft_assumptions                      false
% 3.20/0.99  --soft_lemma_size                       3
% 3.20/0.99  --prop_impl_unit_size                   0
% 3.20/0.99  --prop_impl_unit                        []
% 3.20/0.99  --share_sel_clauses                     true
% 3.20/0.99  --reset_solvers                         false
% 3.20/0.99  --bc_imp_inh                            [conj_cone]
% 3.20/0.99  --conj_cone_tolerance                   3.
% 3.20/0.99  --extra_neg_conj                        none
% 3.20/0.99  --large_theory_mode                     true
% 3.20/0.99  --prolific_symb_bound                   200
% 3.20/0.99  --lt_threshold                          2000
% 3.20/0.99  --clause_weak_htbl                      true
% 3.20/0.99  --gc_record_bc_elim                     false
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing Options
% 3.20/0.99  
% 3.20/0.99  --preprocessing_flag                    true
% 3.20/0.99  --time_out_prep_mult                    0.1
% 3.20/0.99  --splitting_mode                        input
% 3.20/0.99  --splitting_grd                         true
% 3.20/0.99  --splitting_cvd                         false
% 3.20/0.99  --splitting_cvd_svl                     false
% 3.20/0.99  --splitting_nvd                         32
% 3.20/0.99  --sub_typing                            true
% 3.20/0.99  --prep_gs_sim                           true
% 3.20/0.99  --prep_unflatten                        true
% 3.20/0.99  --prep_res_sim                          true
% 3.20/0.99  --prep_upred                            true
% 3.20/0.99  --prep_sem_filter                       exhaustive
% 3.20/0.99  --prep_sem_filter_out                   false
% 3.20/0.99  --pred_elim                             true
% 3.20/0.99  --res_sim_input                         true
% 3.20/0.99  --eq_ax_congr_red                       true
% 3.20/0.99  --pure_diseq_elim                       true
% 3.20/0.99  --brand_transform                       false
% 3.20/0.99  --non_eq_to_eq                          false
% 3.20/0.99  --prep_def_merge                        true
% 3.20/0.99  --prep_def_merge_prop_impl              false
% 3.20/0.99  --prep_def_merge_mbd                    true
% 3.20/0.99  --prep_def_merge_tr_red                 false
% 3.20/0.99  --prep_def_merge_tr_cl                  false
% 3.20/0.99  --smt_preprocessing                     true
% 3.20/0.99  --smt_ac_axioms                         fast
% 3.20/0.99  --preprocessed_out                      false
% 3.20/0.99  --preprocessed_stats                    false
% 3.20/0.99  
% 3.20/0.99  ------ Abstraction refinement Options
% 3.20/0.99  
% 3.20/0.99  --abstr_ref                             []
% 3.20/0.99  --abstr_ref_prep                        false
% 3.20/0.99  --abstr_ref_until_sat                   false
% 3.20/0.99  --abstr_ref_sig_restrict                funpre
% 3.20/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.99  --abstr_ref_under                       []
% 3.20/0.99  
% 3.20/0.99  ------ SAT Options
% 3.20/0.99  
% 3.20/0.99  --sat_mode                              false
% 3.20/0.99  --sat_fm_restart_options                ""
% 3.20/0.99  --sat_gr_def                            false
% 3.20/0.99  --sat_epr_types                         true
% 3.20/0.99  --sat_non_cyclic_types                  false
% 3.20/0.99  --sat_finite_models                     false
% 3.20/0.99  --sat_fm_lemmas                         false
% 3.20/0.99  --sat_fm_prep                           false
% 3.20/0.99  --sat_fm_uc_incr                        true
% 3.20/0.99  --sat_out_model                         small
% 3.20/0.99  --sat_out_clauses                       false
% 3.20/0.99  
% 3.20/0.99  ------ QBF Options
% 3.20/0.99  
% 3.20/0.99  --qbf_mode                              false
% 3.20/0.99  --qbf_elim_univ                         false
% 3.20/0.99  --qbf_dom_inst                          none
% 3.20/0.99  --qbf_dom_pre_inst                      false
% 3.20/0.99  --qbf_sk_in                             false
% 3.20/0.99  --qbf_pred_elim                         true
% 3.20/0.99  --qbf_split                             512
% 3.20/0.99  
% 3.20/0.99  ------ BMC1 Options
% 3.20/0.99  
% 3.20/0.99  --bmc1_incremental                      false
% 3.20/0.99  --bmc1_axioms                           reachable_all
% 3.20/0.99  --bmc1_min_bound                        0
% 3.20/0.99  --bmc1_max_bound                        -1
% 3.20/0.99  --bmc1_max_bound_default                -1
% 3.20/0.99  --bmc1_symbol_reachability              true
% 3.20/0.99  --bmc1_property_lemmas                  false
% 3.20/0.99  --bmc1_k_induction                      false
% 3.20/0.99  --bmc1_non_equiv_states                 false
% 3.20/0.99  --bmc1_deadlock                         false
% 3.20/0.99  --bmc1_ucm                              false
% 3.20/0.99  --bmc1_add_unsat_core                   none
% 3.20/0.99  --bmc1_unsat_core_children              false
% 3.20/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.99  --bmc1_out_stat                         full
% 3.20/0.99  --bmc1_ground_init                      false
% 3.20/0.99  --bmc1_pre_inst_next_state              false
% 3.20/0.99  --bmc1_pre_inst_state                   false
% 3.20/0.99  --bmc1_pre_inst_reach_state             false
% 3.20/0.99  --bmc1_out_unsat_core                   false
% 3.20/0.99  --bmc1_aig_witness_out                  false
% 3.20/0.99  --bmc1_verbose                          false
% 3.20/0.99  --bmc1_dump_clauses_tptp                false
% 3.20/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.99  --bmc1_dump_file                        -
% 3.20/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.99  --bmc1_ucm_extend_mode                  1
% 3.20/0.99  --bmc1_ucm_init_mode                    2
% 3.20/0.99  --bmc1_ucm_cone_mode                    none
% 3.20/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.99  --bmc1_ucm_relax_model                  4
% 3.20/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.99  --bmc1_ucm_layered_model                none
% 3.20/0.99  --bmc1_ucm_max_lemma_size               10
% 3.20/0.99  
% 3.20/0.99  ------ AIG Options
% 3.20/0.99  
% 3.20/0.99  --aig_mode                              false
% 3.20/0.99  
% 3.20/0.99  ------ Instantiation Options
% 3.20/0.99  
% 3.20/0.99  --instantiation_flag                    true
% 3.20/0.99  --inst_sos_flag                         false
% 3.20/0.99  --inst_sos_phase                        true
% 3.20/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel_side                     num_symb
% 3.20/0.99  --inst_solver_per_active                1400
% 3.20/0.99  --inst_solver_calls_frac                1.
% 3.20/0.99  --inst_passive_queue_type               priority_queues
% 3.20/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.99  --inst_passive_queues_freq              [25;2]
% 3.20/0.99  --inst_dismatching                      true
% 3.20/0.99  --inst_eager_unprocessed_to_passive     true
% 3.20/0.99  --inst_prop_sim_given                   true
% 3.20/0.99  --inst_prop_sim_new                     false
% 3.20/0.99  --inst_subs_new                         false
% 3.20/0.99  --inst_eq_res_simp                      false
% 3.20/0.99  --inst_subs_given                       false
% 3.20/0.99  --inst_orphan_elimination               true
% 3.20/0.99  --inst_learning_loop_flag               true
% 3.20/0.99  --inst_learning_start                   3000
% 3.20/0.99  --inst_learning_factor                  2
% 3.20/0.99  --inst_start_prop_sim_after_learn       3
% 3.20/0.99  --inst_sel_renew                        solver
% 3.20/0.99  --inst_lit_activity_flag                true
% 3.20/0.99  --inst_restr_to_given                   false
% 3.20/0.99  --inst_activity_threshold               500
% 3.20/0.99  --inst_out_proof                        true
% 3.20/0.99  
% 3.20/0.99  ------ Resolution Options
% 3.20/0.99  
% 3.20/0.99  --resolution_flag                       true
% 3.20/0.99  --res_lit_sel                           adaptive
% 3.20/0.99  --res_lit_sel_side                      none
% 3.20/0.99  --res_ordering                          kbo
% 3.20/0.99  --res_to_prop_solver                    active
% 3.20/0.99  --res_prop_simpl_new                    false
% 3.20/0.99  --res_prop_simpl_given                  true
% 3.20/0.99  --res_passive_queue_type                priority_queues
% 3.20/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.99  --res_passive_queues_freq               [15;5]
% 3.20/0.99  --res_forward_subs                      full
% 3.20/0.99  --res_backward_subs                     full
% 3.20/0.99  --res_forward_subs_resolution           true
% 3.20/0.99  --res_backward_subs_resolution          true
% 3.20/0.99  --res_orphan_elimination                true
% 3.20/0.99  --res_time_limit                        2.
% 3.20/0.99  --res_out_proof                         true
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Options
% 3.20/0.99  
% 3.20/0.99  --superposition_flag                    true
% 3.20/0.99  --sup_passive_queue_type                priority_queues
% 3.20/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.99  --demod_completeness_check              fast
% 3.20/0.99  --demod_use_ground                      true
% 3.20/0.99  --sup_to_prop_solver                    passive
% 3.20/0.99  --sup_prop_simpl_new                    true
% 3.20/0.99  --sup_prop_simpl_given                  true
% 3.20/0.99  --sup_fun_splitting                     false
% 3.20/0.99  --sup_smt_interval                      50000
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Simplification Setup
% 3.20/0.99  
% 3.20/0.99  --sup_indices_passive                   []
% 3.20/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_full_bw                           [BwDemod]
% 3.20/0.99  --sup_immed_triv                        [TrivRules]
% 3.20/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_immed_bw_main                     []
% 3.20/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.99  
% 3.20/0.99  ------ Combination Options
% 3.20/0.99  
% 3.20/0.99  --comb_res_mult                         3
% 3.20/0.99  --comb_sup_mult                         2
% 3.20/0.99  --comb_inst_mult                        10
% 3.20/0.99  
% 3.20/0.99  ------ Debug Options
% 3.20/0.99  
% 3.20/0.99  --dbg_backtrace                         false
% 3.20/0.99  --dbg_dump_prop_clauses                 false
% 3.20/0.99  --dbg_dump_prop_clauses_file            -
% 3.20/0.99  --dbg_out_stat                          false
% 3.20/0.99  ------ Parsing...
% 3.20/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.20/0.99  ------ Proving...
% 3.20/0.99  ------ Problem Properties 
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  clauses                                 22
% 3.20/0.99  conjectures                             2
% 3.20/0.99  EPR                                     2
% 3.20/0.99  Horn                                    18
% 3.20/0.99  unary                                   12
% 3.20/0.99  binary                                  5
% 3.20/0.99  lits                                    40
% 3.20/0.99  lits eq                                 25
% 3.20/0.99  fd_pure                                 0
% 3.20/0.99  fd_pseudo                               0
% 3.20/0.99  fd_cond                                 1
% 3.20/0.99  fd_pseudo_cond                          4
% 3.20/0.99  AC symbols                              0
% 3.20/0.99  
% 3.20/0.99  ------ Schedule dynamic 5 is on 
% 3.20/0.99  
% 3.20/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  ------ 
% 3.20/0.99  Current options:
% 3.20/0.99  ------ 
% 3.20/0.99  
% 3.20/0.99  ------ Input Options
% 3.20/0.99  
% 3.20/0.99  --out_options                           all
% 3.20/0.99  --tptp_safe_out                         true
% 3.20/0.99  --problem_path                          ""
% 3.20/0.99  --include_path                          ""
% 3.20/0.99  --clausifier                            res/vclausify_rel
% 3.20/0.99  --clausifier_options                    --mode clausify
% 3.20/0.99  --stdin                                 false
% 3.20/0.99  --stats_out                             all
% 3.20/0.99  
% 3.20/0.99  ------ General Options
% 3.20/0.99  
% 3.20/0.99  --fof                                   false
% 3.20/0.99  --time_out_real                         305.
% 3.20/0.99  --time_out_virtual                      -1.
% 3.20/0.99  --symbol_type_check                     false
% 3.20/0.99  --clausify_out                          false
% 3.20/0.99  --sig_cnt_out                           false
% 3.20/0.99  --trig_cnt_out                          false
% 3.20/0.99  --trig_cnt_out_tolerance                1.
% 3.20/0.99  --trig_cnt_out_sk_spl                   false
% 3.20/0.99  --abstr_cl_out                          false
% 3.20/0.99  
% 3.20/0.99  ------ Global Options
% 3.20/0.99  
% 3.20/0.99  --schedule                              default
% 3.20/0.99  --add_important_lit                     false
% 3.20/0.99  --prop_solver_per_cl                    1000
% 3.20/0.99  --min_unsat_core                        false
% 3.20/0.99  --soft_assumptions                      false
% 3.20/0.99  --soft_lemma_size                       3
% 3.20/0.99  --prop_impl_unit_size                   0
% 3.20/0.99  --prop_impl_unit                        []
% 3.20/0.99  --share_sel_clauses                     true
% 3.20/0.99  --reset_solvers                         false
% 3.20/0.99  --bc_imp_inh                            [conj_cone]
% 3.20/0.99  --conj_cone_tolerance                   3.
% 3.20/0.99  --extra_neg_conj                        none
% 3.20/0.99  --large_theory_mode                     true
% 3.20/0.99  --prolific_symb_bound                   200
% 3.20/0.99  --lt_threshold                          2000
% 3.20/0.99  --clause_weak_htbl                      true
% 3.20/0.99  --gc_record_bc_elim                     false
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing Options
% 3.20/0.99  
% 3.20/0.99  --preprocessing_flag                    true
% 3.20/0.99  --time_out_prep_mult                    0.1
% 3.20/0.99  --splitting_mode                        input
% 3.20/0.99  --splitting_grd                         true
% 3.20/0.99  --splitting_cvd                         false
% 3.20/0.99  --splitting_cvd_svl                     false
% 3.20/0.99  --splitting_nvd                         32
% 3.20/0.99  --sub_typing                            true
% 3.20/0.99  --prep_gs_sim                           true
% 3.20/0.99  --prep_unflatten                        true
% 3.20/0.99  --prep_res_sim                          true
% 3.20/0.99  --prep_upred                            true
% 3.20/0.99  --prep_sem_filter                       exhaustive
% 3.20/0.99  --prep_sem_filter_out                   false
% 3.20/0.99  --pred_elim                             true
% 3.20/0.99  --res_sim_input                         true
% 3.20/0.99  --eq_ax_congr_red                       true
% 3.20/0.99  --pure_diseq_elim                       true
% 3.20/0.99  --brand_transform                       false
% 3.20/0.99  --non_eq_to_eq                          false
% 3.20/0.99  --prep_def_merge                        true
% 3.20/0.99  --prep_def_merge_prop_impl              false
% 3.20/0.99  --prep_def_merge_mbd                    true
% 3.20/0.99  --prep_def_merge_tr_red                 false
% 3.20/0.99  --prep_def_merge_tr_cl                  false
% 3.20/0.99  --smt_preprocessing                     true
% 3.20/0.99  --smt_ac_axioms                         fast
% 3.20/0.99  --preprocessed_out                      false
% 3.20/0.99  --preprocessed_stats                    false
% 3.20/0.99  
% 3.20/0.99  ------ Abstraction refinement Options
% 3.20/0.99  
% 3.20/0.99  --abstr_ref                             []
% 3.20/0.99  --abstr_ref_prep                        false
% 3.20/0.99  --abstr_ref_until_sat                   false
% 3.20/0.99  --abstr_ref_sig_restrict                funpre
% 3.20/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.99  --abstr_ref_under                       []
% 3.20/0.99  
% 3.20/0.99  ------ SAT Options
% 3.20/0.99  
% 3.20/0.99  --sat_mode                              false
% 3.20/0.99  --sat_fm_restart_options                ""
% 3.20/0.99  --sat_gr_def                            false
% 3.20/0.99  --sat_epr_types                         true
% 3.20/0.99  --sat_non_cyclic_types                  false
% 3.20/0.99  --sat_finite_models                     false
% 3.20/0.99  --sat_fm_lemmas                         false
% 3.20/0.99  --sat_fm_prep                           false
% 3.20/0.99  --sat_fm_uc_incr                        true
% 3.20/0.99  --sat_out_model                         small
% 3.20/0.99  --sat_out_clauses                       false
% 3.20/0.99  
% 3.20/0.99  ------ QBF Options
% 3.20/0.99  
% 3.20/0.99  --qbf_mode                              false
% 3.20/0.99  --qbf_elim_univ                         false
% 3.20/0.99  --qbf_dom_inst                          none
% 3.20/0.99  --qbf_dom_pre_inst                      false
% 3.20/0.99  --qbf_sk_in                             false
% 3.20/0.99  --qbf_pred_elim                         true
% 3.20/0.99  --qbf_split                             512
% 3.20/0.99  
% 3.20/0.99  ------ BMC1 Options
% 3.20/0.99  
% 3.20/0.99  --bmc1_incremental                      false
% 3.20/0.99  --bmc1_axioms                           reachable_all
% 3.20/0.99  --bmc1_min_bound                        0
% 3.20/0.99  --bmc1_max_bound                        -1
% 3.20/0.99  --bmc1_max_bound_default                -1
% 3.20/0.99  --bmc1_symbol_reachability              true
% 3.20/0.99  --bmc1_property_lemmas                  false
% 3.20/0.99  --bmc1_k_induction                      false
% 3.20/0.99  --bmc1_non_equiv_states                 false
% 3.20/0.99  --bmc1_deadlock                         false
% 3.20/0.99  --bmc1_ucm                              false
% 3.20/0.99  --bmc1_add_unsat_core                   none
% 3.20/0.99  --bmc1_unsat_core_children              false
% 3.20/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.99  --bmc1_out_stat                         full
% 3.20/0.99  --bmc1_ground_init                      false
% 3.20/0.99  --bmc1_pre_inst_next_state              false
% 3.20/0.99  --bmc1_pre_inst_state                   false
% 3.20/0.99  --bmc1_pre_inst_reach_state             false
% 3.20/0.99  --bmc1_out_unsat_core                   false
% 3.20/0.99  --bmc1_aig_witness_out                  false
% 3.20/0.99  --bmc1_verbose                          false
% 3.20/0.99  --bmc1_dump_clauses_tptp                false
% 3.20/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.99  --bmc1_dump_file                        -
% 3.20/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.99  --bmc1_ucm_extend_mode                  1
% 3.20/0.99  --bmc1_ucm_init_mode                    2
% 3.20/0.99  --bmc1_ucm_cone_mode                    none
% 3.20/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.99  --bmc1_ucm_relax_model                  4
% 3.20/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.99  --bmc1_ucm_layered_model                none
% 3.20/0.99  --bmc1_ucm_max_lemma_size               10
% 3.20/0.99  
% 3.20/0.99  ------ AIG Options
% 3.20/0.99  
% 3.20/0.99  --aig_mode                              false
% 3.20/0.99  
% 3.20/0.99  ------ Instantiation Options
% 3.20/0.99  
% 3.20/0.99  --instantiation_flag                    true
% 3.20/0.99  --inst_sos_flag                         false
% 3.20/0.99  --inst_sos_phase                        true
% 3.20/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel_side                     none
% 3.20/0.99  --inst_solver_per_active                1400
% 3.20/0.99  --inst_solver_calls_frac                1.
% 3.20/0.99  --inst_passive_queue_type               priority_queues
% 3.20/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.99  --inst_passive_queues_freq              [25;2]
% 3.20/0.99  --inst_dismatching                      true
% 3.20/0.99  --inst_eager_unprocessed_to_passive     true
% 3.20/0.99  --inst_prop_sim_given                   true
% 3.20/0.99  --inst_prop_sim_new                     false
% 3.20/0.99  --inst_subs_new                         false
% 3.20/0.99  --inst_eq_res_simp                      false
% 3.20/0.99  --inst_subs_given                       false
% 3.20/0.99  --inst_orphan_elimination               true
% 3.20/0.99  --inst_learning_loop_flag               true
% 3.20/0.99  --inst_learning_start                   3000
% 3.20/0.99  --inst_learning_factor                  2
% 3.20/0.99  --inst_start_prop_sim_after_learn       3
% 3.20/0.99  --inst_sel_renew                        solver
% 3.20/0.99  --inst_lit_activity_flag                true
% 3.20/0.99  --inst_restr_to_given                   false
% 3.20/0.99  --inst_activity_threshold               500
% 3.20/0.99  --inst_out_proof                        true
% 3.20/0.99  
% 3.20/0.99  ------ Resolution Options
% 3.20/0.99  
% 3.20/0.99  --resolution_flag                       false
% 3.20/0.99  --res_lit_sel                           adaptive
% 3.20/0.99  --res_lit_sel_side                      none
% 3.20/0.99  --res_ordering                          kbo
% 3.20/0.99  --res_to_prop_solver                    active
% 3.20/0.99  --res_prop_simpl_new                    false
% 3.20/0.99  --res_prop_simpl_given                  true
% 3.20/0.99  --res_passive_queue_type                priority_queues
% 3.20/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.99  --res_passive_queues_freq               [15;5]
% 3.20/0.99  --res_forward_subs                      full
% 3.20/0.99  --res_backward_subs                     full
% 3.20/0.99  --res_forward_subs_resolution           true
% 3.20/0.99  --res_backward_subs_resolution          true
% 3.20/0.99  --res_orphan_elimination                true
% 3.20/0.99  --res_time_limit                        2.
% 3.20/0.99  --res_out_proof                         true
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Options
% 3.20/0.99  
% 3.20/0.99  --superposition_flag                    true
% 3.20/0.99  --sup_passive_queue_type                priority_queues
% 3.20/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.99  --demod_completeness_check              fast
% 3.20/0.99  --demod_use_ground                      true
% 3.20/0.99  --sup_to_prop_solver                    passive
% 3.20/0.99  --sup_prop_simpl_new                    true
% 3.20/0.99  --sup_prop_simpl_given                  true
% 3.20/0.99  --sup_fun_splitting                     false
% 3.20/0.99  --sup_smt_interval                      50000
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Simplification Setup
% 3.20/0.99  
% 3.20/0.99  --sup_indices_passive                   []
% 3.20/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_full_bw                           [BwDemod]
% 3.20/0.99  --sup_immed_triv                        [TrivRules]
% 3.20/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_immed_bw_main                     []
% 3.20/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.99  
% 3.20/0.99  ------ Combination Options
% 3.20/0.99  
% 3.20/0.99  --comb_res_mult                         3
% 3.20/0.99  --comb_sup_mult                         2
% 3.20/0.99  --comb_inst_mult                        10
% 3.20/0.99  
% 3.20/0.99  ------ Debug Options
% 3.20/0.99  
% 3.20/0.99  --dbg_backtrace                         false
% 3.20/0.99  --dbg_dump_prop_clauses                 false
% 3.20/0.99  --dbg_dump_prop_clauses_file            -
% 3.20/0.99  --dbg_out_stat                          false
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  ------ Proving...
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  % SZS status Theorem for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  fof(f8,axiom,(
% 3.20/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f49,plain,(
% 3.20/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.20/1.00    inference(cnf_transformation,[],[f8])).
% 3.20/1.00  
% 3.20/1.00  fof(f3,axiom,(
% 3.20/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f25,plain,(
% 3.20/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.20/1.00    inference(ennf_transformation,[],[f3])).
% 3.20/1.00  
% 3.20/1.00  fof(f31,plain,(
% 3.20/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.20/1.00    introduced(choice_axiom,[])).
% 3.20/1.00  
% 3.20/1.00  fof(f32,plain,(
% 3.20/1.00    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.20/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f31])).
% 3.20/1.00  
% 3.20/1.00  fof(f44,plain,(
% 3.20/1.00    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.20/1.00    inference(cnf_transformation,[],[f32])).
% 3.20/1.00  
% 3.20/1.00  fof(f6,axiom,(
% 3.20/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f47,plain,(
% 3.20/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.20/1.00    inference(cnf_transformation,[],[f6])).
% 3.20/1.00  
% 3.20/1.00  fof(f2,axiom,(
% 3.20/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f23,plain,(
% 3.20/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.20/1.00    inference(rectify,[],[f2])).
% 3.20/1.00  
% 3.20/1.00  fof(f24,plain,(
% 3.20/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.20/1.00    inference(ennf_transformation,[],[f23])).
% 3.20/1.00  
% 3.20/1.00  fof(f29,plain,(
% 3.20/1.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.20/1.00    introduced(choice_axiom,[])).
% 3.20/1.00  
% 3.20/1.00  fof(f30,plain,(
% 3.20/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.20/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f29])).
% 3.20/1.00  
% 3.20/1.00  fof(f43,plain,(
% 3.20/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.20/1.00    inference(cnf_transformation,[],[f30])).
% 3.20/1.00  
% 3.20/1.00  fof(f7,axiom,(
% 3.20/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f48,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.20/1.00    inference(cnf_transformation,[],[f7])).
% 3.20/1.00  
% 3.20/1.00  fof(f79,plain,(
% 3.20/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.20/1.00    inference(definition_unfolding,[],[f43,f48])).
% 3.20/1.00  
% 3.20/1.00  fof(f9,axiom,(
% 3.20/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f33,plain,(
% 3.20/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.20/1.00    inference(nnf_transformation,[],[f9])).
% 3.20/1.00  
% 3.20/1.00  fof(f51,plain,(
% 3.20/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.20/1.00    inference(cnf_transformation,[],[f33])).
% 3.20/1.00  
% 3.20/1.00  fof(f1,axiom,(
% 3.20/1.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f22,plain,(
% 3.20/1.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.20/1.00    inference(rectify,[],[f1])).
% 3.20/1.00  
% 3.20/1.00  fof(f41,plain,(
% 3.20/1.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.20/1.00    inference(cnf_transformation,[],[f22])).
% 3.20/1.00  
% 3.20/1.00  fof(f78,plain,(
% 3.20/1.00    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 3.20/1.00    inference(definition_unfolding,[],[f41,f48])).
% 3.20/1.00  
% 3.20/1.00  fof(f4,axiom,(
% 3.20/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f45,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.20/1.00    inference(cnf_transformation,[],[f4])).
% 3.20/1.00  
% 3.20/1.00  fof(f76,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.20/1.00    inference(definition_unfolding,[],[f45,f48])).
% 3.20/1.00  
% 3.20/1.00  fof(f5,axiom,(
% 3.20/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f26,plain,(
% 3.20/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.20/1.00    inference(ennf_transformation,[],[f5])).
% 3.20/1.00  
% 3.20/1.00  fof(f46,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.20/1.00    inference(cnf_transformation,[],[f26])).
% 3.20/1.00  
% 3.20/1.00  fof(f81,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.20/1.00    inference(definition_unfolding,[],[f46,f48])).
% 3.20/1.00  
% 3.20/1.00  fof(f20,conjecture,(
% 3.20/1.00    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f21,negated_conjecture,(
% 3.20/1.00    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.20/1.00    inference(negated_conjecture,[],[f20])).
% 3.20/1.00  
% 3.20/1.00  fof(f28,plain,(
% 3.20/1.00    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.20/1.00    inference(ennf_transformation,[],[f21])).
% 3.20/1.00  
% 3.20/1.00  fof(f39,plain,(
% 3.20/1.00    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK3 != sK5 & sK3 != sK4 & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)))),
% 3.20/1.00    introduced(choice_axiom,[])).
% 3.20/1.00  
% 3.20/1.00  fof(f40,plain,(
% 3.20/1.00    sK3 != sK5 & sK3 != sK4 & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5))),
% 3.20/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f39])).
% 3.20/1.00  
% 3.20/1.00  fof(f69,plain,(
% 3.20/1.00    r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5))),
% 3.20/1.00    inference(cnf_transformation,[],[f40])).
% 3.20/1.00  
% 3.20/1.00  fof(f13,axiom,(
% 3.20/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f62,plain,(
% 3.20/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.20/1.00    inference(cnf_transformation,[],[f13])).
% 3.20/1.00  
% 3.20/1.00  fof(f74,plain,(
% 3.20/1.00    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.20/1.00    inference(definition_unfolding,[],[f62,f73])).
% 3.20/1.00  
% 3.20/1.00  fof(f14,axiom,(
% 3.20/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f63,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.20/1.00    inference(cnf_transformation,[],[f14])).
% 3.20/1.00  
% 3.20/1.00  fof(f15,axiom,(
% 3.20/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f64,plain,(
% 3.20/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.20/1.00    inference(cnf_transformation,[],[f15])).
% 3.20/1.00  
% 3.20/1.00  fof(f16,axiom,(
% 3.20/1.00    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f65,plain,(
% 3.20/1.00    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.20/1.00    inference(cnf_transformation,[],[f16])).
% 3.20/1.00  
% 3.20/1.00  fof(f72,plain,(
% 3.20/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.20/1.00    inference(definition_unfolding,[],[f64,f65])).
% 3.20/1.00  
% 3.20/1.00  fof(f73,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.20/1.00    inference(definition_unfolding,[],[f63,f72])).
% 3.20/1.00  
% 3.20/1.00  fof(f91,plain,(
% 3.20/1.00    r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5))),
% 3.20/1.00    inference(definition_unfolding,[],[f69,f74,f73])).
% 3.20/1.00  
% 3.20/1.00  fof(f12,axiom,(
% 3.20/1.00    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f61,plain,(
% 3.20/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.20/1.00    inference(cnf_transformation,[],[f12])).
% 3.20/1.00  
% 3.20/1.00  fof(f10,axiom,(
% 3.20/1.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f52,plain,(
% 3.20/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.20/1.00    inference(cnf_transformation,[],[f10])).
% 3.20/1.00  
% 3.20/1.00  fof(f77,plain,(
% 3.20/1.00    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.20/1.00    inference(definition_unfolding,[],[f61,f52,f65,f74])).
% 3.20/1.00  
% 3.20/1.00  fof(f11,axiom,(
% 3.20/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.20/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/1.00  
% 3.20/1.00  fof(f27,plain,(
% 3.20/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.20/1.00    inference(ennf_transformation,[],[f11])).
% 3.20/1.00  
% 3.20/1.00  fof(f34,plain,(
% 3.20/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.20/1.00    inference(nnf_transformation,[],[f27])).
% 3.20/1.00  
% 3.20/1.00  fof(f35,plain,(
% 3.20/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.20/1.00    inference(flattening,[],[f34])).
% 3.20/1.00  
% 3.20/1.00  fof(f36,plain,(
% 3.20/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.20/1.00    inference(rectify,[],[f35])).
% 3.20/1.00  
% 3.20/1.00  fof(f37,plain,(
% 3.20/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 3.20/1.00    introduced(choice_axiom,[])).
% 3.20/1.00  
% 3.20/1.00  fof(f38,plain,(
% 3.20/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.20/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 3.20/1.00  
% 3.20/1.00  fof(f53,plain,(
% 3.20/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.20/1.00    inference(cnf_transformation,[],[f38])).
% 3.20/1.00  
% 3.20/1.00  fof(f89,plain,(
% 3.20/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.20/1.00    inference(definition_unfolding,[],[f53,f72])).
% 3.20/1.00  
% 3.20/1.00  fof(f98,plain,(
% 3.20/1.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 3.20/1.00    inference(equality_resolution,[],[f89])).
% 3.20/1.00  
% 3.20/1.00  fof(f56,plain,(
% 3.20/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.20/1.00    inference(cnf_transformation,[],[f38])).
% 3.20/1.00  
% 3.20/1.00  fof(f86,plain,(
% 3.20/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.20/1.00    inference(definition_unfolding,[],[f56,f72])).
% 3.20/1.00  
% 3.20/1.00  fof(f92,plain,(
% 3.20/1.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 3.20/1.00    inference(equality_resolution,[],[f86])).
% 3.20/1.00  
% 3.20/1.00  fof(f93,plain,(
% 3.20/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 3.20/1.00    inference(equality_resolution,[],[f92])).
% 3.20/1.00  
% 3.20/1.00  fof(f54,plain,(
% 3.20/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.20/1.00    inference(cnf_transformation,[],[f38])).
% 3.20/1.00  
% 3.20/1.00  fof(f88,plain,(
% 3.20/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.20/1.00    inference(definition_unfolding,[],[f54,f72])).
% 3.20/1.00  
% 3.20/1.00  fof(f96,plain,(
% 3.20/1.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 3.20/1.00    inference(equality_resolution,[],[f88])).
% 3.20/1.00  
% 3.20/1.00  fof(f97,plain,(
% 3.20/1.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 3.20/1.00    inference(equality_resolution,[],[f96])).
% 3.20/1.00  
% 3.20/1.00  fof(f71,plain,(
% 3.20/1.00    sK3 != sK5),
% 3.20/1.00    inference(cnf_transformation,[],[f40])).
% 3.20/1.00  
% 3.20/1.00  fof(f70,plain,(
% 3.20/1.00    sK3 != sK4),
% 3.20/1.00    inference(cnf_transformation,[],[f40])).
% 3.20/1.00  
% 3.20/1.00  cnf(c_8,plain,
% 3.20/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.20/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_5,plain,
% 3.20/1.00      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.20/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1664,plain,
% 3.20/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_7,plain,
% 3.20/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.20/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_3,plain,
% 3.20/1.00      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 3.20/1.00      | ~ r1_xboole_0(X1,X2) ),
% 3.20/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1666,plain,
% 3.20/1.00      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 3.20/1.00      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_3438,plain,
% 3.20/1.00      ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top
% 3.20/1.00      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_7,c_1666]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_9,plain,
% 3.20/1.00      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.20/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1663,plain,
% 3.20/1.00      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_2856,plain,
% 3.20/1.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_7,c_1663]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_3922,plain,
% 3.20/1.00      ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
% 3.20/1.00      inference(forward_subsumption_resolution,
% 3.20/1.00                [status(thm)],
% 3.20/1.00                [c_3438,c_2856]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_3926,plain,
% 3.20/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_1664,c_3922]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_2,plain,
% 3.20/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.20/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_0,plain,
% 3.20/1.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.20/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1993,plain,
% 3.20/1.00      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_6,plain,
% 3.20/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.20/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_22,negated_conjecture,
% 3.20/1.00      ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
% 3.20/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_225,plain,
% 3.20/1.00      ( k3_enumset1(sK4,sK4,sK4,sK4,sK5) != X0
% 3.20/1.00      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != X1
% 3.20/1.00      | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = X1 ),
% 3.20/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_226,plain,
% 3.20/1.00      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 3.20/1.00      inference(unflattening,[status(thm)],[c_225]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1994,plain,
% 3.20/1.00      ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_226,c_0]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_2009,plain,
% 3.20/1.00      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 3.20/1.00      inference(demodulation,[status(thm)],[c_1993,c_1994]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1,plain,
% 3.20/1.00      ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3))) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 3.20/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_2427,plain,
% 3.20/1.00      ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK5),k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK4,sK4,sK4,sK5,sK3) ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_2009,c_1]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_4084,plain,
% 3.20/1.00      ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK5),k1_xboole_0) = k3_enumset1(sK4,sK4,sK4,sK5,sK3) ),
% 3.20/1.00      inference(demodulation,[status(thm)],[c_3926,c_2427]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_4293,plain,
% 3.20/1.00      ( k3_enumset1(sK4,sK4,sK4,sK5,sK3) = k3_enumset1(sK4,sK4,sK4,sK4,sK5) ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_8,c_4084]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_4755,plain,
% 3.20/1.00      ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK5,sK3),k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(sK4,sK4,sK4,sK5,sK3))) = k3_enumset1(sK4,sK4,sK4,sK5,X0) ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_4293,c_1]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_4770,plain,
% 3.20/1.00      ( k3_enumset1(sK4,sK4,sK5,sK3,X0) = k3_enumset1(sK4,sK4,sK4,sK5,X0) ),
% 3.20/1.00      inference(demodulation,[status(thm)],[c_4755,c_1]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_4772,plain,
% 3.20/1.00      ( k3_enumset1(sK4,sK4,sK5,sK3,sK3) = k3_enumset1(sK4,sK4,sK4,sK4,sK5) ),
% 3.20/1.00      inference(demodulation,[status(thm)],[c_4770,c_4293]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_6712,plain,
% 3.20/1.00      ( k5_xboole_0(k3_enumset1(sK4,sK4,sK5,sK3,X0),k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(sK4,sK4,sK5,sK3,X0))) = k3_enumset1(sK4,sK4,sK5,X0,X1) ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_4770,c_1]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_6776,plain,
% 3.20/1.00      ( k3_enumset1(sK4,sK5,sK3,X0,X1) = k3_enumset1(sK4,sK4,sK5,X0,X1) ),
% 3.20/1.00      inference(demodulation,[status(thm)],[c_6712,c_1]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_9121,plain,
% 3.20/1.00      ( k3_enumset1(sK4,sK5,sK3,sK3,sK3) = k3_enumset1(sK4,sK4,sK4,sK4,sK5) ),
% 3.20/1.00      inference(demodulation,[status(thm)],[c_4772,c_6776]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_18,plain,
% 3.20/1.00      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
% 3.20/1.00      | X0 = X1
% 3.20/1.00      | X0 = X2
% 3.20/1.00      | X0 = X3 ),
% 3.20/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1654,plain,
% 3.20/1.00      ( X0 = X1
% 3.20/1.00      | X0 = X2
% 3.20/1.00      | X0 = X3
% 3.20/1.00      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3)) != iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_9144,plain,
% 3.20/1.00      ( sK4 = X0
% 3.20/1.00      | sK5 = X0
% 3.20/1.00      | r2_hidden(X0,k3_enumset1(sK4,sK5,sK3,sK3,sK3)) != iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_9121,c_1654]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_9239,plain,
% 3.20/1.00      ( sK4 = sK3
% 3.20/1.00      | sK5 = sK3
% 3.20/1.00      | r2_hidden(sK3,k3_enumset1(sK4,sK5,sK3,sK3,sK3)) != iProver_top ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_9144]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_15,plain,
% 3.20/1.00      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
% 3.20/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1657,plain,
% 3.20/1.00      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) = iProver_top ),
% 3.20/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_6722,plain,
% 3.20/1.00      ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK5,sK3,X0)) = iProver_top ),
% 3.20/1.00      inference(superposition,[status(thm)],[c_4770,c_1657]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_6836,plain,
% 3.20/1.00      ( r2_hidden(X0,k3_enumset1(sK4,sK5,sK3,sK3,X0)) = iProver_top ),
% 3.20/1.00      inference(demodulation,[status(thm)],[c_6722,c_6776]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_6953,plain,
% 3.20/1.00      ( r2_hidden(sK3,k3_enumset1(sK4,sK5,sK3,sK3,sK3)) = iProver_top ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_6836]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1327,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1792,plain,
% 3.20/1.00      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_1327]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1793,plain,
% 3.20/1.00      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_1792]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1790,plain,
% 3.20/1.00      ( sK5 != X0 | sK3 != X0 | sK3 = sK5 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_1327]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_1791,plain,
% 3.20/1.00      ( sK5 != sK3 | sK3 = sK5 | sK3 != sK3 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_1790]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_17,plain,
% 3.20/1.00      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
% 3.20/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_29,plain,
% 3.20/1.00      ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_26,plain,
% 3.20/1.00      ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | sK3 = sK3 ),
% 3.20/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_20,negated_conjecture,
% 3.20/1.00      ( sK3 != sK5 ),
% 3.20/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(c_21,negated_conjecture,
% 3.20/1.00      ( sK3 != sK4 ),
% 3.20/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.20/1.00  
% 3.20/1.00  cnf(contradiction,plain,
% 3.20/1.00      ( $false ),
% 3.20/1.00      inference(minisat,
% 3.20/1.00                [status(thm)],
% 3.20/1.00                [c_9239,c_6953,c_1793,c_1791,c_29,c_26,c_20,c_21]) ).
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.20/1.00  
% 3.20/1.00  ------                               Statistics
% 3.20/1.00  
% 3.20/1.00  ------ General
% 3.20/1.00  
% 3.20/1.00  abstr_ref_over_cycles:                  0
% 3.20/1.00  abstr_ref_under_cycles:                 0
% 3.20/1.00  gc_basic_clause_elim:                   0
% 3.20/1.00  forced_gc_time:                         0
% 3.20/1.00  parsing_time:                           0.01
% 3.20/1.00  unif_index_cands_time:                  0.
% 3.20/1.00  unif_index_add_time:                    0.
% 3.20/1.00  orderings_time:                         0.
% 3.20/1.00  out_proof_time:                         0.007
% 3.20/1.00  total_time:                             0.31
% 3.20/1.00  num_of_symbols:                         45
% 3.20/1.00  num_of_terms:                           9425
% 3.20/1.00  
% 3.20/1.00  ------ Preprocessing
% 3.20/1.00  
% 3.20/1.00  num_of_splits:                          0
% 3.20/1.00  num_of_split_atoms:                     0
% 3.20/1.00  num_of_reused_defs:                     0
% 3.20/1.00  num_eq_ax_congr_red:                    51
% 3.20/1.00  num_of_sem_filtered_clauses:            1
% 3.20/1.00  num_of_subtypes:                        0
% 3.20/1.00  monotx_restored_types:                  0
% 3.20/1.00  sat_num_of_epr_types:                   0
% 3.20/1.00  sat_num_of_non_cyclic_types:            0
% 3.20/1.00  sat_guarded_non_collapsed_types:        0
% 3.20/1.00  num_pure_diseq_elim:                    0
% 3.20/1.00  simp_replaced_by:                       0
% 3.20/1.00  res_preprocessed:                       102
% 3.20/1.00  prep_upred:                             0
% 3.20/1.00  prep_unflattend:                        72
% 3.20/1.00  smt_new_axioms:                         0
% 3.20/1.00  pred_elim_cands:                        2
% 3.20/1.00  pred_elim:                              1
% 3.20/1.00  pred_elim_cl:                           1
% 3.20/1.00  pred_elim_cycles:                       5
% 3.20/1.00  merged_defs:                            8
% 3.20/1.00  merged_defs_ncl:                        0
% 3.20/1.00  bin_hyper_res:                          8
% 3.20/1.00  prep_cycles:                            4
% 3.20/1.00  pred_elim_time:                         0.014
% 3.20/1.00  splitting_time:                         0.
% 3.20/1.00  sem_filter_time:                        0.
% 3.20/1.00  monotx_time:                            0.
% 3.20/1.00  subtype_inf_time:                       0.
% 3.20/1.00  
% 3.20/1.00  ------ Problem properties
% 3.20/1.00  
% 3.20/1.00  clauses:                                22
% 3.20/1.00  conjectures:                            2
% 3.20/1.00  epr:                                    2
% 3.20/1.00  horn:                                   18
% 3.20/1.00  ground:                                 3
% 3.20/1.00  unary:                                  12
% 3.20/1.00  binary:                                 5
% 3.20/1.00  lits:                                   40
% 3.20/1.00  lits_eq:                                25
% 3.20/1.00  fd_pure:                                0
% 3.20/1.00  fd_pseudo:                              0
% 3.20/1.00  fd_cond:                                1
% 3.20/1.00  fd_pseudo_cond:                         4
% 3.20/1.00  ac_symbols:                             0
% 3.20/1.00  
% 3.20/1.00  ------ Propositional Solver
% 3.20/1.00  
% 3.20/1.00  prop_solver_calls:                      27
% 3.20/1.00  prop_fast_solver_calls:                 760
% 3.20/1.00  smt_solver_calls:                       0
% 3.20/1.00  smt_fast_solver_calls:                  0
% 3.20/1.00  prop_num_of_clauses:                    2198
% 3.20/1.00  prop_preprocess_simplified:             6892
% 3.20/1.00  prop_fo_subsumed:                       7
% 3.20/1.00  prop_solver_time:                       0.
% 3.20/1.00  smt_solver_time:                        0.
% 3.20/1.00  smt_fast_solver_time:                   0.
% 3.20/1.00  prop_fast_solver_time:                  0.
% 3.20/1.00  prop_unsat_core_time:                   0.
% 3.20/1.00  
% 3.20/1.00  ------ QBF
% 3.20/1.00  
% 3.20/1.00  qbf_q_res:                              0
% 3.20/1.00  qbf_num_tautologies:                    0
% 3.20/1.00  qbf_prep_cycles:                        0
% 3.20/1.00  
% 3.20/1.00  ------ BMC1
% 3.20/1.00  
% 3.20/1.00  bmc1_current_bound:                     -1
% 3.20/1.00  bmc1_last_solved_bound:                 -1
% 3.20/1.00  bmc1_unsat_core_size:                   -1
% 3.20/1.00  bmc1_unsat_core_parents_size:           -1
% 3.20/1.00  bmc1_merge_next_fun:                    0
% 3.20/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.20/1.00  
% 3.20/1.00  ------ Instantiation
% 3.20/1.00  
% 3.20/1.00  inst_num_of_clauses:                    809
% 3.20/1.00  inst_num_in_passive:                    245
% 3.20/1.00  inst_num_in_active:                     280
% 3.20/1.00  inst_num_in_unprocessed:                284
% 3.20/1.00  inst_num_of_loops:                      300
% 3.20/1.00  inst_num_of_learning_restarts:          0
% 3.20/1.00  inst_num_moves_active_passive:          19
% 3.20/1.00  inst_lit_activity:                      0
% 3.20/1.00  inst_lit_activity_moves:                0
% 3.20/1.00  inst_num_tautologies:                   0
% 3.20/1.00  inst_num_prop_implied:                  0
% 3.20/1.00  inst_num_existing_simplified:           0
% 3.20/1.00  inst_num_eq_res_simplified:             0
% 3.20/1.00  inst_num_child_elim:                    0
% 3.20/1.00  inst_num_of_dismatching_blockings:      756
% 3.20/1.00  inst_num_of_non_proper_insts:           722
% 3.20/1.00  inst_num_of_duplicates:                 0
% 3.20/1.00  inst_inst_num_from_inst_to_res:         0
% 3.20/1.00  inst_dismatching_checking_time:         0.
% 3.20/1.00  
% 3.20/1.00  ------ Resolution
% 3.20/1.00  
% 3.20/1.00  res_num_of_clauses:                     0
% 3.20/1.00  res_num_in_passive:                     0
% 3.20/1.00  res_num_in_active:                      0
% 3.20/1.00  res_num_of_loops:                       106
% 3.20/1.00  res_forward_subset_subsumed:            112
% 3.20/1.00  res_backward_subset_subsumed:           0
% 3.20/1.00  res_forward_subsumed:                   0
% 3.20/1.00  res_backward_subsumed:                  0
% 3.20/1.00  res_forward_subsumption_resolution:     0
% 3.20/1.00  res_backward_subsumption_resolution:    0
% 3.20/1.00  res_clause_to_clause_subsumption:       10491
% 3.20/1.00  res_orphan_elimination:                 0
% 3.20/1.00  res_tautology_del:                      70
% 3.20/1.00  res_num_eq_res_simplified:              0
% 3.20/1.00  res_num_sel_changes:                    0
% 3.20/1.00  res_moves_from_active_to_pass:          0
% 3.20/1.00  
% 3.20/1.00  ------ Superposition
% 3.20/1.00  
% 3.20/1.00  sup_time_total:                         0.
% 3.20/1.00  sup_time_generating:                    0.
% 3.20/1.00  sup_time_sim_full:                      0.
% 3.20/1.00  sup_time_sim_immed:                     0.
% 3.20/1.00  
% 3.20/1.00  sup_num_of_clauses:                     192
% 3.20/1.00  sup_num_in_active:                      39
% 3.20/1.00  sup_num_in_passive:                     153
% 3.20/1.00  sup_num_of_loops:                       59
% 3.20/1.00  sup_fw_superposition:                   137
% 3.20/1.00  sup_bw_superposition:                   207
% 3.20/1.00  sup_immediate_simplified:               157
% 3.20/1.00  sup_given_eliminated:                   5
% 3.20/1.00  comparisons_done:                       0
% 3.20/1.00  comparisons_avoided:                    42
% 3.20/1.00  
% 3.20/1.00  ------ Simplifications
% 3.20/1.00  
% 3.20/1.00  
% 3.20/1.00  sim_fw_subset_subsumed:                 17
% 3.20/1.00  sim_bw_subset_subsumed:                 4
% 3.20/1.00  sim_fw_subsumed:                        64
% 3.20/1.00  sim_bw_subsumed:                        1
% 3.20/1.00  sim_fw_subsumption_res:                 5
% 3.20/1.00  sim_bw_subsumption_res:                 0
% 3.20/1.00  sim_tautology_del:                      2
% 3.20/1.00  sim_eq_tautology_del:                   3
% 3.20/1.00  sim_eq_res_simp:                        0
% 3.20/1.00  sim_fw_demodulated:                     70
% 3.20/1.00  sim_bw_demodulated:                     28
% 3.20/1.00  sim_light_normalised:                   40
% 3.20/1.00  sim_joinable_taut:                      0
% 3.20/1.00  sim_joinable_simp:                      0
% 3.20/1.00  sim_ac_normalised:                      0
% 3.20/1.00  sim_smt_subsumption:                    0
% 3.20/1.00  
%------------------------------------------------------------------------------
